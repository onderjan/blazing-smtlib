module

public import BSmtLib.Parser.Category.Term
public import BSmtLib.Traits.CommandHandler

public section

/-!
# Functions

The parsers of the parts of function definitions: a signature, a function declaration, and the
recursive bodies of `define-funs-rec`.
-/

namespace BSmtLib.Parser.Command.Internal.Function

open BSmtLib.Plain (SymbolView)
open BSmtLib.Nodes BSmtLib.Traits BSmtLib.Parser.Category.Combinator BSmtLib.Parser.Category.Sort
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Parser.Category.Sort.Internal
open BSmtLib.Parser.Category.SortedVar BSmtLib.Parser.Category.Term BSmtLib.Parser.Category.Token
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Category.Token.Internal
open BSmtLib.Token (Version)
open BSmtLib.Parser.Internal (PM call syntaxError)

/-- The state of the parser of a function signature `⟨symbol⟩ (⟨sorted_var⟩∗) ⟨sort⟩`. -/
inductive SignatureState (HandledSort : Type) where
  | start
  | parameters (symbol : SymbolView)
      (state : ListState (SortedVarState HandledSort) (SymbolView × HandledSort))
  | result (symbol : SymbolView) (parameters : Array (SymbolView × HandledSort))
      (state : SortState HandledSort)

/-- The state of the parser of a function declaration `(` signature `)`. -/
inductive FunctionDecState (HandledSort : Type) where
  | start
  | signature (state : SignatureState HandledSort)
  | close (signature : Signature HandledSort)

section

variable {H : Type} {m : Type → Type} [Monad m] [Handler H m]

/-- A step of the signature parser; the sorts are handled at their last tokens. -/
def signatureStep (version : Version) (self : SignatureState (Handler.«Sort» H))
    (token : Internal.Input) :
    PM H (Internal.Step (SignatureState (Handler.«Sort» H)) (Signature (Handler.«Sort» H))) := do
  match self with
  | .start => return .more (.parameters (← expectSymbol token) (ListState.paren .start))
  | .parameters symbol state =>
    match ← state.step .start (sortedVarStep version) none token with
    | .more state => return .more (.parameters symbol state)
    | .done parameters => return .more (.result symbol parameters .init)
  | .result symbol parameters state =>
    match ← sortStep version state token with
    | .more state => return .more (.result symbol parameters state)
    | .done result => return .done ⟨symbol, parameters, result⟩

/-- A step of the parser of a function declaration. -/
def functionDecStep (version : Version) (self : FunctionDecState (Handler.«Sort» H))
    (token : Internal.Input) :
    PM H (Internal.Step (FunctionDecState (Handler.«Sort» H)) (Signature (Handler.«Sort» H))) := do
  match self with
  | .start =>
    expectOpen token
    return .more (.signature .start)
  | .signature state =>
    match ← signatureStep version state token with
    | .more state => return .more (.signature state)
    | .done signature => return .more (.close signature)
  | .close signature =>
    expectClose token
    return .done signature

end

section

variable {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]

/--
A step of the parser of a recursive body: the body between `start_recursive_body` and
`end_recursive_body`, which comes at the body's last token, as a body has no `)` of its own.
-/
def bodyStep (version : Version) (self : TermStateOf H) (token : Internal.Input) :
    PM H (Internal.Step (TermStateOf H) Unit) := do
  match ← termStep version self token with
  | .more term => return .more term
  | .done body =>
    call (CommandHandler.endRecursiveBody body)
    return .done ()

/--
A step of the list of recursive bodies, as many as the functions. A body's start is not made
here but when its first token arrives (`bodiesArrive`).
-/
def bodiesStep (count : Nat) (version : Version) (self : ListState (TermStateOf H) Unit)
    (token : Internal.Input) : PM H (Internal.Step (ListState (TermStateOf H) Unit) (Array Unit)) :=
  self.step .init (bodyStep version) (some count) token

/--
The calls due when a token arrives at the list of recursive bodies: between bodies, a token that
can begin a body, any but `)`, while a body is still due, starts it, with the signature of its
function, before the list takes the token.
-/
def bodiesArrive (signatures : Array (Signature (Handler.«Sort» H)))
    (self : ListState (TermStateOf H) Unit) (token : Internal.Input) : PM H Unit :=
  if self.opened && self.outside then
    match token, signatures[self.items.size]? with
    | .parenClose, _ => pure ()
    | _, some signature => call (CommandHandler.startRecursiveBody signature)
    | _, none => pure ()
  else pure ()

end

end BSmtLib.Parser.Command.Internal.Function
