module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Single
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Whitespace
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Quoted
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Symbol
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Comment
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Hash
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.String
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Keyword
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal.Digits
import all BSmtLib.Lexer.Helpers

@[expose] public section

/-!
# The Rust port's normal state against the naive lexer

`lexNormalFrom_wp`: the loop of the Rust port's normal state, with its fast paths and its slow
path, keeps the correspondence with the naive lexer's pure run.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal

open BSmtLib.Lexer.Internal.WRustPort (Frame)
open BSmtLib.Lexer.Internal.WRustPort.Slice (get?)
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Delimiters

section

variable {floor : Option Nat} {low : Nat}

variable {C : BSmtLibSpec.Lexer.Consumer} {hd : Bool} {iv : Token.Version}

theorem normalSpec_lt (v : Token.Version) (input : ByteSlice) (offset base : Nat)
    (hframe : Frame floor low offset) :
    ∀ (n index : Nat), input.size - index < n →
      Basic.NormalSpec C v hd iv input offset base hframe index := by
  intro n
  induction n with
  | zero => intro index h; omega
  | succ n ih =>
  intro index hn
  match hget : get? input index with
  | none => exact Single.normalSpec_end v input offset base hframe index hget
  | some c =>
  by_cases h41 : c = 41
  · exact Single.normalSpec_parenClose v input offset base hframe n index ih hn hget h41
  by_cases h40 : c = 40
  · exact Single.normalSpec_parenOpen v input offset base hframe n index ih hn hget h40
  rcases fastFlags_cases c with hfoff | ⟨hf, hwsr⟩ | ⟨hf, hpipe⟩ | ⟨hf, hsym, hdig⟩
  · cases hst : Lexer.Helpers.startOf c
    case lineFeed =>
      exact Single.normalSpec_lineFeed v input offset base hframe n index ih hn hget h40 h41 hfoff
          hst
    case comment =>
      exact Comment.normalSpec_comment v input offset base hframe n index ih hn hget h40 h41 hfoff
          hst
    case hash =>
      exact Hash.normalSpec_hash v input offset base hframe n index ih hn hget h40 h41 hfoff hst
    case quote =>
      exact String.normalSpec_string v input offset base hframe n index ih hn hget h40 h41 hfoff hst
    case colon =>
      exact Keyword.normalSpec_keyword v input offset base hframe n index ih hn hget h40 h41 hfoff
          hst
    case digit =>
      exact Digits.normalSpec_digits v input offset base hframe n index ih hn hget h40 h41 hfoff hst
    all_goals
      exact Single.normalSpec_other v input offset base hframe index hget h40 h41 hfoff
        (by rw [hst]; rfl)
  · exact Whitespace.normalSpec_whitespace v input offset base hframe n index ih hn hget h40 h41 hf
      hwsr
  · exact Quoted.normalSpec_quoted v input offset base hframe n index ih hn hget h40 h41 hf hpipe
  · exact Symbol.normalSpec_symbol v input offset base hframe n index ih hn hget h40 h41 hf hsym
      hdig

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Normal
