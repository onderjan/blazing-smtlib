//! A command handler that folds every callback it receives into one hash,
//! so that two parser revisions can be compared on the whole corpus by
//! comparing one number per file.
//!
//! The hash covers the sequence of callbacks, their order, and the content of
//! their arguments: symbol, numeral, keyword, and string bytes, the structure
//! of sorts, terms, patterns, and attribute values, and the handled values
//! that the parser passes back (which are the running hash at the moment the
//! value was produced, so nesting is covered too). It deliberately covers
//! nothing about the Rust types involved, so an API change that keeps the
//! callbacks and their content the same keeps the hashes the same.
//!
//! The hash is FNV-1a over a byte encoding: every callback writes a tag byte,
//! every byte string is length-prefixed, every collection is count-prefixed,
//! and every handled value is written as eight bytes.

use smt_parser_rs::{
    CommandHandler, NonstandardCommandError, SmtAttributeValue, SmtDatatypeConstructor,
    SmtFunctionSignature, SmtHandler, SmtIdent, SmtIndex, SmtKeyword, SmtNumeral, SmtPattern,
    SmtQuantifierKind, SmtSExpr, SmtSimplePattern, SmtSort, SmtSpecialConstant,
    SmtStringContent, SmtSymbol, SmtSymbolView, SmtTerm, read::parser::NoCommandParser,
};

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

/// Handler folding every callback into a running FNV-1a hash.
pub struct TraceHash {
    state: u64,
}

impl Default for TraceHash {
    fn default() -> Self {
        Self::new()
    }
}

// callback tags; the numbers only need to be distinct and stable
mod tag {
    pub const SORT: u8 = 1;
    pub const TERM: u8 = 2;
    pub const S_EXPR: u8 = 3;
    pub const ATTRIBUTE: u8 = 4;
    pub const ANNOTATE_TERM: u8 = 5;
    pub const START_LET: u8 = 6;
    pub const END_LET: u8 = 7;
    pub const START_QUANTIFIER: u8 = 8;
    pub const END_QUANTIFIER: u8 = 9;
    pub const START_LAMBDA: u8 = 10;
    pub const END_LAMBDA: u8 = 11;
    pub const START_MATCH: u8 = 12;
    pub const START_MATCH_CASE: u8 = 13;
    pub const END_MATCH_CASE: u8 = 14;
    pub const END_MATCH: u8 = 15;
    pub const ECHO: u8 = 32;
    pub const GET_OPTION: u8 = 33;
    pub const SET_OPTION: u8 = 34;
    pub const GET_INFO: u8 = 35;
    pub const SET_INFO: u8 = 36;
    pub const SET_LOGIC: u8 = 37;
    pub const GET_VALUE: u8 = 38;
    pub const GET_ASSERTIONS: u8 = 39;
    pub const GET_ASSIGNMENT: u8 = 40;
    pub const GET_MODEL: u8 = 41;
    pub const GET_PROOF: u8 = 42;
    pub const GET_UNSAT_ASSUMPTIONS: u8 = 43;
    pub const GET_UNSAT_CORE: u8 = 44;
    pub const DECLARE_SORT: u8 = 45;
    pub const DECLARE_SORT_PARAMETER: u8 = 46;
    pub const DECLARE_FUN: u8 = 47;
    pub const ASSERT: u8 = 48;
    pub const CHECK_SAT: u8 = 49;
    pub const RESET: u8 = 50;
    pub const RESET_ASSERTIONS: u8 = 51;
    pub const EXIT: u8 = 52;
    pub const PUSH: u8 = 53;
    pub const POP: u8 = 54;
    pub const START_DEFINE_SORT: u8 = 55;
    pub const END_DEFINE_SORT: u8 = 56;
    pub const START_DEFINE_FUN: u8 = 57;
    pub const END_DEFINE_FUN: u8 = 58;
    pub const START_DEFINE_FUNS_REC: u8 = 59;
    pub const START_RECURSIVE_BODY: u8 = 60;
    pub const END_RECURSIVE_BODY: u8 = 61;
    pub const END_DEFINE_FUNS_REC: u8 = 62;
    pub const START_DECLARE_DATATYPES: u8 = 63;
    pub const START_DATATYPE_DECLARATION: u8 = 64;
    pub const END_DATATYPE_DECLARATION: u8 = 65;
    pub const END_DECLARE_DATATYPES: u8 = 66;
}

impl TraceHash {
    pub fn new() -> Self {
        Self { state: FNV_OFFSET }
    }

    /// The hash of everything handled so far.
    pub fn digest(&self) -> u64 {
        self.state
    }

    /// Folds arbitrary bytes into the hash, for digests of trace files.
    pub fn fold(&mut self, bytes: &[u8]) {
        self.bytes(bytes);
    }

    fn byte(&mut self, byte: u8) {
        self.state ^= u64::from(byte);
        self.state = self.state.wrapping_mul(FNV_PRIME);
    }

    fn u64(&mut self, value: u64) {
        for byte in value.to_le_bytes() {
            self.byte(byte);
        }
    }

    fn count(&mut self, count: usize) {
        self.u64(count as u64);
    }

    fn bytes(&mut self, bytes: &[u8]) {
        self.count(bytes.len());
        for &byte in bytes {
            self.byte(byte);
        }
    }

    fn values(&mut self, values: &[u64]) {
        self.count(values.len());
        for &value in values {
            self.u64(value);
        }
    }

    fn symbol(&mut self, symbol: &SmtSymbol) {
        self.bytes(symbol.as_slice());
    }

    fn numeral(&mut self, numeral: &SmtNumeral) {
        self.bytes(numeral.as_slice());
    }

    fn keyword(&mut self, keyword: &SmtKeyword) {
        self.bytes(keyword.as_slice());
    }

    fn symbols(&mut self, symbols: &[SmtSymbol]) {
        self.count(symbols.len());
        for symbol in symbols {
            self.symbol(symbol);
        }
    }

    fn special_constant(&mut self, constant: &SmtSpecialConstant) {
        match constant {
            SmtSpecialConstant::Numeral(value) => {
                self.byte(1);
                self.bytes(value.as_slice());
            }
            SmtSpecialConstant::Decimal(value) => {
                self.byte(2);
                self.bytes(value.as_slice());
            }
            SmtSpecialConstant::Hexadecimal(value) => {
                self.byte(3);
                self.bytes(value.as_slice());
            }
            SmtSpecialConstant::Binary(value) => {
                self.byte(4);
                self.bytes(value.as_slice());
            }
            SmtSpecialConstant::String(value) => {
                self.byte(5);
                self.bytes(value.as_slice());
            }
        }
    }

    fn ident(&mut self, ident: &SmtIdent) {
        self.symbol(&ident.name);
        self.count(ident.indices.len());
        for index in &ident.indices {
            match index {
                SmtIndex::Numeral(value) => {
                    self.byte(1);
                    self.numeral(value);
                }
                SmtIndex::Symbol(value) => {
                    self.byte(2);
                    self.symbol(value);
                }
            }
        }
    }

    fn optional_value(&mut self, value: Option<u64>) {
        match value {
            None => self.byte(0),
            Some(value) => {
                self.byte(1);
                self.u64(value);
            }
        }
    }

    fn sorted_vars(&mut self, vars: &[(SmtSymbol, u64)]) {
        self.count(vars.len());
        for (name, sort) in vars {
            self.symbol(name);
            self.u64(*sort);
        }
    }

    fn signature(&mut self, signature: &SmtFunctionSignature<Self>) {
        self.symbol(&signature.name);
        self.sorted_vars(&signature.params);
        self.u64(signature.result_sort);
    }

    fn simple_pattern(&mut self, pattern: &SmtSimplePattern) {
        match pattern {
            SmtSimplePattern::Symbol(symbol) => {
                self.byte(1);
                self.symbol(symbol);
            }
            SmtSimplePattern::Wildcard => self.byte(2),
        }
    }

    /// Returns the current state as the handled value of the callback.
    fn produce(&self) -> u64 {
        self.state
    }
}

impl SmtHandler for TraceHash {
    type Error = NonstandardCommandError;
    type Resources = ();

    type SExpr = u64;
    type Attribute = u64;
    type Sort = u64;
    type Term = u64;

    fn handle_sort(&mut self, sort: SmtSort<Self>) -> Result<u64, Self::Error> {
        self.byte(tag::SORT);
        self.ident(&sort.ident);
        self.values(&sort.applied);
        Ok(self.produce())
    }

    fn handle_term(&mut self, term: SmtTerm<Self>) -> Result<u64, Self::Error> {
        self.byte(tag::TERM);
        match &term {
            SmtTerm::SpecialConstant(constant) => {
                self.byte(1);
                self.special_constant(constant);
            }
            SmtTerm::QualifiedIdent(ident) => {
                self.byte(2);
                self.ident(&ident.ident);
                self.optional_value(ident.sort);
            }
            SmtTerm::Application(application) => {
                self.byte(3);
                self.ident(&application.function.ident);
                self.optional_value(application.function.sort);
                self.values(&application.args);
            }
        }
        Ok(self.produce())
    }

    fn handle_s_expr(&mut self, expr: SmtSExpr<Self>) -> Result<u64, Self::Error> {
        self.byte(tag::S_EXPR);
        match &expr {
            SmtSExpr::SpecialConstant(constant) => {
                self.byte(1);
                self.special_constant(constant);
            }
            SmtSExpr::Symbol(symbol) => {
                self.byte(2);
                self.symbol(symbol);
            }
            SmtSExpr::Reserved(reserved) => {
                self.byte(3);
                self.bytes(reserved.as_str().as_bytes());
            }
            SmtSExpr::Keyword(keyword) => {
                self.byte(4);
                self.keyword(keyword);
            }
            SmtSExpr::SExprs(exprs) => {
                self.byte(5);
                self.values(exprs);
            }
        }
        Ok(self.produce())
    }

    fn handle_attribute(
        &mut self,
        name: SmtKeyword,
        value: Option<SmtAttributeValue<Self>>,
    ) -> Result<u64, Self::Error> {
        self.byte(tag::ATTRIBUTE);
        self.keyword(&name);
        match &value {
            None => self.byte(0),
            Some(SmtAttributeValue::SpecialConstant(constant)) => {
                self.byte(1);
                self.special_constant(constant);
            }
            Some(SmtAttributeValue::Symbol(symbol)) => {
                self.byte(2);
                self.symbol(symbol);
            }
            Some(SmtAttributeValue::SExprs(exprs)) => {
                self.byte(3);
                self.values(exprs);
            }
        }
        Ok(self.produce())
    }

    fn annotate_term(&mut self, term: u64, attributes: Vec<u64>) -> Result<u64, Self::Error> {
        self.byte(tag::ANNOTATE_TERM);
        self.u64(term);
        self.values(&attributes);
        Ok(self.produce())
    }

    fn start_let(&mut self, bindings: Vec<(SmtSymbol, u64)>) -> Result<(), Self::Error> {
        self.byte(tag::START_LET);
        self.count(bindings.len());
        for (name, term) in &bindings {
            self.symbol(name);
            self.u64(*term);
        }
        Ok(())
    }

    fn end_let(&mut self, term: u64) -> Result<u64, Self::Error> {
        self.byte(tag::END_LET);
        self.u64(term);
        Ok(self.produce())
    }

    fn start_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        name: SmtSymbol,
        sort: u64,
    ) -> Result<(), Self::Error> {
        self.byte(tag::START_QUANTIFIER);
        self.byte(match kind {
            SmtQuantifierKind::Exists => 1,
            SmtQuantifierKind::Forall => 2,
        });
        self.symbol(&name);
        self.u64(sort);
        Ok(())
    }

    fn end_quantifier(&mut self, term: u64) -> Result<u64, Self::Error> {
        self.byte(tag::END_QUANTIFIER);
        self.u64(term);
        Ok(self.produce())
    }

    fn start_lambda(&mut self, name: SmtSymbol, sort: u64) -> Result<(), Self::Error> {
        self.byte(tag::START_LAMBDA);
        self.symbol(&name);
        self.u64(sort);
        Ok(())
    }

    fn end_lambda(&mut self, term: u64) -> Result<u64, Self::Error> {
        self.byte(tag::END_LAMBDA);
        self.u64(term);
        Ok(self.produce())
    }

    fn start_match(&mut self, scrutinee: u64) -> Result<(), Self::Error> {
        self.byte(tag::START_MATCH);
        self.u64(scrutinee);
        Ok(())
    }

    fn start_match_case(&mut self, pattern: SmtPattern) -> Result<(), Self::Error> {
        self.byte(tag::START_MATCH_CASE);
        match &pattern {
            SmtPattern::Simple(simple) => {
                self.byte(1);
                self.simple_pattern(simple);
            }
            SmtPattern::Application { constructor, args } => {
                self.byte(2);
                self.symbol(constructor);
                self.count(args.len());
                for arg in args {
                    self.simple_pattern(arg);
                }
            }
        }
        Ok(())
    }

    fn end_match_case(&mut self, term: u64) -> Result<(), Self::Error> {
        self.byte(tag::END_MATCH_CASE);
        self.u64(term);
        Ok(())
    }

    fn end_match(&mut self) -> Result<u64, Self::Error> {
        self.byte(tag::END_MATCH);
        Ok(self.produce())
    }
}

impl CommandHandler for TraceHash {
    type NonstandardParser = NoCommandParser;

    fn nonstandard_command(
        &mut self,
        name: SmtSymbolView<'_>,
    ) -> Result<Self::NonstandardParser, Self::Error> {
        // nonstandard commands are rejected, as by CheckStandardSyntax, so the
        // sweep reports the same failure classes as the plain parse sweep
        Err(NonstandardCommandError(name.into_owned()))
    }

    fn command_echo(&mut self, value: SmtStringContent) -> Result<(), Self::Error> {
        self.byte(tag::ECHO);
        self.bytes(value.as_slice());
        Ok(())
    }

    fn command_get_option(&mut self, option: SmtKeyword) -> Result<(), Self::Error> {
        self.byte(tag::GET_OPTION);
        self.keyword(&option);
        Ok(())
    }

    fn command_set_option(&mut self, option: u64) -> Result<(), Self::Error> {
        self.byte(tag::SET_OPTION);
        self.u64(option);
        Ok(())
    }

    fn command_get_info(&mut self, keyword: SmtKeyword) -> Result<(), Self::Error> {
        self.byte(tag::GET_INFO);
        self.keyword(&keyword);
        Ok(())
    }

    fn command_set_info(&mut self, attribute: u64) -> Result<(), Self::Error> {
        self.byte(tag::SET_INFO);
        self.u64(attribute);
        Ok(())
    }

    fn command_set_logic(&mut self, logic: SmtSymbol) -> Result<(), Self::Error> {
        self.byte(tag::SET_LOGIC);
        self.symbol(&logic);
        Ok(())
    }

    fn command_get_value(&mut self, terms: Vec<u64>) -> Result<(), Self::Error> {
        self.byte(tag::GET_VALUE);
        self.values(&terms);
        Ok(())
    }

    fn command_get_assertions(&mut self) -> Result<(), Self::Error> {
        self.byte(tag::GET_ASSERTIONS);
        Ok(())
    }

    fn command_get_assignment(&mut self) -> Result<(), Self::Error> {
        self.byte(tag::GET_ASSIGNMENT);
        Ok(())
    }

    fn command_get_model(&mut self) -> Result<(), Self::Error> {
        self.byte(tag::GET_MODEL);
        Ok(())
    }

    fn command_get_proof(&mut self) -> Result<(), Self::Error> {
        self.byte(tag::GET_PROOF);
        Ok(())
    }

    fn command_get_unsat_assumptions(&mut self) -> Result<(), Self::Error> {
        self.byte(tag::GET_UNSAT_ASSUMPTIONS);
        Ok(())
    }

    fn command_get_unsat_core(&mut self) -> Result<(), Self::Error> {
        self.byte(tag::GET_UNSAT_CORE);
        Ok(())
    }

    fn command_declare_sort(
        &mut self,
        name: SmtSymbol,
        arity: SmtNumeral,
    ) -> Result<(), Self::Error> {
        self.byte(tag::DECLARE_SORT);
        self.symbol(&name);
        self.numeral(&arity);
        Ok(())
    }

    fn command_declare_sort_parameter(&mut self, name: SmtSymbol) -> Result<(), Self::Error> {
        self.byte(tag::DECLARE_SORT_PARAMETER);
        self.symbol(&name);
        Ok(())
    }

    fn command_declare_fun(
        &mut self,
        name: SmtSymbol,
        param_sorts: Vec<u64>,
        result_sort: u64,
    ) -> Result<(), Self::Error> {
        self.byte(tag::DECLARE_FUN);
        self.symbol(&name);
        self.values(&param_sorts);
        self.u64(result_sort);
        Ok(())
    }

    fn command_assert(&mut self, term: u64) -> Result<(), Self::Error> {
        self.byte(tag::ASSERT);
        self.u64(term);
        Ok(())
    }

    fn command_check_sat(&mut self, assumptions: Vec<u64>) -> Result<(), Self::Error> {
        self.byte(tag::CHECK_SAT);
        self.values(&assumptions);
        Ok(())
    }

    fn command_reset(&mut self) -> Result<(), Self::Error> {
        self.byte(tag::RESET);
        Ok(())
    }

    fn command_reset_assertions(&mut self) -> Result<(), Self::Error> {
        self.byte(tag::RESET_ASSERTIONS);
        Ok(())
    }

    fn command_exit(&mut self) -> Result<(), Self::Error> {
        self.byte(tag::EXIT);
        Ok(())
    }

    fn command_push(&mut self, amount: SmtNumeral) -> Result<(), Self::Error> {
        self.byte(tag::PUSH);
        self.numeral(&amount);
        Ok(())
    }

    fn command_pop(&mut self, amount: SmtNumeral) -> Result<(), Self::Error> {
        self.byte(tag::POP);
        self.numeral(&amount);
        Ok(())
    }

    fn start_define_sort(
        &mut self,
        name: SmtSymbol,
        params: Vec<SmtSymbol>,
    ) -> Result<(), Self::Error> {
        self.byte(tag::START_DEFINE_SORT);
        self.symbol(&name);
        self.symbols(&params);
        Ok(())
    }

    fn end_define_sort(&mut self, sort: u64) -> Result<(), Self::Error> {
        self.byte(tag::END_DEFINE_SORT);
        self.u64(sort);
        Ok(())
    }

    fn start_define_fun(
        &mut self,
        signature: SmtFunctionSignature<Self>,
    ) -> Result<(), Self::Error> {
        self.byte(tag::START_DEFINE_FUN);
        self.signature(&signature);
        Ok(())
    }

    fn end_define_fun(&mut self, term: u64) -> Result<(), Self::Error> {
        self.byte(tag::END_DEFINE_FUN);
        self.u64(term);
        Ok(())
    }

    fn start_define_funs_rec(
        &mut self,
        signatures: Vec<SmtFunctionSignature<Self>>,
    ) -> Result<(), Self::Error> {
        self.byte(tag::START_DEFINE_FUNS_REC);
        self.count(signatures.len());
        for signature in &signatures {
            self.signature(signature);
        }
        Ok(())
    }

    fn start_recursive_body(&mut self) -> Result<(), Self::Error> {
        self.byte(tag::START_RECURSIVE_BODY);
        Ok(())
    }

    fn end_recursive_body(&mut self, term: u64) -> Result<(), Self::Error> {
        self.byte(tag::END_RECURSIVE_BODY);
        self.u64(term);
        Ok(())
    }

    fn end_define_funs_rec(&mut self) -> Result<(), Self::Error> {
        self.byte(tag::END_DEFINE_FUNS_REC);
        Ok(())
    }

    fn start_declare_datatypes(
        &mut self,
        introductions: Vec<(SmtSymbol, SmtNumeral)>,
    ) -> Result<(), Self::Error> {
        self.byte(tag::START_DECLARE_DATATYPES);
        self.count(introductions.len());
        for (name, arity) in &introductions {
            self.symbol(name);
            self.numeral(arity);
        }
        Ok(())
    }

    fn start_datatype_declaration(
        &mut self,
        sort_params: Vec<SmtSymbol>,
    ) -> Result<(), Self::Error> {
        self.byte(tag::START_DATATYPE_DECLARATION);
        self.symbols(&sort_params);
        Ok(())
    }

    fn end_datatype_declaration(
        &mut self,
        constructors: Vec<SmtDatatypeConstructor<Self>>,
    ) -> Result<(), Self::Error> {
        self.byte(tag::END_DATATYPE_DECLARATION);
        self.count(constructors.len());
        for constructor in &constructors {
            self.symbol(&constructor.name);
            self.sorted_vars(&constructor.selectors);
        }
        Ok(())
    }

    fn end_declare_datatypes(&mut self) -> Result<(), Self::Error> {
        self.byte(tag::END_DECLARE_DATATYPES);
        Ok(())
    }
}
