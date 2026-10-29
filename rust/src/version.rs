use crate::lexicon::SmtDecimal;

/// Version of the SMT-LIB standard (2.0, 2.5, 2.6, or 2.7).
///
/// A script declares the version it is written in with an attribute, e.g.
/// `(set-info :smt-lib-version 2.6)`.
///
/// A version decides which words are reserved and which syntax is accepted, e.g. `lambda` and
/// the wildcard `_` from 2.7 on, and `match` and `declare-datatype` from 2.6 on. Under an earlier
/// version, the name of a later command is a symbol, so the command is nonstandard.
///
/// The default version is SMT-LIB 2.7.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord)]
pub enum SmtVersion {
    /// Version 2.0.
    V2_0,
    /// Version 2.5.
    V2_5,
    /// Version 2.6.
    V2_6,
    /// Version 2.7.
    #[default]
    V2_7,
}

impl SmtVersion {
    /// Returns the version that the decimal names, if any.
    pub fn from_decimal(decimal: SmtDecimal<'_>) -> Option<Self> {
        match decimal.as_slice() {
            b"2.0" => Some(SmtVersion::V2_0),
            b"2.5" => Some(SmtVersion::V2_5),
            b"2.6" => Some(SmtVersion::V2_6),
            b"2.7" => Some(SmtVersion::V2_7),
            _ => None,
        }
    }

    /// Returns the decimal that names the version, as in `:smt-lib-version`.
    pub fn as_decimal(&self) -> SmtDecimal<'static> {
        let decimal: &'static [u8] = match self {
            SmtVersion::V2_0 => b"2.0",
            SmtVersion::V2_5 => b"2.5",
            SmtVersion::V2_6 => b"2.6",
            SmtVersion::V2_7 => b"2.7",
        };
        SmtDecimal::new_unchecked(decimal)
    }
}

/// Version posture (versions a script may declare and how many declarations it may make).
///
/// The posture applies to version declarations `(set-info :smt-lib-version …)` only;
/// the initial version is unaffected by the posture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtVersionPosture {
    allowed: Vec<SmtVersion>,
    max_declarations: Option<u64>,
}

impl SmtVersionPosture {
    /// Returns the allowed versions.
    pub fn allowed(&self) -> &[SmtVersion] {
        &self.allowed
    }

    /// Returns the maximum number of version declarations, or [`None`] if unlimited.
    pub fn max_declarations(&self) -> Option<u64> {
        self.max_declarations
    }
}

impl Default for SmtVersionPosture {
    /// Returns the default posture.
    ///
    /// The default posture allows versions 2.5, 2.6 and 2.7, and at most one version declaration.
    fn default() -> Self {
        SmtVersionPostureBuilder::new().build()
    }
}

/// Builds a version posture.
///
/// For example, a posture that also allows SMT-LIB 2.0 and any number of version declarations:
///
/// ```
/// use blazing_smtlib::{SmtReader, SmtSyntaxChecker, SmtVersion, SmtVersionPostureBuilder};
///
/// let posture = SmtVersionPostureBuilder::new()
///     .add_allowed(SmtVersion::V2_0)
///     .set_max_declarations(None)
///     .build();
/// let mut handler = SmtSyntaxChecker;
/// let mut reader = SmtReader::script(&mut handler, posture, SmtVersion::V2_7);
/// reader
///     .read_all(b"(set-info :smt-lib-version 2.0)\n(set-info :smt-lib-version 2.6)")
///     .unwrap();
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtVersionPostureBuilder {
    allowed: Vec<SmtVersion>,
    max_declarations: Option<u64>,
}

impl SmtVersionPostureBuilder {
    /// Creates a builder with the [default posture](SmtVersionPosture::default).
    pub fn new() -> Self {
        Self {
            allowed: vec![SmtVersion::V2_5, SmtVersion::V2_6, SmtVersion::V2_7],
            max_declarations: Some(1),
        }
    }

    /// Returns the allowed versions.
    pub fn allowed(&self) -> &[SmtVersion] {
        &self.allowed
    }

    /// Returns the maximum number of version declarations, or [`None`] if unlimited.
    pub fn max_declarations(&self) -> Option<u64> {
        self.max_declarations
    }

    /// Disallows every version.
    pub fn clear_allowed(mut self) -> Self {
        self.allowed.clear();
        self
    }

    /// Allows the version.
    pub fn add_allowed(mut self, allowed: SmtVersion) -> Self {
        self.allowed.push(allowed);
        self
    }

    /// Disallows the version.
    pub fn remove_allowed(mut self, allowed: SmtVersion) -> Self {
        while let Some(index) = self.allowed.iter().position(|elem| *elem == allowed) {
            self.allowed.remove(index);
        }
        self
    }

    /// Sets the maximum number of version declarations ([`None`] for unlimited).
    pub fn set_max_declarations(mut self, max_declarations: Option<u64>) -> Self {
        self.max_declarations = max_declarations;
        self
    }

    /// Builds the version posture.
    pub fn build(self) -> SmtVersionPosture {
        SmtVersionPosture {
            allowed: self.allowed,
            max_declarations: self.max_declarations,
        }
    }
}

impl Default for SmtVersionPostureBuilder {
    fn default() -> Self {
        Self::new()
    }
}
