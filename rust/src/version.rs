use crate::SmtDecimal;

/// Version of the SMT-LIB standard.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord)]
pub enum SmtVersion {
    V2_0,
    V2_5,
    V2_6,
    #[default]
    V2_7,
}

impl SmtVersion {
    /// The version that the decimal names, if any.
    pub fn from_decimal(decimal: &[u8]) -> Option<Self> {
        match decimal {
            b"2.0" => Some(SmtVersion::V2_0),
            b"2.5" => Some(SmtVersion::V2_5),
            b"2.6" => Some(SmtVersion::V2_6),
            b"2.7" => Some(SmtVersion::V2_7),
            _ => None,
        }
    }

    /// The decimal that names the version, as in `:smt-lib-version`.
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtVersionPosture {
    allowed: Vec<SmtVersion>,
    max_declarations: Option<u64>,
}

impl SmtVersionPosture {
    pub fn allowed(&self) -> &[SmtVersion] {
        &self.allowed
    }

    pub fn max_declarations(&self) -> Option<u64> {
        self.max_declarations
    }
}

impl Default for SmtVersionPosture {
    fn default() -> Self {
        SmtVersionPostureBuilder::new().build()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtVersionPostureBuilder {
    allowed: Vec<SmtVersion>,
    max_declarations: Option<u64>,
}

impl SmtVersionPostureBuilder {
    pub fn new() -> Self {
        Self {
            allowed: vec![SmtVersion::V2_5, SmtVersion::V2_6, SmtVersion::V2_7],
            max_declarations: Some(1),
        }
    }

    pub fn allowed(&self) -> &[SmtVersion] {
        &self.allowed
    }

    pub fn max_declarations(&self) -> Option<u64> {
        self.max_declarations
    }

    pub fn clear_allowed(&mut self) -> &mut Self {
        self.allowed.clear();
        self
    }

    pub fn add_allowed(&mut self, allowed: SmtVersion) -> &mut Self {
        self.allowed.push(allowed);
        self
    }

    pub fn remove_allowed(&mut self, allowed: SmtVersion) -> &mut Self {
        while let Some(index) = self.allowed.iter().position(|elem| *elem == allowed) {
            self.allowed.remove(index);
        }
        self
    }

    pub fn set_max_declarations(&mut self, max_declarations: Option<u64>) -> &mut Self {
        self.max_declarations = max_declarations;
        self
    }

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
