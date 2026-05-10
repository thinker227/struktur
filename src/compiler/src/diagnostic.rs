//! Diagnostics and error reporting.

use std::{fmt::Display, sync::Arc};

use ariadne::ReportKind;

use crate::text::TextLocation;

pub type Report = ariadne::Report<'static, TextLocation>;
pub type ReportBuilder = ariadne::ReportBuilder<'static, TextLocation>;

/// The category of a diagnostic code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Category {
    Parse,
    Resolve,
}

impl Display for Category {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Category::Parse => write!(f, "PARSE"),
            Category::Resolve => write!(f, "RESOLVE"),
        }
    }
}

/// A code identifying a diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Code {
    category: Category,
    id: u16,
}

impl Code {
    /// Creates a new code.
    pub fn new(category: Category, id: u16) -> Self {
        Self { category, id }
    }

    /// Makes a code with the [Category::Parse] category.
    pub fn parse(id: u16) -> Self {
        Self::new(Category::Parse, id)
    }

    /// Gets the category.
    pub fn category(self) -> Category {
        self.category
    }

    /// Gets the numeric ID.
    pub fn id(self) -> u16 {
        self.id
    }
}

impl Display for Code {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{:03}", self.category, self.id)
    }
}

/// Severity of a diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
}

impl From<Severity> for ReportKind<'static> {
    fn from(value: Severity) -> Self {
        match value {
            Severity::Error => ReportKind::Error,
        }
    }
}

/// A compiler diagnostic.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    severity: Severity,
    code: Code,
    location: TextLocation,
    report: Arc<Report>,
}

impl Diagnostic {
    /// Makes a new diagnostic.
    pub fn make(
        severity: Severity,
        code: Code,
        location: TextLocation,
        build: impl FnOnce(ReportBuilder) -> ReportBuilder,
    ) -> Self {
        let builder = Report::build(severity.into(), location);
        let report = build(builder).with_code(code).finish();

        Self {
            severity,
            code,
            location,
            report: Arc::new(report),
        }
    }

    /// Makes a new diagnostic with the [ReportKind::Error] report kind.
    pub fn error(
        code: Code,
        location: TextLocation,
        build: impl FnOnce(ReportBuilder) -> ReportBuilder,
    ) -> Self {
        Self::make(Severity::Error, code, location, build)
    }

    /// Gets the diagnostic severity.
    pub fn severity(&self) -> Severity {
        self.severity
    }

    /// Gets the diagnostic code.
    pub fn code(&self) -> Code {
        self.code
    }

    /// Gets the diagnostic location.
    pub fn location(&self) -> TextLocation {
        self.location
    }

    /// Gets the diagnostic report.
    pub fn report(&self) -> &Report {
        &self.report
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn code_display() {
        assert_eq!(Code::new(Category::Parse, 1).to_string(), "PARSE001");
        assert_eq!(Code::new(Category::Parse, 42).to_string(), "PARSE042");
        assert_eq!(Code::new(Category::Parse, 621).to_string(), "PARSE621");
    }
}
