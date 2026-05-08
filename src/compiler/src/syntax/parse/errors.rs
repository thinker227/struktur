//! Helper module for all errors produced by the parser.

use crate::text::TextSpan;
use ariadne::Label;

use crate::{
    diagnostic::Diagnostic,
    syntax::{SyntaxErrorCode, TokenKind},
};

use super::Parser;

impl Parser<'_> {
    pub(super) fn error_unexpected_token(
        &self,
        span: TextSpan,
        found: TokenKind,
        expected: impl ToString,
    ) -> Diagnostic {
        let expected = expected.to_string();
        self.error(SyntaxErrorCode::UnexpectedToken, span, move |report| {
            report.with_message(format!("Found {found}, expected {expected}"))
        })
    }

    pub(super) fn error_ty_ann_not_allowed(
        &self,
        target_span: TextSpan,
        full_span: TextSpan,
        kind: impl ToString,
    ) -> Diagnostic {
        let kind = kind.to_string();
        self.error(SyntaxErrorCode::TyAnnNotAllowed, full_span, move |report| {
            report
                .with_message("Type annotation has to be enclosed in parentheses")
                .with_label(
                    Label::new(target_span.with_context(self.source.key()))
                        .with_message(format!("Assuming you intended to annotate this {}", kind)),
                )
        })
    }

    pub(super) fn error_empty_forall(&self, span: TextSpan) -> Diagnostic {
        self.error(SyntaxErrorCode::EmptyForall, span, |report| {
            report.with_message("Empty forall quantifier")
        })
    }

    pub(super) fn error_unknown_type(&self, span: TextSpan, text: &str) -> Diagnostic {
        self.error(SyntaxErrorCode::UnknownType, span, |report| {
            report.with_message(format!("Unknown type `{text}`"))
        })
    }
}
