//! Utilities for lexing.

use crate::{
    diagnostic::{Code, Diagnostic},
    sources::{Source, SourceContext},
    syntax::SyntaxErrorCode,
    text::TextSpan,
};

use super::{Token, TokenKind};
use logos::Logos as _;

/// An error produced by lexing.
///
/// Only used internally, externally [Diagnostic] is returned as the error from lexing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LexError {
    span: TextSpan,
}

impl LexError {
    pub fn to_diagnostic(self, context: SourceContext) -> Diagnostic {
        let code = Code::parse(SyntaxErrorCode::UnknownCharacter.into());
        Diagnostic::error(code, self.span.with_context(context), |report| {
            report.with_message("Unknown character")
        })
    }
}

impl Default for LexError {
    /// Always panics.
    fn default() -> Self {
        // There is no "default" for lex errors, but Logos requires this impl.
        unimplemented!()
    }
}

pub(super) fn unknown_character(lex: &mut logos::Lexer<TokenKind>) -> LexError {
    LexError {
        span: lex.span().into(),
    }
}

/// Grouping of a set of tokens, an end-of-input tokens, as well as the source the tokens originate from.
pub struct Tokens<'a> {
    pub tokens: Vec<Token>,
    pub eoi: Token,
    pub source: &'a Source,
}

/// Lexes a string into an iterator of tokens.
pub fn lex(source: &Source) -> Result<Tokens<'_>, Diagnostic> {
    let text = source.text();
    let context = source.key();

    let tokens = TokenKind::lexer(text.text())
        .spanned()
        .map(|(item, range)| {
            item.map(|kind| Token {
                kind,
                span: range.into(),
            })
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| e.to_diagnostic(context))?;

    let eoi = Token {
        kind: TokenKind::EndOfInput,
        span: TextSpan::empty(text.len()),
    };

    Ok(Tokens {
        tokens,
        eoi,
        source,
    })
}
