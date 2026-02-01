use std::fmt::Display;

use logos::Logos;

use crate::{parse::ParseError, text_span::TextSpan};

#[derive(Debug, Clone, Copy)]
pub struct Token<'src> {
    pub kind: TokenKind,
    pub text: &'src str,
    pub span: TextSpan,
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(static_str) = self.kind.static_source() {
            write!(f, "{}", static_str.escape_debug())?;
        } else {
            write!(f, "{:?} `{}`", self.kind, self.text.escape_debug())?;
        }

        write!(f, " @ {}..{}", self.span.offset(), self.span.offset() + self.span.len())?;

        Ok(())
    }
}

#[allow(unused, reason = "Used by Logos derive.")]
fn unknown_token(lex: &mut logos::Lexer<TokenKind>) -> ParseError {
    ParseError::UnknownCharacter {
        char_span: lex.span().into(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[derive(Logos)]
#[logos(utf8 = true)]
#[logos(error(ParseError, callback = unknown_token))]
#[logos(subpattern name = r"\p{L}(?:[\p{L}\p{N}])*")]
#[logos(skip(r"[ \t\r\n\f]"))]
#[logos(skip(r"//[^\n]*", allow_greedy = true))]
pub enum TokenKind {
    #[token("=")]
    Equals,

    #[token(":")]
    Colon,

    #[token(".")]
    Dot,

    #[token(r"\")]
    Backslash,

    #[token("|")]
    Bar,

    #[token("_")]
    Underscore,

    #[token("->")]
    DashGreaterThan,

    #[token("(")]
    OpenParen,

    #[token(")")]
    CloseParen,

    #[token("true")]
    True,

    #[token("false")]
    False,

    #[token("let")]
    Let,

    #[token("in")]
    In,

    #[token("fun")]
    Fun,

    #[token("if")]
    If,

    #[token("then")]
    Then,

    #[token("else")]
    Else,

    #[token("forall")]
    Forall,

    #[regex("(?&name)")]
    Name,

    #[regex("'(?&name)")]
    TypeVarName,

    #[regex("[0-9]+")]
    Number,

    #[regex(r#""(?:(?:\")|[^"])*""#)]
    String,

    EndOfInput,
}

impl TokenKind {
    pub fn static_source(&self) -> Option<&'static str> {
        use TokenKind::*;
        match self {
            Equals => Some("="),
            Colon => Some(":"),
            Dot => Some("."),
            Backslash => Some("\\"),
            Bar => Some("|"),
            Underscore => Some("_"),
            DashGreaterThan => Some("->"),
            OpenParen => Some("("),
            CloseParen => Some(")"),
            True => Some("true"),
            False => Some("false"),
            Let => Some("let"),
            In => Some("in"),
            Fun => Some("fun"),
            If => Some("if"),
            Then => Some("then"),
            Else => Some("else"),
            Forall => Some("forall"),
            Name => None,
            TypeVarName => None,
            Number => None,
            String => None,
            EndOfInput => None,
        }
    }

    pub fn display_source(&self) -> &'static str {
        use TokenKind::*;
        match self {
            Name => "name",
            TypeVarName => "type variable name",
            Number => "number",
            String => "string",
            EndOfInput => "end of input",

            _ => self.static_source().unwrap()
        }
    }
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.static_source() {
            Some(x) => write!(f, "`{x}`"),
            None => write!(f, "{}", self.display_source())
        }
    }
}

#[derive(Debug, Clone)]
pub struct Lexed<'src> {
    pub tokens: Vec<Token<'src>>,
    pub eoi: Token<'static>,
}

pub fn lex(source: &str) -> Result<Lexed<'_>, ParseError> {
    let lexer = TokenKind::lexer(source);
    let tokens = lexer.spanned()
        .map(|(kind, span)|
            kind.map(|kind| Token {
                kind,
                text: &source[span.clone()],
                span: span.into()
            }))
        .collect::<Result<Vec<_>, _>>()?;

    let eoi = Token {
        kind: TokenKind::EndOfInput,
        text: "",
        span: TextSpan::empty(source.len())
    };

    Ok(Lexed {
        tokens,
        eoi
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn print_result(res: &Result<Lexed, ParseError>) {
        match res {
            Ok(lexed) => {
                for t in &lexed.tokens {
                    println!("{}", t);
                }
                println!("{}", lexed.eoi);
            }
            Err(e) => println!("{e:?}")
        }
    }

    #[test]
    fn indent() {
        let s = "a\n  b \n  c\n    d\ne";

        let result = lex(s);

        print_result(&result);
    }

    #[test]
    fn names() {
        let s = "a bc d0 åäö ä1";

        let result = lex(s);

        print_result(&result);
    }

    #[test]
    fn foo() {
        let s = "  a\n    b\n  c\n    d\n  e";

        let result = lex(s);

        print_result(&result);
    }
}
