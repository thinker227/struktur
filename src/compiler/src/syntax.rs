//! Syntax tree, parsing, and lexing.
//!
//! The syntax tree consists of two parts: an untyped core, and a strongly typed layer on top of that.
//! The parser produces a set of untyped [SyntaxNode]s which are just a set of children nodes and tokens
//! along with a [SyntaxKind] identifying the node. The strongly typed layer is then lazily built on top of
//! the untyped tree, providing rigid structure using a set of structs and enums.

use crate::text::{Spanned, TextSpan};
use lex::{LexError, unknown_character};
use logos::Logos;
use serde::Serialize;

pub mod lex;
pub mod nodes;
pub mod parse;
pub mod selector;
pub mod tree;

pub use tree::NodeId;

pub type Nodes = tree::Nodes<SyntaxKind, Token>;
pub type NodeBuilder = tree::NodeBuilder<SyntaxKind, Token>;
pub type SyntaxNode<'map> = tree::SyntaxNode<'map, SyntaxKind, Token>;

/// A syntax token.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct Token {
    pub kind: TokenKind,
    pub span: TextSpan,
}

impl Spanned for Token {
    fn span(&self) -> TextSpan {
        self.span
    }
}

/// Identifies the kind of a syntax token.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Logos)]
#[logos(error(LexError, callback = unknown_character))]
#[logos(subpattern ident = r"\p{L}(?:[\p{L}\p{N}])*")]
#[logos(skip(r"[ \t\r\n\f]+", logos::skip))]
#[logos(skip(r"//[^\n]*", allow_greedy = true))]
#[logos(utf8 = true)]
pub enum TokenKind {
    // ------------------
    // Static token kinds
    // ------------------
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

    // --------------------
    // Variable token kinds
    // --------------------
    #[regex("(?&ident)")]
    Ident,

    #[regex("'(?&ident)")]
    TypeVar,

    #[regex("[0-9]+")]
    Number,

    #[regex(r#""(?:(?:\")|[^"])*""#)]
    String,

    // -------------------
    // Special tokens kind
    // -------------------
    EndOfInput,
}

/// Identifies the kind of a syntax node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum SyntaxKind {
    /// Identifiers.
    Ident,

    /// The root of the tree.
    Root,

    /// Binding items.
    Binding,

    /// Unit expressions.
    UnitExpr,
    /// Int expressions.
    IntExpr,
    /// Bool expressions.
    BoolExpr,
    /// String expressions.
    StringExpr,
    /// Variable expressions.
    VarExpr,
    /// Let-expressions.
    LetExpr,
    /// Lambda expressions.
    LambdaExpr,
    /// Application expressions.
    ApplicationExpr,
    /// If-else expressions.
    IfElseExpr,
    /// Type annotation expressions.
    TyAnnExpr,
    /// Syntactic grouping expressions.
    GroupingExpr,

    /// A case.
    Case,

    /// Wildcard patterns.
    WildcardPattern,
    /// Variable patterns.
    VarPattern,
    /// Unit patterns.
    UnitPattern,
    /// Int patterns.
    IntPattern,
    /// Bool patterns.
    BoolPattern,
    /// Type annotation patterns.
    TyAnnPattern,
    /// Syntactic grouping pattern.
    GroupingPattern,

    /// Type annotations.
    TyAnn,

    /// The unit type.
    UnitTyExpr,
    /// The int type.
    IntTyExpr,
    /// The bool type.
    BoolTyExpr,
    /// The string type.
    StringTyExpr,
    /// Type variables type expressions.
    VarTyExpr,
    /// Function type expressions.
    FunctionTyExpr,
    /// Forall type expressions.
    ForallTyExpr,
    /// Syntactic grouping type expressions.
    GroupingTyExpr,
}

impl TokenKind {
    pub fn static_source(&self) -> Option<&'static str> {
        match self {
            Self::Equals => Some("="),
            Self::Colon => Some(":"),
            Self::Dot => Some("."),
            Self::Backslash => Some("\\"),
            Self::Bar => Some("|"),
            Self::Underscore => Some("_"),
            Self::DashGreaterThan => Some("->"),
            Self::OpenParen => Some("("),
            Self::CloseParen => Some(")"),
            Self::True => Some("true"),
            Self::False => Some("false"),
            Self::Let => Some("let"),
            Self::In => Some("in"),
            Self::Fun => Some("fun"),
            Self::If => Some("if"),
            Self::Then => Some("then"),
            Self::Else => Some("else"),
            Self::Forall => Some("forall"),
            Self::Ident => None,
            Self::TypeVar => None,
            Self::Number => None,
            Self::String => None,
            Self::EndOfInput => None,
        }
    }

    pub fn display_source(&self) -> &'static str {
        match self {
            Self::Ident => "name",
            Self::TypeVar => "type variable name",
            Self::Number => "number",
            Self::String => "string",
            Self::EndOfInput => "end of input",

            _ => self.static_source().unwrap(),
        }
    }
}

impl std::fmt::Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.static_source() {
            Some(x) => write!(f, "`{x}`"),
            None => write!(f, "{}", self.display_source()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
enum SyntaxErrorCode {
    UnknownCharacter = 1,
    UnexpectedToken = 2,
    TyAnnNotAllowed = 3,
    EmptyForall = 4,
    UnknownType = 5,
}

impl From<SyntaxErrorCode> for u16 {
    fn from(value: SyntaxErrorCode) -> Self {
        value as u16
    }
}
