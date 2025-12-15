mod lex;

use std::{rc::Rc, vec};

use crate::{ast::*, id::IdProvider, stage::{Parse, Stage}, text_span::TextSpan};
use self::lex::{Token, TokenKind, lex};

#[derive(Debug, Clone, thiserror::Error, miette::Diagnostic)]
pub enum ParseError {
    #[error("Unknown character")]
    UnknownCharacter {
        #[label]
        char_span: TextSpan,
    },

    #[error("Only ASCII space characters are allowed as indentation")]
    IllegalIndentation {
        #[label("This whitespace character is not allowed as indentation")]
        char_span: TextSpan,
    },

    #[error("Indentation of {indentation} character(s) does not match that of any block")]
    InconsistentIndentation {
        indentation: usize,
        #[label]
        indent_span: TextSpan,
        #[related]
        blocks: Vec<IndentationHint>,
    },

    #[error("Found {found:?} token, expected {expected:?}")]
    UnexpectedToken {
        #[label]
        span: TextSpan,
        found: TokenKind,
        expected: TokenKind,
    },

    #[error("")]
    Foo {
        #[label]
        bar: (usize, usize)
    }
}

#[derive(Debug, Clone, thiserror::Error, miette::Diagnostic)]
#[error("Block with {indentation} indentation character(s) starts here")]
#[diagnostic(severity(advice))]
pub struct IndentationHint {
    indentation: usize,
    #[label]
    span: TextSpan,
}

type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug, Clone, Copy)]
enum CurrentToken<'src> {
    AtStart,
    Token(Token<'src>),
    AtEnd,
}

enum AllowBlock {
    Allow,
    Deny,
    Impartial,
}

#[derive(Debug, Clone)]
struct Parser<'src, 'tokens> {
    eoi: Token<'static>,
    tokens: &'tokens [Token<'src>],
    current: CurrentToken<'src>,
    id_provider: Rc<IdProvider<NodeId>>,
}

impl<'src, 'tokens> Parser<'src, 'tokens> {
    pub fn new(tokens: &'tokens [Token<'src>], eoi: Token<'static>) -> Self {
        Self {
            eoi,
            tokens,
            current: CurrentToken::AtStart,
            id_provider: Rc::new(IdProvider::new(NodeId))
        }
    }

    fn node_data(&self, data: <Parse as Stage>::NodeData) -> NodeData<Parse> {
        NodeData {
            id: self.id_provider.next(),
            data
        }
    }

    fn move_next(&mut self) -> Token<'src> {
        match self.tokens.first() {
            Some(t) => {
                self.current = CurrentToken::Token(*t);
                self.tokens = &self.tokens[1..];
                *t
            }
            None => {
                self.current = CurrentToken::AtEnd;
                self.eoi
            }
        }
    }

    fn current(&mut self) -> Token<'src> {
        match self.current {
            CurrentToken::AtStart => self.move_next(),
            CurrentToken::Token(token) => token,
            CurrentToken::AtEnd => self.eoi
        }
    }

    fn advance(&mut self) -> Token<'src> {
        let prev = self.current();
        self.move_next();
        prev
    }

    fn peek(&mut self, ahead: usize) -> Token<'src> {
        _ = self.current();

        match self.tokens.get(ahead) {
            Some(t) => *t,
            None => self.eoi
        }
    }

    fn expect(&mut self, kind: TokenKind) -> ParseResult<Token<'src>> {
        let current = self.current();
        if current.kind == kind {
            Ok(current)
        } else {
            Err(ParseError::UnexpectedToken {
                span: current.span,
                found: current.kind,
                expected: kind
            })
        }
    }

    fn parse_root(&mut self) -> ParseResult<Root<Parse>> {
        let mut items = Vec::new();

        while self.current().kind != TokenKind::EndOfInput {
            let item = self.parse_item()?;
            items.push(item);
        }

        let eoi = self.advance();

        let span = match items.first() {
            Some(item) => TextSpan::between(*item.data(), eoi.span),
            None => eoi.span
        };

        Ok(Root(items, self.node_data(span)))
    }

    fn parse_item(&mut self) -> ParseResult<Item<Parse>> {
        todo!()
    }

    fn parse_expr(&mut self) -> ParseResult<Expr<Parse>> {
        todo!()
    }

    fn parse_binding_expr(&mut self) -> ParseResult<Let<Parse>> {
        todo!()
    }

    fn parse_lambda_expr(&mut self) -> ParseResult<Lambda<Parse>> {
        todo!()
    }

    fn parse_application_expr(&mut self) -> ParseResult<Application<Parse>> {
        todo!()
    }
}

/// Parses a string into an AST.
pub fn parse(source: &str) -> Result<Ast<Parse>, ParseError> {
    let lexed = lex(source)?;
    let mut parser = Parser::new(&lexed.tokens, lexed.eoi);
    let root = parser.parse_root()?;

    Ok(Ast::new(root, (), ()))
}
