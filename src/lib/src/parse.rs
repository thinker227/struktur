//! Lexing and parsing source code into an initial AST.

mod lex;

use std::{fmt::Display, rc::Rc};

use crate::{ast::*, id::IdProvider, maybe_result::MaybeResult, stage::{Parse, Stage}, text_span::TextSpan};
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

    // #[error("Found {found} token in {context}, expected {expected}")]
    #[error("Found {found} token, expected {expected}")]
    UnexpectedToken {
        #[label]
        span: TextSpan,
        found: TokenKind,
        expected: String,
    }
}

impl ParseError {
    pub(self) fn unexpected_token(
        span: TextSpan,
        found: TokenKind,
        expected: impl Display
    ) -> Self {
        Self::UnexpectedToken {
            span,
            found,
            expected: expected.to_string()
        }
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

/// The context in which an atom expression is parsed.
///
/// For expressions starting with a keyword (such as `fun` in lambda expressions,
/// `if` in if-else expressions, and *especially* `let` in let-expressions),
/// this is used to distinguish whether the expression is allowed to be parsed immediately after
/// another expression, in order to not make syntax like `let x = x let y = y` ambiguous.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExprContext {
    /// The expression is parsed as normal.
    Normal,
    /// The expression is forbidden from being a keyword-led expression.
    /// Only used as the context for the argument expression in function applications.
    Trailing,
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

    fn _advance_if(&mut self, kind: TokenKind) -> Option<Token<'src>> {
        if self.current().kind == kind {
            Some(self.advance())
        } else {
            None
        }
    }

    fn _peek(&mut self, ahead: usize) -> Token<'src> {
        _ = self.current();

        match self.tokens.get(ahead) {
            Some(t) => *t,
            None => self.eoi
        }
    }

    fn expect(&mut self, kind: TokenKind) -> ParseResult<Token<'src>> {
        let current = self.current();
        if current.kind == kind {
            self.move_next();
            Ok(current)
        } else {
            Err(ParseError::unexpected_token(
                current.span,
                current.kind,
                kind
            ))
        }
    }

    fn parse_root(&mut self) -> ParseResult<Root<Parse>> {
        let mut items = Vec::new();

        while self.current().kind != TokenKind::EndOfInput {
            let item = self.parse_item()?;
            items.push(item);

            if self.current().kind == TokenKind::EndOfInput {
                break;
            }
        }

        let eoi = self.advance();

        let span = match items.first() {
            Some(item) => TextSpan::between(*item.data(), eoi.span),
            None => eoi.span
        };

        Ok(Root(items, self.node_data(span)))
    }

    fn parse_item(&mut self) -> ParseResult<Item<Parse>> {
        self.try_parse_item().unwrap_or_err(|| {
            let current = self.current();
            ParseError::unexpected_token(current.span, current.kind, "item")
        })
    }

    fn try_parse_item(&mut self) -> MaybeResult<Item<Parse>, ParseError> {
        let (item, span) = match self.current().kind {
            TokenKind::Let => {
                let (binding, span) = self.parse_binding()?;
                (ItemVal::Binding(binding), span)
            }

            _ => return MaybeResult::None
        };

        MaybeResult::Ok(Item(item, self.node_data(span)))
    }

    fn parse_binding(&mut self) -> ParseResult<(Binding<Parse>, TextSpan)> {
        self.expect(TokenKind::Let)?;
        let name = self.expect(TokenKind::Name)?;
        self.expect(TokenKind::Equals)?;
        let body = self.parse_expr()?;

        let span = TextSpan::between(name.span, body.2.data);

        Ok((
            Binding {
                symbol: name.text.to_owned(),
                body
            },
            span
        ))
    }

    fn parse_expr(&mut self) -> ParseResult<Expr<Parse>> {
        self.parse_application_expr()
    }

    fn parse_application_expr(&mut self) -> ParseResult<Expr<Parse>> {
        let mut result = self.parse_atom_expr(ExprContext::Normal)?;

        while let Some(expr) = self.try_parse_atom_expr(ExprContext::Trailing).into_option() {
            let expr = expr?;

            let span = TextSpan::between(result.2.data, expr.2.data);

            result = Expr(
                ExprVal::Apply(Box::new(Application {
                    target: result,
                    arg: expr
                })),
                (),
                self.node_data(span)
            );
        }

        Ok(result)
    }

    fn parse_atom_expr(&mut self, ctx: ExprContext) -> ParseResult<Expr<Parse>> {
        self.try_parse_atom_expr(ctx).unwrap_or_err(|| {
            let current = self.current();
            ParseError::unexpected_token(current.span, current.kind, "expression")
        })
    }

    fn try_parse_atom_expr(&mut self, ctx: ExprContext) -> MaybeResult<Expr<Parse>, ParseError> {
        let (expr, span) = match self.current().kind {
            TokenKind::OpenParen => {
                let open_paren = self.advance();

                if self.current().kind == TokenKind::CloseParen {
                    let close_paren = self.advance();
                    let span = TextSpan::between(open_paren.span, close_paren.span);
                    (ExprVal::Unit, span)
                } else {
                    let expr = self.parse_expr()?;
                    self.expect(TokenKind::CloseParen)?;
                    return MaybeResult::Ok(expr);
                }
            }

            TokenKind::Number => {
                let number = self.advance();
                let val = number.text.parse().unwrap();
                (ExprVal::Int(val), number.span)
            }

            TokenKind::True | TokenKind::False => {
                let bool = self.advance();
                let val = bool.kind == TokenKind::True;
                (ExprVal::Bool(val), bool.span)
            }

            TokenKind::_String => {
                let str = self.advance();
                let text = str.text;
                let val = text[1 .. text.len() - 1].to_owned();
                (ExprVal::String(val), str.span)
            }

            TokenKind::Name => {
                let name = self.advance();
                let var = name.text.to_owned();
                (ExprVal::Var(var), name.span)
            }

            TokenKind::Let if ctx == ExprContext::Normal => {
                let (r#let, span) = self.parse_let_expr()?;
                (ExprVal::Bind(Box::new(r#let)), span)
            }

            TokenKind::Fun if ctx == ExprContext::Normal => {
                let (lambda, span) = self.parse_lambda_expr()?;
                (ExprVal::Lambda(Box::new(lambda)), span)
            }

            TokenKind::If if ctx == ExprContext::Normal => {
                let (if_else, span) = self.parse_if_else_expr()?;
                (ExprVal::If(Box::new(if_else)), span)
            }

            _ => return MaybeResult::None
        };

        MaybeResult::Ok(Expr(expr, (), self.node_data(span)))
    }

    fn parse_let_expr(&mut self) -> ParseResult<(Let<Parse>, TextSpan)> {
        let r#let = self.expect(TokenKind::Let)?;
        let name = self.expect(TokenKind::Name)?;
        self.expect(TokenKind::Equals)?;
        let value = self.parse_expr()?;
        self.expect(TokenKind::In)?;
        let expr = self.parse_expr()?;

        let span = TextSpan::between(r#let.span, expr.2.data);

        Ok((
            Let {
                symbol: name.text.to_owned(),
                value,
                expr
            },
            span
        ))
    }

    fn parse_lambda_expr(&mut self) -> ParseResult<(Lambda<Parse>, TextSpan)> {
        let fun = self.expect(TokenKind::Fun)?;
        let param = self.expect(TokenKind::Name)?;
        self.expect(TokenKind::DashGreaterThan)?;
        let body = self.parse_expr()?;

        let span = TextSpan::between(fun.span, body.2.data);

        Ok((
            Lambda {
                param: param.text.to_owned(),
                body
            },
            span
        ))
    }

    fn parse_if_else_expr(&mut self) -> ParseResult<(IfElse<Parse>, TextSpan)> {
        let r#if = self.expect(TokenKind::If)?;
        let condition = self.parse_expr()?;
        self.expect(TokenKind::Then)?;
        let if_true = self.parse_expr()?;
        self.expect(TokenKind::Else)?;
        let if_false = self.parse_expr()?;

        let span = TextSpan::between(r#if.span, if_false.2.data);

        Ok((
            IfElse {
                condition,
                if_true,
                if_false
            },
            span
        ))
    }
}

/// Parses a string into an AST.
pub fn parse(source: &str) -> Result<Ast<Parse>, ParseError> {
    let lexed = lex(source)?;
    // dbg!(&lexed);
    let mut parser = Parser::new(&lexed.tokens, lexed.eoi);
    let root = parser.parse_root()?;

    Ok(Ast::new(root, (), ()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn foo() {
        let x = parse("let foo = fun f -> f 1 2 3");

        dbg!(&x);
    }
}
