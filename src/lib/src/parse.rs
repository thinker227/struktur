// Prevent warnings about Miette diagnostic fields never being read.
// See https://github.com/rust-lang/rust/issues/147648
#![allow(unused_assignments)]

//! Lexing and parsing source code into an initial AST.

mod lex;

use std::{fmt::Display, rc::Rc};

use crate::{ast::*, id::IdProvider, maybe_result::MaybeResult, stage::Parse, text_span::TextSpan};
use self::lex::{Token, TokenKind, lex};

#[derive(Debug, Clone, thiserror::Error, miette::Diagnostic)]
pub enum ParseError {
    #[error("Unknown character")]
    UnknownCharacter {
        #[label]
        char_span: TextSpan,
    },

    #[error("Unterminated string literal")]
    UnterminatedString {
        #[label]
        string_span: TextSpan,
    },

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

    fn node_data(&self, span: TextSpan) -> NodeData {
        NodeData {
            id: self.id_provider.next(),
            span
        }
    }

    fn expr_data(&self, span: TextSpan) -> ExprData<Parse> {
        ExprData {
            node: self.node_data(span),
            expr: ()
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

    fn advance_if(&mut self, kind: TokenKind) -> Option<Token<'src>> {
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
            Some(item) => TextSpan::between(item.span(), eoi.span),
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
        let item = match self.current().kind {
            TokenKind::Let => {
                let binding = self.parse_binding()?;
                Item::Binding(binding)
            }

            _ => return MaybeResult::None
        };

        MaybeResult::Ok(item)
    }

    fn parse_binding(&mut self) -> ParseResult<Binding<Parse>> {
        let r#let = self.expect(TokenKind::Let)?;
        let name = self.expect(TokenKind::Name)?;
        self.expect(TokenKind::Equals)?;
        let body = self.parse_expr()?;

        let span = TextSpan::between(r#let.span, body.span());

        Ok(Binding {
            data: self.node_data(span),
            symbol: name.text.to_owned(),
            body
        })
    }

    fn parse_expr(&mut self) -> ParseResult<Expr<Parse>> {
        self.parse_application_expr()
    }

    fn parse_application_expr(&mut self) -> ParseResult<Expr<Parse>> {
        let mut result = self.parse_atom_expr(ExprContext::Normal)?;

        while let Some(expr) = self.try_parse_atom_expr(ExprContext::Trailing).into_option() {
            let expr = expr?;

            let span = TextSpan::between(result.span(), expr.span());

            result = Expr::Apply(Box::new(Application {
                data: self.expr_data(span),
                target: result,
                arg: expr
            }));
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
        let expr = match self.current().kind {
            TokenKind::OpenParen => {
                let open_paren = self.advance();

                if self.current().kind == TokenKind::CloseParen {
                    let close_paren = self.advance();
                    let span = TextSpan::between(open_paren.span, close_paren.span);
                    Expr::Unit(self.expr_data(span))
                } else {
                    let expr = self.parse_expr()?;
                    self.expect(TokenKind::CloseParen)?;
                    return MaybeResult::Ok(expr);
                }
            }

            TokenKind::Number => {
                let number = self.advance();
                let val = number.text.parse().unwrap();
                Expr::Int(self.expr_data(number.span), val)
            }

            TokenKind::True | TokenKind::False => {
                let bool = self.advance();
                let val = bool.kind == TokenKind::True;
                Expr::Bool(self.expr_data(bool.span), val)
            }

            TokenKind::String => {
                let str = self.advance();
                let text = str.text;
                let val = text[1 .. text.len() - 1].to_owned();
                Expr::String(self.expr_data(str.span), val)
            }

            TokenKind::Name => {
                let name = self.advance();
                let var = name.text.to_owned();
                Expr::Var(self.expr_data(name.span), var)
            }

            TokenKind::Let if ctx == ExprContext::Normal => {
                let r#let = self.parse_let_expr()?;
                Expr::Bind(Box::new(r#let))
            }

            TokenKind::Fun if ctx == ExprContext::Normal => {
                let lambda = self.parse_lambda_expr()?;
                Expr::Lambda(Box::new(lambda))
            }

            TokenKind::If if ctx == ExprContext::Normal => {
                let if_else = self.parse_if_else_expr()?;
                Expr::If(Box::new(if_else))
            }

            _ => return MaybeResult::None
        };

        MaybeResult::Ok(expr)
    }

    fn parse_let_expr(&mut self) -> ParseResult<Let<Parse>> {
        let r#let = self.expect(TokenKind::Let)?;
        let pattern = self.parse_pattern()?;
        self.expect(TokenKind::Equals)?;
        let value = self.parse_expr()?;
        self.expect(TokenKind::In)?;
        let expr = self.parse_expr()?;

        let span = TextSpan::between(r#let.span, expr.span());

        Ok(Let {
            data: self.expr_data(span),
            pattern,
            value,
            expr
        })
    }

    fn parse_if_else_expr(&mut self) -> ParseResult<IfElse<Parse>> {
        let r#if = self.expect(TokenKind::If)?;
        let condition = self.parse_expr()?;
        self.expect(TokenKind::Then)?;
        let if_true = self.parse_expr()?;
        self.expect(TokenKind::Else)?;
        let if_false = self.parse_expr()?;

        let span = TextSpan::between(r#if.span, if_false.span());

        Ok(IfElse {
            data: self.expr_data(span),
            condition,
            if_true,
            if_false
        })
    }

    fn parse_lambda_expr(&mut self) -> ParseResult<Lambda<Parse>> {
        let fun = self.expect(TokenKind::Fun)?;

        self.advance_if(TokenKind::Bar);
        let mut cases = vec![self.parse_case()?];

        while self.current().kind == TokenKind::Bar {
            self.advance();
            let case = self.parse_case()?;
            cases.push(case);
        }

        let span = TextSpan::between(fun.span, cases.last().unwrap().body.span());

        Ok(Lambda {
            data: self.expr_data(span),
            cases
        })
    }

    fn parse_case(&mut self) -> ParseResult<Case<Parse>> {
        let pattern = self.parse_pattern()?;
        self.expect(TokenKind::DashGreaterThan)?;
        let body = self.parse_expr()?;

        let span = TextSpan::between(pattern.span(), body.span());

        Ok(Case {
            pattern,
            body,
            data: self.node_data(span)
        })
    }

    fn parse_pattern(&mut self) -> ParseResult<Pattern<Parse>> {
        let pattern = match self.current().kind {
            TokenKind::Underscore => {
                let underscore = self.advance();
                Pattern::Wildcard(self.node_data(underscore.span))
            }

            TokenKind::Name => {
                let name = self.advance();
                Pattern::Var(self.node_data(name.span), name.text.to_owned())
            }

            TokenKind::OpenParen => {
                let open_paren = self.advance();

                if let Some(close_paren) = self.advance_if(TokenKind::CloseParen) {
                    let span = TextSpan::between(open_paren.span, close_paren.span);
                    Pattern::Unit(self.node_data(span))
                } else {
                    let pattern = self.parse_pattern()?;
                    self.expect(TokenKind::CloseParen)?;
                    return Ok(pattern);
                }
            }

            TokenKind::Number => {
                let number = self.advance();
                let val = number.text.parse().unwrap();
                Pattern::Number(self.node_data(number.span), val)
            }

            TokenKind::True | TokenKind::False => {
                let bool = self.advance();
                let val = bool.kind == TokenKind::True;
                Pattern::Bool(self.node_data(bool.span), val)
            }

            _ => {
                let current = self.current();
                return Err(ParseError::unexpected_token(
                    current.span,
                    current.kind,
                    "pattern"
                ))
            }
        };

        Ok(pattern)
    }
}

/// Parses a string into an AST.
pub fn parse(source: &str) -> Result<Ast<Parse>, ParseError> {
    let lexed = lex(source)?;
    // dbg!(&lexed);
    let mut parser = Parser::new(&lexed.tokens, lexed.eoi);
    let root = parser.parse_root()?;

    Ok(Ast::new(root, ()))
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
