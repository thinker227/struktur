// Prevent warnings about Miette diagnostic fields never being read.
// See https://github.com/rust-lang/rust/issues/147648
#![allow(unused_assignments)]

//! Lexing and parsing source code into an initial AST.

mod lex;

use std::{fmt::Display, rc::Rc};

use crate::{ast::*, id::IdProvider, stage::Parse, text_span::TextSpan};
use self::lex::{Token, TokenKind, lex};

#[derive(Debug, Clone, PartialEq, thiserror::Error, miette::Diagnostic)]
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

    #[error("Expected name after `'`")]
    MalformedTypeVarName {
        #[label]
        tick_span: TextSpan,
    },

    #[error("Found {found} token, expected {expected}")]
    UnexpectedToken {
        #[label]
        span: TextSpan,
        found: TokenKind,
        expected: String,
    },

    #[error("Type annotation has to be enclosed in parentheses")]
    TyAnnNotAllowed {
        #[label("Assuming you intended to annotate this {kind}")]
        target_span: TextSpan,
        #[label("Enclose this in parentheses")]
        full_span: TextSpan,
        kind: String,
    },

    #[error("Empty forall quantifier")]
    EmptyForall {
        #[label]
        span: TextSpan,
    },

    #[error("Unknown type `{name}`")]
    UnknownType {
        #[label]
        span: TextSpan,
        name: String,
    }
}

impl Default for ParseError {
    fn default() -> Self {
        // There is no "default" for parse errors, but Logos requires this impl.
        unimplemented!()
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

/// The context in which an expression is parsed.
///
/// For expressions starting with a keyword (such as `fun` in lambda expressions,
/// `if` in if-else expressions, and *especially* `let` in let-expressions),
/// this is used to distinguish whether the expression is allowed to be parsed immediately after
/// another expression, in order to not make syntax like `let x = x let y = y` ambiguous.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ExprContext {
    /// Whether expressions starting with a keyword are allowed.
    /// Needed in order to not permit weird syntax like `f fun x -> y`.
    allow_keyword: bool,
    /// Whether type annotation expressions are allowed.
    allow_tyann: bool,
}

/// The context in which an atom pattern is parsed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PatternContext {
    /// Whether type annotation patterns are allowed.
    /// Needed specifically in order to not allow the ambiguous syntax `fun x : Int -> y`
    /// (which could be parsed as either `fun (x : Int) -> y` or `fun x : (Int -> y)`).
    allow_tyann: bool,
}

/// A parsed expression.
#[derive(Debug, Clone)]
struct ParsedExpr {
    /// The expression node.
    expr: Expr<Parse>,
    /// Whether the expression is considered 'complex'
    /// and may therefore not be the direct target of a type annotation.
    complex: bool,
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

        Ok(Root {
            data: self.node_data(span),
            items
        })
    }

    fn parse_name(&mut self) -> ParseResult<Name> {
        let name = self.expect(TokenKind::Name)?;

        Ok(Name {
            data: self.node_data(name.span),
            name: name.text.to_owned()
        })
    }

    fn parse_item(&mut self) -> ParseResult<Item<Parse>> {
        self.try_parse_item()?.ok_or_else(|| {
            let current = self.current();
            ParseError::unexpected_token(current.span, current.kind, "item")
        })
    }

    fn try_parse_item(&mut self) -> Result<Option<Item<Parse>>, ParseError> {
        let item = match self.current().kind {
            TokenKind::Let => {
                let binding = self.parse_binding()?;
                Item::Binding(binding)
            }

            _ => return Ok(None)
        };

        Ok(Some(item))
    }

    fn parse_binding(&mut self) -> ParseResult<Binding<Parse>> {
        let r#let = self.expect(TokenKind::Let)?;
        let name = self.parse_name()?;

        let ty = self.try_parse_type_ann()?;

        self.expect(TokenKind::Equals)?;
        let body = self.parse_expr(ExprContext {
            allow_keyword: true,
            allow_tyann: true
        })?.expr;

        let span = TextSpan::between(r#let.span, body.span());

        Ok(Binding {
            data: self.node_data(span),
            symbol: name,
            ty,
            body
        })
    }

    fn parse_expr(&mut self, ctx: ExprContext) -> ParseResult<ParsedExpr> {
        self.parse_tyann_expr(ctx)
    }

    fn parse_tyann_expr(&mut self, ctx: ExprContext) -> ParseResult<ParsedExpr> {
        let ParsedExpr { mut expr, mut complex } = self.parse_application_expr()?;

        if ctx.allow_tyann {
            // Type annotations are not allowed to be chained, but we nonetheless parse them in a loop
            // just so that `x : Int : Int` will have a nicer error message.
            while let Some(ty) = self.try_parse_type_ann()? {
                let span = TextSpan::between(expr.span(), ty.span());

                if !complex {
                    expr = Expr::TyAnn(Box::new(TyAnnExpr {
                        data: self.node_data(span),
                        expr,
                        ty
                    }));
                    complex = true;
                } else {
                    return Err(ParseError::TyAnnNotAllowed {
                        target_span: expr.span(),
                        full_span: span,
                        kind: "expression".to_owned()
                    });
                };
            }
        }

        Ok(ParsedExpr { expr, complex })
    }

    fn parse_application_expr(&mut self) -> ParseResult<ParsedExpr> {
        let ParsedExpr { expr: mut result, mut complex } = self.parse_atom_expr(ExprContext {
            allow_keyword: true,
            allow_tyann: true
        })?;

        while let Some(ParsedExpr { expr, .. }) = self.try_parse_atom_expr(ExprContext {
            allow_keyword: false,
            // A type annotation is specficially not allowed here in order to allow
            // `f x : T` to parse as `(f x) : T` instead of `f (x : T)`.
            allow_tyann: false
        })? {
            let span = TextSpan::between(result.span(), expr.span());

            result = Expr::Apply(Box::new(Application {
                data: self.expr_data(span),
                target: result,
                arg: expr
            }));

            complex = false;
        }

        Ok(ParsedExpr { expr: result, complex })
    }

    fn parse_atom_expr(&mut self, ctx: ExprContext) -> ParseResult<ParsedExpr> {
        self.try_parse_atom_expr(ctx)?.ok_or_else(|| {
            let current = self.current();
            ParseError::unexpected_token(current.span, current.kind, "expression")
        })
    }

    fn try_parse_atom_expr(&mut self, ctx: ExprContext) -> Result<Option<ParsedExpr>, ParseError> {
        let result = match self.current().kind {
            TokenKind::OpenParen => {
                let open_paren = self.advance();

                if self.current().kind == TokenKind::CloseParen {
                    let close_paren = self.advance();
                    let span = TextSpan::between(open_paren.span, close_paren.span);

                    ParsedExpr {
                        expr: Expr::Unit(UnitExpr {
                            data: self.expr_data(span)
                        }),
                        complex: false
                    }
                } else {
                    let expr = self.parse_expr(ExprContext {
                        allow_keyword: true,
                        allow_tyann: true
                    })?.expr;
                    self.expect(TokenKind::CloseParen)?;
                    return Ok(Some(ParsedExpr { expr, complex: false }));
                }
            }

            TokenKind::Number => {
                let number = self.advance();
                let val = number.text.parse().unwrap();

                ParsedExpr {
                    expr: Expr::Int(IntExpr {
                        data: self.expr_data(number.span),
                        val
                    }),
                    complex: false
                }
            }

            TokenKind::True | TokenKind::False => {
                let bool = self.advance();
                let val = bool.kind == TokenKind::True;

                ParsedExpr {
                    expr: Expr::Bool(BoolExpr {
                        data: self.expr_data(bool.span),
                        val
                    }),
                    complex: false
                }
            }

            TokenKind::String => {
                let str = self.advance();
                let text = str.text;
                let val = text[1 .. text.len() - 1].to_owned();

                ParsedExpr {
                    expr: Expr::String(StringExpr {
                        data: self.expr_data(str.span),
                        val
                    }),
                    complex: false
                }
            }

            TokenKind::Name => {
                let name = self.advance();
                let var = name.text.to_owned();

                ParsedExpr {
                    expr: Expr::Var(VarExpr {
                        data: self.expr_data(name.span),
                        symbol: var
                    }),
                    complex: false
                }
            }

            TokenKind::Let if ctx.allow_keyword => {
                let r#let = self.parse_let_expr()?;
                ParsedExpr {
                    expr: Expr::Bind(Box::new(r#let)),
                    complex: true
                }
            }

            TokenKind::Fun if ctx.allow_keyword => {
                let lambda = self.parse_lambda_expr()?;
                ParsedExpr {
                    expr: Expr::Lambda(Box::new(lambda)),
                    complex: true
                }
            }

            TokenKind::If if ctx.allow_keyword => {
                let if_else = self.parse_if_else_expr()?;
                ParsedExpr {
                    expr: Expr::If(Box::new(if_else)),
                    complex: true
                }
            }

            _ => return Ok(None)
        };

        Ok(Some(result))
    }

    fn parse_let_expr(&mut self) -> ParseResult<Let<Parse>> {
        let r#let = self.expect(TokenKind::Let)?;

        let pattern = self.parse_pattern(PatternContext {
            allow_tyann: true
        })?;

        self.expect(TokenKind::Equals)?;

        let value = self.parse_expr(ExprContext {
            allow_keyword: true,
            allow_tyann: true
        })?.expr;

        self.expect(TokenKind::In)?;

        let expr = self.parse_expr(ExprContext {
            allow_keyword: true,
            allow_tyann: true
        })?.expr;

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

        let condition = self.parse_expr(ExprContext {
            allow_keyword: false,
            allow_tyann: true
        })?.expr;

        self.expect(TokenKind::Then)?;

        let if_true = self.parse_expr(ExprContext {
            allow_keyword: true,
            allow_tyann: true
        })?.expr;

        self.expect(TokenKind::Else)?;

        let if_false = self.parse_expr(ExprContext {
            allow_keyword: true,
            allow_tyann: true
        })?.expr;

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
        let pattern = self.parse_pattern(PatternContext {
            allow_tyann: false
        })?;
        self.expect(TokenKind::DashGreaterThan)?;
        let body = self.parse_expr(ExprContext {
            allow_keyword: true,
            allow_tyann: true
        })?.expr;

        let span = TextSpan::between(pattern.span(), body.span());

        Ok(Case {
            pattern,
            body,
            data: self.node_data(span)
        })
    }

    fn parse_pattern(&mut self, ctx: PatternContext) -> ParseResult<Pattern<Parse>> {
        self.parse_tyann_pattern(ctx)
    }

    fn parse_tyann_pattern(&mut self, mut ctx: PatternContext) -> ParseResult<Pattern<Parse>> {
        let mut pattern = self.parse_atom_pattern()?;

        while let Some(ty) = self.try_parse_type_ann()? {
            let span = TextSpan::between(pattern.span(), ty.span());

            if ctx.allow_tyann {
                pattern = Pattern::TyAnn(Box::new(TyAnnPattern {
                    data: self.node_data(span),
                    pat: pattern,
                    ty
                }));
                ctx.allow_tyann = false;
            } else {
                return Err(ParseError::TyAnnNotAllowed {
                    target_span: pattern.span(),
                    full_span: span,
                    kind: "pattern".to_owned()
                });
            }
        }

        Ok(pattern)
    }

    fn parse_atom_pattern(&mut self) -> ParseResult<Pattern<Parse>> {
        let pattern = match self.current().kind {
            TokenKind::Underscore => {
                let underscore = self.advance();
                Pattern::Wildcard(WildcardPattern {
                    data: self.node_data(underscore.span)
                })
            }

            TokenKind::Name => {
                let name = self.advance();
                Pattern::Var(VarPattern {
                    data: self.node_data(name.span),
                    symbol: name.text.to_owned()
                })
            }

            TokenKind::OpenParen => {
                let open_paren = self.advance();

                if let Some(close_paren) = self.advance_if(TokenKind::CloseParen) {
                    let span = TextSpan::between(open_paren.span, close_paren.span);
                    Pattern::Unit(UnitPattern {
                        data: self.node_data(span)
                    })
                } else {
                    let pattern = self.parse_pattern(PatternContext {
                        allow_tyann: true
                    })?;
                    self.expect(TokenKind::CloseParen)?;
                    pattern
                }
            }

            TokenKind::Number => {
                let number = self.advance();
                let val = number.text.parse().unwrap();
                Pattern::Number(NumberPattern {
                    data: self.node_data(number.span),
                    val
                })
            }

            TokenKind::True | TokenKind::False => {
                let bool = self.advance();
                let val = bool.kind == TokenKind::True;
                Pattern::Bool(BoolPattern {
                    data: self.node_data(bool.span),
                    val
                })
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

    fn try_parse_type_ann(&mut self) -> ParseResult<Option<TyExpr<Parse>>> {
        if self.advance_if(TokenKind::Colon).is_some() {
            let ty = self.parse_tyexpr()?;
            Ok(Some(ty))
        } else {
            Ok(None)
        }
    }

    fn parse_tyexpr(&mut self) -> ParseResult<TyExpr<Parse>> {
        self.parse_function_tyexpr()
    }

    fn parse_function_tyexpr(&mut self) -> ParseResult<TyExpr<Parse>> {
        let ty = self.parse_atom_tyexpr()?;

        if self.advance_if(TokenKind::DashGreaterThan).is_some() {
            let ret = self.parse_tyexpr()?;

            let span = TextSpan::between(ty.span(), ret.span());

            Ok(TyExpr::Function(Box::new(FunctionTyExpr {
                data: self.node_data(span),
                param: ty,
                ret
            })))
        } else {
            Ok(ty)
        }
    }

    fn parse_atom_tyexpr(&mut self) -> ParseResult<TyExpr<Parse>> {
        self.try_parse_atom_tyexpr()?.ok_or_else(|| {
            let current = self.current();
            ParseError::unexpected_token(current.span, current.kind, "type")
        })
    }

    fn try_parse_atom_tyexpr(&mut self) -> Result<Option<TyExpr<Parse>>, ParseError> {
        let expr = match self.current().kind {
            TokenKind::OpenParen => {
                let open_paren = self.advance();

                if self.current().kind == TokenKind::CloseParen {
                    let close_paren = self.advance();
                    let span = TextSpan::between(open_paren.span, close_paren.span);
                    TyExpr::Unit(UnitTyExpr {
                        data: self.node_data(span)
                    })
                } else {
                    let ty = self.parse_tyexpr()?;
                    self.expect(TokenKind::CloseParen)?;
                    return Ok(Some(ty));
                }
            }

            TokenKind::Name => {
                let name = self.advance();

                let span = name.span;

                match name.text {
                    "Int" => TyExpr::Int(IntTyExpr {
                        data: self.node_data(span)
                    }),
                    "Bool" => TyExpr::Bool(BoolTyExpr {
                        data: self.node_data(span)
                    }),
                    "String" => TyExpr::String(StringTyExpr {
                        data: self.node_data(span)
                    }),

                    _ => return Err(ParseError::UnknownType {
                        span,
                        name: name.text.to_owned()
                    })
                }
            }

            TokenKind::TypeVarName => {
                let var = self.advance();

                let name = &var.text[1..];

                TyExpr::Var(VarTyExpr {
                    data: self.node_data(var.span),
                    symbol: name.to_owned()
                })
            }

            TokenKind::Forall => {
                let forall = self.advance();

                let mut vars = Vec::new();

                while let Some(var) = self.advance_if(TokenKind::TypeVarName) {
                    vars.push(Name {
                        data: self.node_data(var.span),
                        name: var.text[1..].to_owned()
                    });
                }

                let dot = match self.advance_if(TokenKind::Dot) {
                    Some(dot) => dot,
                    None => {
                        let current = self.current();
                        return Err(ParseError::UnexpectedToken {
                            span: current.span,
                            found: current.kind,
                            expected: "type variable name or `.`".to_owned()
                        });
                    }
                };

                if vars.is_empty() {
                    return Err(ParseError::EmptyForall {
                        span: TextSpan::between(forall.span, dot.span)
                    });
                }

                let inner = self.parse_tyexpr()?;

                let span = TextSpan::between(forall.span, inner.span());

                TyExpr::Forall(Box::new(ForallTyExpr {
                    data: self.node_data(span),
                    vars,
                    ty: inner
                }))
            }

            _ => return Ok(None)
        };

        Ok(Some(expr))
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
