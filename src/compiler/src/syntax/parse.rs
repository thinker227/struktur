//! Main parser implementation.

use crate::{
    diagnostic::{Category, Code, Diagnostic, ReportBuilder},
    sources::Source,
    syntax::{SyntaxErrorCode, SyntaxNode, lex::Tokens},
    text::{Spanned as _, TextSpan},
};

use super::{NodeBuilder, NodeId, Nodes, SyntaxKind, Token, TokenKind};

mod errors;

type Result<T = NodeId, E = Diagnostic> = std::result::Result<T, E>;

/// Parses a sequence of tokens into an AST.
pub fn parse(map: &mut Nodes, tokens: Tokens) -> Result {
    let mut parser = Parser::new(
        tokens.source,
        TokenStream::new(&tokens.tokens, tokens.eoi),
        map,
    );
    parser.parse_root()
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

impl ExprContext {
    pub const ALL: Self = Self {
        allow_keyword: true,
        allow_tyann: true,
    };
}

/// The context in which an atom pattern is parsed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PatternContext {
    /// Whether type annotation patterns are allowed.
    /// Needed specifically in order to disallow the ambiguous syntax `fun x : Int -> y`
    /// (which could be parsed as either `fun (x : Int) -> y` or `fun x : (Int -> y)`).
    allow_tyann: bool,
}

/// A parsed expression.
#[derive(Debug, Clone)]
struct ParsedExpr {
    /// The expression node.
    expr: NodeId,
    /// Whether the expression is considered 'complex'
    /// and may therefore not be the direct target of a type annotation.
    complex: bool,
}

/// Helper for managing the stream of tokens.
struct TokenStream<'tokens> {
    tokens: &'tokens [Token],
    eoi: Token,
    index: usize,
}

impl<'tokens> TokenStream<'tokens> {
    pub fn new(tokens: &'tokens [Token], eoi: Token) -> Self {
        Self {
            tokens,
            eoi,
            index: 0,
        }
    }

    pub fn current(&mut self) -> Token {
        self.tokens.get(self.index).copied().unwrap_or(self.eoi)
    }

    pub fn advance(&mut self) -> Token {
        let token = self.current();
        self.index += 1;
        token
    }

    pub fn expect_optional(&mut self, kind: TokenKind) -> Option<Token> {
        let token = self.current();
        if token.kind == kind {
            self.advance();
            Some(token)
        } else {
            None
        }
    }
}

struct Parser<'a> {
    source: &'a Source,
    tokens: TokenStream<'a>,
    map: &'a mut Nodes,
}

impl<'a> Parser<'a> {
    pub fn new(source: &'a Source, tokens: TokenStream<'a>, map: &'a mut Nodes) -> Self {
        Self {
            source,
            tokens,
            map,
        }
    }

    fn node(&mut self, kind: SyntaxKind, build: impl FnOnce(&mut NodeBuilder)) -> NodeId {
        let mut builder = NodeBuilder::new(kind);
        build(&mut builder);
        let node = builder.finish_raw();
        self.map.insert(node, self.source.key())
    }

    fn error(
        &self,
        code: SyntaxErrorCode,
        span: TextSpan,
        build: impl FnOnce(ReportBuilder) -> ReportBuilder,
    ) -> Diagnostic {
        let code = Code::new(Category::Parse, code.into());
        let location = span.with_context(self.source.key());
        Diagnostic::error(code, location, build)
    }

    pub fn expect(&mut self, kind: TokenKind) -> Result<Token> {
        let current = self.tokens.current();
        if current.kind == kind {
            Ok(self.tokens.advance())
        } else {
            Err(self.error_unexpected_token(current.span, current.kind, kind))
        }
    }

    pub fn slice(&self, span: TextSpan) -> &'a str {
        &self.source.text().text()[span]
    }
}

impl Parser<'_> {
    pub fn parse_root(&mut self) -> Result {
        let mut items = Vec::new();

        while self.tokens.current().kind != TokenKind::EndOfInput {
            let item = self.parse_item()?;
            items.push(item);

            if self.tokens.current().kind == TokenKind::EndOfInput {
                break;
            }
        }

        let eoi = self.tokens.advance();

        Ok(self.node(SyntaxKind::Root, |b| {
            b.add_nodes(items);
            b.add_token(eoi);
        }))
    }

    fn parse_ident(&mut self) -> Result {
        let ident = self.expect(TokenKind::Ident)?;

        Ok(self.node(SyntaxKind::Ident, |b| {
            b.add_token(ident);
        }))
    }

    fn parse_item(&mut self) -> Result {
        self.try_parse_item()?.ok_or_else(|| {
            let current = self.tokens.current();
            self.error_unexpected_token(current.span, current.kind, "item")
        })
    }

    fn try_parse_item(&mut self) -> Result<Option<NodeId>> {
        let item = match self.tokens.current().kind {
            TokenKind::Let => self.parse_binding()?,
            _ => return Ok(None),
        };

        Ok(Some(item))
    }

    fn parse_binding(&mut self) -> Result {
        let r#let = self.expect(TokenKind::Let)?;
        let name = self.parse_ident()?;

        let ty = self.try_parse_type_ann()?;

        let equals = self.expect(TokenKind::Equals)?;
        let body = self.parse_expr(ExprContext::ALL)?.expr;

        Ok(self.node(SyntaxKind::Binding, |b| {
            b.add_token(r#let);
            b.add_node(name);
            b.try_add_node(ty);
            b.add_token(equals);
            b.add_node(body);
        }))
    }

    fn parse_expr(&mut self, ctx: ExprContext) -> Result<ParsedExpr> {
        self.parse_tyann_expr(ctx)
    }

    fn parse_tyann_expr(&mut self, ctx: ExprContext) -> Result<ParsedExpr> {
        let ParsedExpr {
            mut expr,
            mut complex,
        } = self.parse_application_expr()?;

        if ctx.allow_tyann {
            // Type annotations are not allowed to be chained, but we nonetheless parse them in a loop
            // just so that `x : Int : Int` will have a nicer error message.
            while let Some(ty) = self.try_parse_type_ann()? {
                if !complex {
                    expr = self.node(SyntaxKind::TyAnnExpr, |b| {
                        b.add_node(expr);
                        b.add_node(ty);
                    });
                    complex = true;
                } else {
                    let expr = SyntaxNode::new(self.map, expr);
                    let ty = SyntaxNode::new(self.map, ty);
                    let expr_span = expr.span();
                    let full_span = TextSpan::between(expr_span, ty.span());
                    return Err(self.error_ty_ann_not_allowed(expr_span, full_span, "expression"));
                }
            }
        }

        Ok(ParsedExpr { expr, complex })
    }

    fn parse_application_expr(&mut self) -> Result<ParsedExpr> {
        let ParsedExpr {
            expr: mut result,
            mut complex,
        } = self.parse_atom_expr(ExprContext::ALL)?;

        while let Some(ParsedExpr { expr, .. }) = self.try_parse_atom_expr(ExprContext {
            allow_keyword: false,
            // A type annotation is specficially not allowed here in order to allow
            // `f x : T` to parse as `(f x) : T` instead of `f (x : T)`.
            allow_tyann: false,
        })? {
            result = self.node(SyntaxKind::ApplicationExpr, |b| {
                b.add_node(result);
                b.add_node(expr);
            });

            complex = true;
        }

        Ok(ParsedExpr {
            expr: result,
            complex,
        })
    }

    fn parse_atom_expr(&mut self, ctx: ExprContext) -> Result<ParsedExpr> {
        self.try_parse_atom_expr(ctx)?.ok_or_else(|| {
            let current = self.tokens.current();
            self.error_unexpected_token(current.span, current.kind, "expression")
        })
    }

    fn try_parse_atom_expr(&mut self, ctx: ExprContext) -> Result<Option<ParsedExpr>> {
        let result = match self.tokens.current().kind {
            TokenKind::OpenParen => {
                let open_paren = self.tokens.advance();

                let node =
                    if let Some(close_paren) = self.tokens.expect_optional(TokenKind::CloseParen) {
                        self.node(SyntaxKind::UnitExpr, |b| {
                            b.add_token(open_paren);
                            b.add_token(close_paren);
                        })
                    } else {
                        let expr = self.parse_expr(ExprContext::ALL)?.expr;

                        let close_paren = self.expect(TokenKind::CloseParen)?;

                        self.node(SyntaxKind::GroupingExpr, |b| {
                            b.add_token(open_paren);
                            b.add_node(expr);
                            b.add_token(close_paren);
                        })
                    };

                ParsedExpr {
                    expr: node,
                    complex: false,
                }
            }

            TokenKind::Ident => {
                let ident = self.parse_ident()?;

                ParsedExpr {
                    expr: self.node(SyntaxKind::VarExpr, |b| {
                        b.add_node(ident);
                    }),
                    complex: false,
                }
            }

            TokenKind::Let if ctx.allow_keyword => {
                let r#let = self.parse_let_expr()?;

                ParsedExpr {
                    expr: r#let,
                    complex: true,
                }
            }

            TokenKind::Fun if ctx.allow_keyword => {
                let lambda = self.parse_lambda_expr()?;

                ParsedExpr {
                    expr: lambda,
                    complex: true,
                }
            }

            TokenKind::If if ctx.allow_keyword => {
                let if_else = self.parse_if_else_expr()?;

                ParsedExpr {
                    expr: if_else,
                    complex: true,
                }
            }

            _ => return Ok(self.try_parse_single_token_atom_expr()),
        };

        Ok(Some(result))
    }

    fn try_parse_single_token_atom_expr(&mut self) -> Option<ParsedExpr> {
        let syntax_kind = match self.tokens.current().kind {
            TokenKind::Number => SyntaxKind::IntExpr,
            TokenKind::True | TokenKind::False => SyntaxKind::BoolExpr,
            TokenKind::String => SyntaxKind::StringExpr,
            _ => return None,
        };

        let token = self.tokens.advance();

        let expr = self.node(syntax_kind, |b| {
            b.add_token(token);
        });

        Some(ParsedExpr {
            expr,
            complex: false,
        })
    }

    fn parse_let_expr(&mut self) -> Result {
        let r#let = self.expect(TokenKind::Let)?;

        let pattern = self.parse_pattern(PatternContext { allow_tyann: true })?;

        let equals = self.expect(TokenKind::Equals)?;

        let value = self.parse_expr(ExprContext::ALL)?.expr;

        let r#in = self.expect(TokenKind::In)?;

        let subexpr = self.parse_expr(ExprContext::ALL)?.expr;

        Ok(self.node(SyntaxKind::LetExpr, |b| {
            b.add_token(r#let);
            b.add_node(pattern);
            b.add_token(equals);
            b.add_node(value);
            b.add_token(r#in);
            b.add_node(subexpr);
        }))
    }

    fn parse_if_else_expr(&mut self) -> Result {
        let r#if = self.expect(TokenKind::If)?;

        let condition = self
            .parse_expr(ExprContext {
                allow_keyword: false,
                allow_tyann: true,
            })?
            .expr;

        let then = self.expect(TokenKind::Then)?;

        let if_true = self.parse_expr(ExprContext::ALL)?.expr;

        let r#else = self.expect(TokenKind::Else)?;

        let if_false = self.parse_expr(ExprContext::ALL)?.expr;

        Ok(self.node(SyntaxKind::IfElseExpr, |b| {
            b.add_token(r#if);
            b.add_node(condition);
            b.add_token(then);
            b.add_node(if_true);
            b.add_token(r#else);
            b.add_node(if_false);
        }))
    }

    fn parse_lambda_expr(&mut self) -> Result {
        let fun = self.expect(TokenKind::Fun)?;

        let mut cases = Vec::new();

        {
            let bar = self.tokens.expect_optional(TokenKind::Bar);
            let case = self.parse_case()?;

            cases.push(self.node(SyntaxKind::LambdaExprStructuring, |b| {
                b.try_add_token(bar);
                b.add_node(case);
            }));
        }

        while self.tokens.current().kind == TokenKind::Bar {
            let bar = self.tokens.advance();
            let case = self.parse_case()?;

            cases.push(self.node(SyntaxKind::LambdaExprStructuring, |b| {
                b.add_token(bar);
                b.add_node(case);
            }));
        }

        Ok(self.node(SyntaxKind::LambdaExpr, |b| {
            b.add_token(fun);
            b.add_nodes(cases);
        }))
    }

    fn parse_case(&mut self) -> Result {
        let pattern = self.parse_pattern(PatternContext { allow_tyann: false })?;

        let arrow = self.expect(TokenKind::DashGreaterThan)?;

        let body = self.parse_expr(ExprContext::ALL)?.expr;

        Ok(self.node(SyntaxKind::Case, |b| {
            b.add_node(pattern);
            b.add_token(arrow);
            b.add_node(body);
        }))
    }

    fn parse_pattern(&mut self, ctx: PatternContext) -> Result {
        self.parse_tyann_pattern(ctx)
    }

    fn parse_tyann_pattern(&mut self, ctx: PatternContext) -> Result {
        let PatternContext { mut allow_tyann } = ctx;

        let mut pattern = self.parse_atom_pattern()?;

        while let Some(ty) = self.try_parse_type_ann()? {
            if allow_tyann {
                pattern = self.node(SyntaxKind::TyAnnPattern, |b| {
                    b.add_node(pattern);
                    b.add_node(ty);
                });

                allow_tyann = false;
            } else {
                let pattern = SyntaxNode::new(self.map, pattern);
                let ty = SyntaxNode::new(self.map, ty);
                let pattern_span = pattern.span();
                let full_span = TextSpan::between(pattern_span, ty.span());
                return Err(self.error_ty_ann_not_allowed(pattern_span, full_span, "pattern"));
            }
        }

        Ok(pattern)
    }

    fn parse_atom_pattern(&mut self) -> Result {
        let pattern = match self.tokens.current().kind {
            TokenKind::OpenParen => {
                let open_paren = self.tokens.advance();

                if let Some(close_paren) = self.tokens.expect_optional(TokenKind::CloseParen) {
                    self.node(SyntaxKind::UnitPattern, |b| {
                        b.add_token(open_paren);
                        b.add_token(close_paren);
                    })
                } else {
                    let pattern = self.parse_pattern(PatternContext { allow_tyann: true })?;

                    let close_paren = self.expect(TokenKind::CloseParen)?;

                    self.node(SyntaxKind::GroupingPattern, |b| {
                        b.add_token(open_paren);
                        b.add_node(pattern);
                        b.add_token(close_paren);
                    })
                }
            }

            TokenKind::Ident => {
                let ident = self.parse_ident()?;

                self.node(SyntaxKind::VarPattern, |b| {
                    b.add_node(ident);
                })
            }

            _ if let Some(pattern) = self.try_parse_single_token_atom_pattern() => pattern,

            _ => {
                let current = self.tokens.current();
                return Err(self.error_unexpected_token(current.span, current.kind, "pattern"));
            }
        };

        Ok(pattern)
    }

    fn try_parse_single_token_atom_pattern(&mut self) -> Option<NodeId> {
        let syntax_kind = match self.tokens.current().kind {
            TokenKind::Underscore => SyntaxKind::WildcardPattern,
            TokenKind::Number => SyntaxKind::IntPattern,
            TokenKind::True | TokenKind::False => SyntaxKind::BoolPattern,
            _ => return None,
        };

        let token = self.tokens.advance();

        let pattern = self.node(syntax_kind, |b| {
            b.add_token(token);
        });

        Some(pattern)
    }

    fn try_parse_type_ann(&mut self) -> Result<Option<NodeId>> {
        if let Some(colon) = self.tokens.expect_optional(TokenKind::Colon) {
            let ty = self.parse_tyexpr()?;

            Ok(Some(self.node(SyntaxKind::TyAnn, |b| {
                b.add_token(colon);
                b.add_node(ty);
            })))
        } else {
            Ok(None)
        }
    }

    fn parse_tyexpr(&mut self) -> Result {
        self.parse_function_tyexpr()
    }

    fn parse_function_tyexpr(&mut self) -> Result {
        let ty = self.parse_atom_tyexpr()?;

        if let Some(arrow) = self.tokens.expect_optional(TokenKind::DashGreaterThan) {
            let ret = self.parse_tyexpr()?;

            Ok(self.node(SyntaxKind::FunctionTyExpr, |b| {
                b.add_node(ty);
                b.add_token(arrow);
                b.add_node(ret);
            }))
        } else {
            Ok(ty)
        }
    }

    fn parse_atom_tyexpr(&mut self) -> Result {
        self.try_parse_atom_tyexpr()?.ok_or_else(|| {
            let current = self.tokens.current();
            self.error_unexpected_token(current.span, current.kind, "type")
        })
    }

    fn try_parse_atom_tyexpr(&mut self) -> Result<Option<NodeId>> {
        let expr = match self.tokens.current().kind {
            TokenKind::OpenParen => {
                let open_paren = self.tokens.advance();

                if let Some(close_paren) = self.tokens.expect_optional(TokenKind::CloseParen) {
                    self.node(SyntaxKind::UnitTyExpr, |b| {
                        b.add_token(open_paren);
                        b.add_token(close_paren);
                    })
                } else {
                    let ty = self.parse_tyexpr()?;

                    let close_paren = self.expect(TokenKind::CloseParen)?;

                    self.node(SyntaxKind::GroupingTyExpr, |b| {
                        b.add_token(open_paren);
                        b.add_node(ty);
                        b.add_token(close_paren);
                    })
                }
            }

            TokenKind::Ident => {
                let ident = self.tokens.advance();

                let span = ident.span;
                let text = self.slice(span);

                let syntax_kind = match text {
                    "Int" => SyntaxKind::IntTyExpr,
                    "Bool" => SyntaxKind::BoolTyExpr,
                    "String" => SyntaxKind::StringTyExpr,

                    _ => return Err(self.error_unknown_type(span, text)),
                };

                self.node(syntax_kind, |b| {
                    b.add_token(ident);
                })
            }

            TokenKind::TypeVar => {
                let var = self.tokens.advance();

                self.node(SyntaxKind::VarTyExpr, |b| {
                    b.add_token(var);
                })
            }

            TokenKind::Forall => self.parse_forall_tyexpr()?,

            _ => return Ok(None),
        };

        Ok(Some(expr))
    }

    fn parse_forall_tyexpr(&mut self) -> Result {
        let forall = self.tokens.advance();

        let mut vars = Vec::new();

        while let Some(var) = self.tokens.expect_optional(TokenKind::TypeVar) {
            vars.push(self.node(SyntaxKind::VarTyExpr, |b| {
                b.add_token(var);
            }));
        }

        let dot = match self.tokens.expect_optional(TokenKind::Dot) {
            Some(dot) => dot,
            None => {
                let current = self.tokens.current();
                return Err(self.error_unexpected_token(
                    current.span,
                    current.kind,
                    "type variable name or `.`",
                ));
            }
        };

        if vars.is_empty() {
            return Err(self.error_empty_forall(TextSpan::between(forall.span, dot.span)));
        }

        let subty = self.parse_tyexpr()?;

        let structuring = self.node(SyntaxKind::ForallTyExprStructuring, |b| {
            b.add_nodes(vars);
        });

        Ok(self.node(SyntaxKind::ForallTyExpr, |b| {
            b.add_token(forall);
            b.add_node(structuring);
            b.add_token(dot);
            b.add_node(subty);
        }))
    }
}

#[cfg(test)]
mod tests {
    use insta::assert_yaml_snapshot;

    use crate::{
        sources::{SourceName, SourceProject},
        syntax::{lex::lex, nodes::Root},
    };

    use super::*;

    fn test_parse<'map>(map: &'map mut Nodes, text: &str) -> Result<Root<'map>> {
        let mut sources = SourceProject::new();
        let source = sources.add(
            SourceName::InMemory {
                name: "test".to_owned(),
            },
            text.to_owned(),
        );

        let tokens = lex(source)?;
        let node_id = parse(map, tokens)?;

        let node = SyntaxNode::new(map, node_id);
        let root = Root::new(node).unwrap();

        Ok(root)
    }

    #[test]
    fn simple_let_expr() {
        let mut map = Nodes::new();

        let text = "let x = 0";
        let root = test_parse(&mut map, text).unwrap().raw();

        assert_yaml_snapshot!(root);
    }

    #[test]
    fn simple_unexpected_token() {
        let mut map = Nodes::new();

        let diagnostic = test_parse(&mut map, "let.").unwrap_err();

        assert_eq!(
            diagnostic.code(),
            Code::parse(SyntaxErrorCode::UnexpectedToken.into())
        );
        assert_eq!(diagnostic.location().span, TextSpan::new(3, 1));
    }

    #[test]
    fn empty_forall() {
        let mut map = Nodes::new();

        let text = "let x: forall. () = ()";
        let diagnostic = test_parse(&mut map, text).unwrap_err();

        assert_eq!(
            diagnostic.code(),
            Code::parse(SyntaxErrorCode::EmptyForall.into())
        );
        assert_eq!(diagnostic.location().span, TextSpan::new(7, 7));
    }

    #[test]
    fn unknown_type() {
        let mut map = Nodes::new();

        let text = "let x: uwu = 0";
        let diagnostic = test_parse(&mut map, text).unwrap_err();

        assert_eq!(
            diagnostic.code(),
            Code::parse(SyntaxErrorCode::UnknownType.into())
        );
        assert_eq!(diagnostic.location().span, TextSpan::new(7, 3));
    }
}
