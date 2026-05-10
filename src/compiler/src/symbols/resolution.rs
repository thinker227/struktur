use std::collections::HashMap;

use ariadne::Label;

use crate::{
    diagnostic::{Category, Code, Diagnostic},
    sources::SourceProject,
    syntax::{
        NodeId,
        nodes::{Binding, Case, Expr, Item, Pattern, Root, TyExpr},
    },
    text::TextLocation,
};

use super::{Declaration, Symbol, Symbols};

type Result<T, E = Diagnostic> = std::result::Result<T, E>;

/// Resolves the symbols of an AST.
pub fn resolve_symbols(symbols: &mut Symbols, sources: &SourceProject, root: Root) -> Result<()> {
    let mut resolver = Resolver::new(symbols, sources);

    // TODO: This eventually needs to manage declarations in multiple modules
    // as well as imports of declarations from those modules.
    // Just visiting the root of a single tree at a time won't work.
    resolver.visit_root(root)?;

    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NameKind {
    Value,
    TypeVar,
}

#[derive(Debug, Default)]
struct Named {
    value: Option<Symbol>,
    type_var: Option<Symbol>,
}

impl Named {
    pub fn select(&self, kind: NameKind) -> Option<Symbol> {
        match kind {
            NameKind::Value => self.value,
            NameKind::TypeVar => self.type_var,
        }
    }

    pub fn select_mut(&mut self, kind: NameKind) -> &mut Option<Symbol> {
        match kind {
            NameKind::Value => &mut self.value,
            NameKind::TypeVar => &mut self.type_var,
        }
    }
}

#[derive(Debug)]
struct Resolver<'a> {
    scopes: Vec<HashMap<String, Named>>,
    symbols: &'a mut Symbols,
    sources: &'a SourceProject,
}

impl<'a> Resolver<'a> {
    pub fn new(symbols: &'a mut Symbols, sources: &'a SourceProject) -> Self {
        Self {
            scopes: vec![HashMap::new()],
            symbols,
            sources,
        }
    }

    fn in_scope<T, E>(&mut self, f: impl FnOnce(&mut Self) -> Result<T, E>) -> Result<T, E> {
        self.scopes.push(HashMap::new());
        let res = f(self);
        self.scopes.pop();

        res
    }

    fn register(
        &mut self,
        name: String,
        decl: Declaration,
        kind: NameKind,
    ) -> Result<Symbol, Symbol> {
        let scope = self
            .scopes
            .last_mut()
            .expect("there should always be at least one scope");

        let named = scope.entry(name.clone()).or_default();
        let spot = named.select_mut(kind);

        match spot {
            Some(symbol) => Err(*symbol),
            None => {
                let symbol = self.symbols.register(name, decl).unwrap().key();
                *spot = Some(symbol);
                Ok(symbol)
            }
        }
    }

    fn bind(&mut self, node: NodeId, symbol: Symbol) -> Result<(), Symbol> {
        self.symbols.bind(node, symbol)
    }

    fn lookup(&self, name: &str, kind: NameKind) -> Option<Symbol> {
        for scope in self.scopes.iter().rev() {
            if let Some(named) = scope.get(name)
                && let Some(symbol) = named.select(kind)
            {
                return Some(symbol);
            }
        }

        None
    }
}

impl Resolver<'_> {
    pub fn visit_root(&mut self, root: Root) -> Result<()> {
        // Forward references
        let mut symbols = Vec::new();
        for item in root.items() {
            let symbol = self.register_item(item)?;
            symbols.push(symbol);
        }

        for item in root.items() {
            self.visit_item(item)?;
        }

        Ok(())
    }

    fn register_item(&mut self, item: Item) -> Result<Symbol> {
        let (name, decl) = match item {
            Item::Binding(binding) => {
                let ident = binding.ident();
                let name = self.sources.lookup(ident.location()).unwrap().to_owned();
                let decl = Declaration {
                    node: binding.id(),
                    location: ident.location(),
                };
                (name, decl)
            }
        };

        self.register(name.clone(), decl, NameKind::Value)
            .map_err(|prev| {
                let prev_span = self.symbols.get(prev).decl().location;
                error_duplicate_declaration(decl.location, &name, prev_span, "binding")
            })
    }

    fn visit_item(&mut self, item: Item) -> Result<()> {
        match item {
            Item::Binding(binding) => self.visit_binding(binding)?,
        }

        Ok(())
    }

    fn visit_binding(&mut self, binding: Binding) -> Result<()> {
        self.in_scope(|this| {
            if let Some(ty_ann) = binding.ty_ann() {
                this.visit_tyexpr(ty_ann.ty())?;
            }

            this.visit_expr(binding.expr())?;

            Ok(())
        })
    }

    fn visit_expr(&mut self, expr: Expr) -> Result<()> {
        match expr {
            Expr::Unit(_) | Expr::Int(_) | Expr::Bool(_) | Expr::String(_) => {}

            Expr::Var(var) => {
                let name = self.sources.lookup(var.ident().location()).unwrap();
                let symbol = self
                    .lookup(name, NameKind::Value)
                    .ok_or_else(|| error_undeclared(var.location(), name, "variable or binding"))?;

                self.bind(var.id(), symbol).unwrap();
            }

            Expr::Let(bind) => {
                self.visit_expr(bind.value())?;

                self.in_scope(|this| {
                    this.visit_pattern(bind.pattern())?;
                    this.visit_expr(bind.subexpr())?;

                    Ok(())
                })?;
            }

            Expr::Lambda(lambda) => {
                for case in lambda.cases() {
                    self.visit_case(case)?;
                }
            }

            Expr::Application(application) => {
                self.visit_expr(application.target())?;
                self.visit_expr(application.arg())?;
            }

            Expr::IfElse(if_else) => {
                self.visit_expr(if_else.condition())?;
                self.visit_expr(if_else.true_branch())?;
                self.visit_expr(if_else.false_branch())?;
            }

            Expr::TyAnn(ty_ann) => {
                self.visit_tyexpr(ty_ann.ty_ann().ty())?;
                self.visit_expr(ty_ann.expr())?;
            }

            Expr::Grouping(grouping) => {
                self.visit_expr(grouping.expr())?;
            }
        }

        Ok(())
    }

    fn visit_case(&mut self, case: Case) -> Result<()> {
        self.in_scope(|this| {
            this.visit_pattern(case.pattern())?;
            this.visit_expr(case.body())?;

            Ok(())
        })
    }

    fn visit_pattern(&mut self, pattern: Pattern) -> Result<()> {
        match pattern {
            Pattern::Wildcard(_) | Pattern::Unit(_) | Pattern::Number(_) | Pattern::Bool(_) => {}

            Pattern::Var(var) => {
                let ident = var.ident();
                let name = self.sources.lookup(ident.location()).unwrap();
                let decl = Declaration {
                    node: var.id(),
                    location: ident.location(),
                };

                self.register(name.to_owned(), decl, NameKind::Value)
                    .map_err(|prev| {
                        let prev_span = self.symbols.get(prev).decl().location;
                        error_duplicate_declaration(decl.location, name, prev_span, "variable")
                    })?;
            }

            Pattern::TyAnn(ann) => {
                self.visit_pattern(ann.pattern())?;
                self.visit_tyexpr(ann.ty_ann().ty())?;
            }

            Pattern::Grouping(grouping) => {
                self.visit_pattern(grouping.pattern())?;
            }
        }

        Ok(())
    }

    fn visit_tyexpr(&mut self, tyexpr: TyExpr) -> Result<()> {
        match tyexpr {
            TyExpr::Unit(_) | TyExpr::Int(_) | TyExpr::Bool(_) | TyExpr::String(_) => {}

            TyExpr::Var(var) => {
                let name = &self.sources.lookup(var.location()).unwrap()[1..];
                let symbol = self
                    .lookup(name, NameKind::TypeVar)
                    .ok_or_else(|| error_undeclared(var.location(), name, "type variable"))?;

                self.bind(var.id(), symbol).unwrap();
            }

            TyExpr::Function(function) => {
                self.visit_tyexpr(function.param())?;
                self.visit_tyexpr(function.ret())?;
            }

            TyExpr::Forall(forall) => {
                self.in_scope(|this| {
                    for var in forall.vars() {
                        let name = &this.sources.lookup(var.location()).unwrap()[1..];
                        let decl = Declaration::from(var.raw());

                        this.register(name.to_owned(), decl, NameKind::TypeVar)
                            .map_err(|prev| {
                                let prev_span = this.symbols.get(prev).decl().location;
                                error_duplicate_declaration(
                                    decl.location,
                                    name,
                                    prev_span,
                                    "type variable",
                                )
                            })?;
                    }

                    this.visit_tyexpr(forall.subty())?;

                    Ok(())
                })?;
            }

            TyExpr::Grouping(grouping) => {
                self.visit_tyexpr(grouping.ty())?;
            }
        }

        Ok(())
    }
}

fn error_duplicate_declaration(
    span: TextLocation,
    name: &str,
    prev_decl_span: TextLocation,
    kind: &str,
) -> Diagnostic {
    let code = Code::new(Category::Resolve, 1);
    Diagnostic::error(code, span, |report| {
        report
            .with_message(format!(
                "A {kind} with the name `{name}` has already been declared in this scope"
            ))
            .with_label(
                Label::new(prev_decl_span)
                    .with_message(format!("`{name}` previously declared here"))
                    .with_order(0),
            )
            .with_label(
                Label::new(span)
                    .with_message(format!("`{name}` redeclared here"))
                    .with_order(1),
            )
    })
}

fn error_undeclared(span: TextLocation, name: &str, kind: &str) -> Diagnostic {
    let code = Code::new(Category::Resolve, 2);
    Diagnostic::error(code, span, |report| {
        report
            .with_message(format!(
                "No {kind} with the name `{name}` is available in this scope"
            ))
            .with_label(Label::new(span).with_message("This reference cannot be resolved"))
    })
}
