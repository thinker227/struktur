use std::collections::hash_map::HashMap;

use crate::{ast::*, stage::{Parse, Sem}, symbols::{BindingSymbol, Symbol, SymbolKind, Symbols, TypeVarSymbol, VariableSymbol}, text_span::TextSpan};

/// Resolves all the symbols of an AST.
pub fn resolve_symbols(ast: &Ast<Parse>) -> Result<Ast<Sem>, SymbolResError> {
    let mut resolver = Resolver::new(ast);

    let sem_root = resolver.root(ast.root())?;
    let symbols = resolver.symbols;

    Ok(Ast::new(sem_root, symbols))
}

#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum SymbolResError {
    #[error("A {kind} with the name `{name}` has already been declared in this scope")]
    DuplicateDeclaration {
        #[label]
        span: TextSpan,
        name: String,
        #[label("Previously declared here")]
        previous_declaration: TextSpan,
        kind: String,
    },

    #[error("No {kind} with the name `{name}` is available in this scope")]
    Undeclared {
        #[label]
        span: TextSpan,
        name: String,
        kind: String,
    },
}

type SymResult<T> = Result<T, SymbolResError>;

#[derive(Debug, Clone)]
struct Named {
    value: Option<Symbol>,
    type_var: Option<Symbol>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NameKind {
    Value,
    TypeVar,
}

#[derive(Debug, Clone)]
enum ActiveForall {
    Implicit,
    Explicit,
}

struct Resolver<'ast> {
    scopes: Vec<HashMap<String, Named>>,
    foralls: Vec<ActiveForall>,
    symbols: Symbols<Sem>,
    ast: &'ast Ast<Parse>,
}

impl<'ast> Resolver<'ast> {
    fn new(ast: &'ast Ast<Parse>) -> Self {
        Self {
            scopes: vec![HashMap::new()],
            foralls: Vec::new(),
            symbols: Symbols::new(),
            ast
        }
    }

    fn in_scope<R>(&mut self, f: impl FnOnce(&mut Self) -> SymResult<R>) -> SymResult<R> {
        self.scopes.push(HashMap::new());
        let res = f(self);
        self.scopes.pop();
        res
    }

    fn in_forall<R>(&mut self, forall: ActiveForall, f: impl FnOnce(&mut Self) -> SymResult<R>) -> SymResult<R> {
        self.foralls.push(forall);
        let res = f(self);
        self.foralls.pop();
        res
    }

    fn register(&mut self, name: String, data: SymbolKind<Sem>) -> Result<Symbol, Symbol> {
        let Resolver { scopes, symbols, .. } = self;

        let scope = scopes.last_mut()
            .expect("there should always be a scope");

        let named = scope.entry(name)
            .or_insert_with(|| Named {
                value: None,
                type_var: None
            });

        let spot = match data {
            SymbolKind::Var(_) => &mut named.value,
            SymbolKind::Binding(_) => &mut named.value,
            SymbolKind::TypeVar(_) => &mut named.type_var,
        };

        match spot {
            Some(x) => Err(*x),
            None => {
                let symbol = symbols.register(data);
                *spot = Some(symbol);
                Ok(symbol)
            }
        }
    }

    fn look_up(&self, name: &str, kind: NameKind) -> Option<Symbol> {
        for scope in self.scopes.iter().rev() {
            if let Some(named) = scope.get(name) {
                return match kind {
                    NameKind::Value => named.value,
                    NameKind::TypeVar => named.type_var,
                };
            }
        }

        None
    }

    fn root(&mut self, root: &Root<Parse>) -> SymResult<Root<Sem>> {
        // Forward refs
        let mut symbols = Vec::new();
        for item in &root.items {
            let symbol = self.register_item(item)?;
            symbols.push(symbol);
        }

        let mut sem_items = Vec::new();
        for (item, symbol) in root.items.iter().zip(symbols) {
            let sem_item = self.item(item, symbol)?;
            sem_items.push(sem_item);
        }

        Ok(Root {
            data: root.data,
            items: sem_items
        })
    }

    fn register_item(&mut self, item: &Item<Parse>) -> SymResult<Symbol> {
        let data = match item {
            Item::Binding(binding) => {
                SymbolKind::Binding(BindingSymbol {
                    name: binding.symbol.clone(),
                    decl: binding.id(),
                    data: ()
                })
            }
        };
        let name = data.name().clone();

        self.register(name.clone(), data)
            .map_err(|prev| {
                let prev = self.symbols.get(prev).decl();
                let prev_span = self.ast.get_node(prev).span();
                SymbolResError::DuplicateDeclaration {
                    span: item.span(),
                    name,
                    previous_declaration: prev_span,
                    kind: "binding".to_owned()
                }
            })
    }

    fn item(&mut self, item: &Item<Parse>, symbol: Symbol) -> SymResult<Item<Sem>> {
        let sem_item = match item {
            Item::Binding(binding) => {
                let sem_function = self.binding(binding, symbol)?;
                Item::Binding(sem_function)
            }
        };

        Ok(sem_item)
    }

    fn binding(&mut self, binding: &Binding<Parse>, function_symbol: Symbol) -> SymResult<Binding<Sem>> {
        let (sem_body, sem_ty) = self.in_scope(|this| {
            let sem_ty = this.in_forall(ActiveForall::Implicit, |this| {
                let sem_ty = match &binding.ty {
                    Some(ty) => Some(this.tyexpr(ty)?),
                    None => None
                };

                Ok(sem_ty)
            })?;

            let sem_body = this.expr(&binding.body)?;

            Ok((sem_body, sem_ty))
        })?;

        Ok(Binding {
            data: binding.data,
            body: sem_body,
            ty: sem_ty,
            symbol: function_symbol
        })
    }

    fn expr(&mut self, expr: &Expr<Parse>) -> SymResult<Expr<Sem>> {
        let sem_expr = match expr {
            Expr::Unit(unit) => Expr::Unit(UnitExpr {
                data: unit.data.with(())
            }),

            Expr::Int(int) => Expr::Int(IntExpr {
                data: int.data.with(()),
                val: int.val
            }),

            Expr::Bool(bool) => Expr::Bool(BoolExpr {
                data: bool.data.with(()),
                val: bool.val
            }),

            Expr::String(string) => Expr::String(StringExpr {
                data: string.data.with(()),
                val: string.val.clone(),
            }),

            Expr::Var(var) => {
                let var_symbol = self.look_up(&var.symbol, NameKind::Value)
                    .ok_or_else(|| SymbolResError::Undeclared {
                        span: TextSpan::empty(0),
                        name: var.symbol.clone(),
                        kind: "variable or binding".to_owned()
                    })?;

                Expr::Var(VarExpr {
                    data: var.data.with(()),
                    symbol: var_symbol,
                })
            }

            Expr::Bind(binding) => {
                let sem_value = self.expr(&binding.value)?;

                let (sem_pattern, sem_expr) = self.in_scope(|this| {
                    let sem_pattern = this.in_forall(ActiveForall::Implicit, |this| {
                        this.pattern(&binding.pattern)
                    })?;

                    let sem_expr = this.expr(&binding.expr)?;

                    Ok((sem_pattern, sem_expr))
                })?;

                Expr::bind(Let {
                    data: binding.data.with(()),
                    pattern: sem_pattern,
                    value: sem_value,
                    expr: sem_expr
                })
            }

            Expr::Lambda(lambda) => {
                let mut sem_cases = Vec::with_capacity(lambda.cases.len());

                for case in &lambda.cases {
                    let sem_case = self.case(case)?;
                    sem_cases.push(sem_case)
                }

                Expr::lambda(Lambda {
                    data: lambda.data.with(()),
                    cases: sem_cases
                })
            }

            Expr::Apply(application) => {
                let sem_target = self.expr(&application.target)?;
                let sem_arg = self.expr(&application.arg)?;

                Expr::apply(Application {
                    data: application.data.with(()),
                    target: sem_target,
                    arg: sem_arg
                })
            }

            Expr::If(if_else) => {
                let sem_condition = self.expr(&if_else.condition)?;
                let sem_if_true = self.expr(&if_else.if_true)?;
                let sem_if_false = self.expr(&if_else.if_false)?;

                Expr::if_else(IfElse {
                    data: if_else.data.with(()),
                    condition: sem_condition,
                    if_true: sem_if_true,
                    if_false: sem_if_false
                })
            }

            Expr::TyAnn(ann) => {
                let sem_expr = self.expr(&ann.expr)?;
                let sem_ty = self.tyexpr(&ann.ty)?;

                Expr::TyAnn(Box::new(TyAnnExpr {
                    data: ann.data,
                    expr: sem_expr,
                    ty: sem_ty
                }))
            }
        };

        Ok(sem_expr)
    }

    fn case(&mut self, case: &Case<Parse>) -> SymResult<Case<Sem>> {
        let (sem_pattern, sem_body) = self.in_scope(|this| {
            let sem_pattern = this.pattern(&case.pattern)?;
            let sem_body = this.expr(&case.body)?;
            Ok((sem_pattern, sem_body))
        })?;

        Ok(Case {
            pattern: sem_pattern,
            body: sem_body,
            data: case.data
        })
    }

    fn pattern(&mut self, pattern: &Pattern<Parse>) -> SymResult<Pattern<Sem>> {
        let sem_pattern = match pattern {
            Pattern::Wildcard(wildcard) => Pattern::Wildcard(wildcard.clone()),

            Pattern::Var(var) => {
                let var_data = VariableSymbol {
                    name: var.symbol.clone(),
                    decl: var.data.id,
                    data: ()
                };

                let var_symbol = self.register(var.symbol.clone(), SymbolKind::Var(var_data)).expect("todo");

                Pattern::Var(VarPattern {
                    data: var.data,
                    symbol: var_symbol
                })
            }

            Pattern::Unit(unit) => Pattern::Unit(unit.clone()),

            Pattern::Number(number) => Pattern::Number(number.clone()),

            Pattern::Bool(bool) => Pattern::Bool(bool.clone()),

            Pattern::TyAnn(ann) => {
                let sem_pat = self.pattern(&ann.pat)?;
                let sem_ty = self.tyexpr(&ann.ty)?;

                Pattern::TyAnn(Box::new(TyAnnPattern {
                    data: ann.data,
                    pat: sem_pat,
                    ty: sem_ty
                }))
            }
        };

        Ok(sem_pattern)
    }

    fn tyexpr(&mut self, tyexpr: &TyExpr<Parse>) -> SymResult<TyExpr<Sem>> {
        let sem_tyexpr = match tyexpr {
            TyExpr::Unit(unit) => TyExpr::Unit(unit.clone()),
            TyExpr::Int(int) => TyExpr::Int(int.clone()),
            TyExpr::Bool(bool) => TyExpr::Bool(bool.clone()),
            TyExpr::String(string) => TyExpr::String(string.clone()),

            TyExpr::Var(var) => {
                let name = &var.symbol;

                let symbol = if let Some(symbol) = self.look_up(&var.symbol, NameKind::TypeVar) {
                    symbol
                } else if let Some(ActiveForall::Implicit) = self.foralls.last() {
                    self.register(name.clone(), SymbolKind::TypeVar(TypeVarSymbol {
                        name: name.clone(),
                        decl: var.id()
                    })).expect("todo")
                } else {
                    return Err(SymbolResError::Undeclared {
                        span: var.span(),
                        name: name.clone(),
                        kind: "type variable".to_owned()
                    });
                };

                TyExpr::Var(VarTyExpr {
                    data: var.data,
                    symbol
                })
            }

            TyExpr::Function(function) => {
                let sem_param = self.tyexpr(&function.param)?;
                let sem_ret = self.tyexpr(&function.ret)?;

                TyExpr::Function(Box::new(FunctionTyExpr {
                    data: function.data,
                    param: sem_param,
                    ret: sem_ret
                }))
            }

            TyExpr::Forall(forall) => {
                self.in_scope(|this| {
                    let (sem_vars, sem_ty) = this.in_forall(ActiveForall::Explicit, |this| {
                        let mut sem_vars = Vec::new();

                        for var in &forall.vars {
                            let symbol = this.register(
                                var.clone(),
                                SymbolKind::TypeVar(TypeVarSymbol {
                                    name: var.clone(),
                                    decl: forall.id()
                                }
                            )).map_err(|prev| {
                                let prev = this.symbols.get(prev).decl();
                                let prev_span = this.ast.get_node(prev).span();
                                SymbolResError::DuplicateDeclaration {
                                    span: forall.span(),
                                    name: var.clone(),
                                    previous_declaration: prev_span,
                                    kind: "type variable".to_owned()
                                }
                            })?;

                            sem_vars.push(symbol);
                        }

                        let sem_ty = this.tyexpr(&forall.ty)?;

                        Ok((sem_vars, sem_ty))
                    })?;

                    Ok(TyExpr::Forall(Box::new(ForallTyExpr {
                        data: forall.data,
                        vars: sem_vars,
                        ty: sem_ty
                    })))
                })?
            }
        };

        Ok(sem_tyexpr)
    }
}
