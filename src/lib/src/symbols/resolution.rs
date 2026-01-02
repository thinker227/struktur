use std::collections::hash_map::{HashMap, Entry};

use crate::{ast::*, stage::{Parse, Sem}, symbols::{BindingSymbol, Symbol, SymbolKind, Symbols, VariableSymbol}, text_span::TextSpan};

/// Resolves all the symbols of an AST.
pub fn resolve_symbols(ast: &Ast<Parse>) -> Result<Ast<Sem>, SymbolResError> {
    let mut resolver = Resolver::new(ast);

    let sem_root = resolver.root(ast.root())?;
    let symbols = resolver.symbols;

    Ok(Ast::new(sem_root, symbols))
}

#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum SymbolResError {
    #[error("A symbol with the name `{name}` has already been declared in this scope")]
    DuplicateDeclaration {
        #[label]
        span: TextSpan,
        name: String,
        #[label("Previously declared here")]
        previous_declaration: TextSpan,
    },

    #[error("No symbol with the name `{name}` is available in this scope")]
    Undeclared {
        #[label]
        span: TextSpan,
        name: String,
    },
}

type SymResult<T> = Result<T, SymbolResError>;

struct Resolver<'ast> {
    scopes: Vec<HashMap<String, Symbol>>,
    symbols: Symbols<Sem>,
    ast: &'ast Ast<Parse>,
}

impl<'ast> Resolver<'ast> {
    fn new(ast: &'ast Ast<Parse>) -> Self {
        Self {
            scopes: vec![HashMap::new()],
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

    fn register(&mut self, name: String, data: SymbolKind<Sem>) -> Result<Symbol, Symbol> {
        let Resolver { scopes, symbols, .. } = self;

        let scope = scopes.last_mut()
            .expect("there should always be a scope");

        match scope.entry(name) {
            Entry::Occupied(entry) => Err(*entry.get()),
            Entry::Vacant(entry) => {
                let symbol = symbols.register(data);
                entry.insert(symbol);
                Ok(symbol)
            }
        }
    }

    fn look_up(&self, name: &str) -> Option<Symbol> {
        for scope in self.scopes.iter().rev() {
            if let Some(sym) = scope.get(name) {
                return Some(*sym);
            }
        }

        None
    }

    fn root(&mut self, Root(items, node_data): &Root<Parse>) -> SymResult<Root<Sem>> {
        // Forward refs
        let mut symbols = Vec::new();
        for item in items {
            let symbol = self.register_item(item)?;
            symbols.push(symbol);
        }

        let mut sem_items = Vec::new();
        for (item, symbol) in items.iter().zip(symbols) {
            let sem_item = self.item(item, symbol)?;
            sem_items.push(sem_item);
        }

        Ok(Root(sem_items, *node_data))
    }

    fn register_item(&mut self, item: &Item<Parse>) -> SymResult<Symbol> {
        let data = match item {
            Item::Binding(binding) => {
                SymbolKind::Binding(BindingSymbol {
                    name: binding.symbol.clone(),
                    decl: binding.body.id(),
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
                    previous_declaration: prev_span
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
        let sem_body = self.in_scope(|this| {
            // This technically doesn't need a scope,
            // but it's nice just to ensure that symbols don't accidentally leak out.
            this.expr(&binding.body)
        })?;

        Ok(Binding {
            data: binding.data,
            body: sem_body,
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
                let var_symbol = self.look_up(&var.symbol)
                    .ok_or_else(|| SymbolResError::Undeclared {
                        span: TextSpan::empty(0),
                        name: var.symbol.clone()
                    })?;

                Expr::Var(VarExpr {
                    data: var.data.with(()),
                    symbol: var_symbol,
                })
            }

            Expr::Bind(binding) => {
                let sem_value = self.expr(&binding.value)?;

                let (sem_pattern, sem_expr) = self.in_scope(|this| {
                    let sem_pattern = this.pattern(&binding.pattern)?;
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
        };

        Ok(sem_pattern)
    }
}
