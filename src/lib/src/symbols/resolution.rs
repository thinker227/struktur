use std::collections::hash_map::{HashMap, Entry};

use crate::{ast::*, stage::{Parse, Sem}, symbols::{BindingSymbol, Symbol, SymbolKind, Symbols, VariableSymbol}, text_span::TextSpan};

/// Resolves all the symbols of an AST.
pub fn resolve_symbols(ast: &Ast<Parse>) -> Result<Ast<Sem>, SymbolResError> {
    let mut resolver = Resolver::new(ast);

    let sem_root = resolver.root(ast.root())?;
    let symbols = resolver.symbols;

    Ok(Ast::new(sem_root, symbols, ()))
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

        Ok(Root(sem_items, node_data.clone().into_stage()))
    }

    fn register_item(&mut self, Item(item, node_data): &Item<Parse>) -> SymResult<Symbol> {
        let data = match item {
            ItemVal::Binding(binding) => {
                SymbolKind::Binding(BindingSymbol {
                    name: binding.symbol.clone(),
                    decl: node_data.id,
                    data: ()
                })
            }
        };
        let name = data.name().clone();

        self.register(name.clone(), data)
            .map_err(|prev| {
                let prev = self.symbols.get(prev).decl();
                let prev_span = *self.ast.get_node(prev).data();
                SymbolResError::DuplicateDeclaration {
                    span: node_data.data,
                    name,
                    previous_declaration: prev_span
                }
            })
    }

    fn item(&mut self, Item(item, node_data): &Item<Parse>, symbol: Symbol) -> SymResult<Item<Sem>> {
        let val = match item {
            ItemVal::Binding(binding) => {
                let sem_function = self.binding(binding, node_data, symbol)?;
                ItemVal::Binding(sem_function)
            }
        };

        Ok(Item(val, node_data.clone().into_stage()))
    }

    fn binding(&mut self, binding: &Binding<Parse>, _: &NodeData<Parse>, function_symbol: Symbol) -> SymResult<Binding<Sem>> {
        let sem_body = self.in_scope(|this| {
            // This technically doesn't need a scope,
            // but it's nice just to ensure that symbols don't accidentally leak out.
            this.expr(&binding.body)
        })?;

        Ok(Binding {
            body: sem_body,
            symbol: function_symbol
        })
    }

    fn expr(&mut self, Expr(expr, _, node_data): &Expr<Parse>) -> SymResult<Expr<Sem>> {
        let val = match expr {
            ExprVal::Unit => ExprVal::Unit,

            ExprVal::Int(x) => ExprVal::Int(*x),

            ExprVal::Bool(x) => ExprVal::Bool(*x),

            ExprVal::String(x) => ExprVal::String(x.clone()),

            ExprVal::Var(var_name) => {
                let var_symbol = self.look_up(var_name)
                    .ok_or_else(|| SymbolResError::Undeclared {
                        span: TextSpan::empty(0),
                        name: var_name.clone()
                    })?;

                ExprVal::Var(var_symbol)
            }

            ExprVal::Bind(binding) => {
                let sem_value = self.expr(&binding.value)?;

                let (sem_pattern, sem_expr) = self.in_scope(|this| {
                    let sem_pattern = this.pattern(&binding.pattern)?;
                    let sem_expr = this.expr(&binding.expr)?;
                    Ok((sem_pattern, sem_expr))
                })?;

                ExprVal::bind(Let {
                    pattern: sem_pattern,
                    value: sem_value,
                    expr: sem_expr
                })
            }

            ExprVal::Lambda(lambda) => {
                let mut sem_cases = Vec::with_capacity(lambda.cases.len());

                for case in &lambda.cases {
                    let sem_case = self.case(case)?;
                    sem_cases.push(sem_case)
                }

                ExprVal::lambda(Lambda {
                    cases: sem_cases
                })
            }

            ExprVal::Apply(application) => {
                let sem_target = self.expr(&application.target)?;
                let sem_arg = self.expr(&application.arg)?;

                ExprVal::apply(Application {
                    target: sem_target,
                    arg: sem_arg
                })
            }

            ExprVal::If(if_else) => {
                let sem_condition = self.expr(&if_else.condition)?;
                let sem_if_true = self.expr(&if_else.if_true)?;
                let sem_if_false = self.expr(&if_else.if_false)?;

                ExprVal::if_else(IfElse {
                    condition: sem_condition,
                    if_true: sem_if_true,
                    if_false: sem_if_false
                })
            }
        };

        Ok(Expr(val, (), node_data.clone().into_stage()))
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
            data: case.data.clone().into_stage()
        })
    }

    fn pattern(&mut self, Pattern(pattern, node_data): &Pattern<Parse>) -> SymResult<Pattern<Sem>> {
        let val = match pattern {
            PatternVal::Wildcard => PatternVal::Wildcard,

            PatternVal::Var(var) => {
                let var_data = VariableSymbol {
                    name: var.clone(),
                    decl: node_data.id,
                    data: ()
                };

                let var_symbol = self.register(var.clone(), SymbolKind::Var(var_data)).expect("todo");

                PatternVal::Var(var_symbol)
            }

            PatternVal::Unit => PatternVal::Unit,

            PatternVal::Number(val) => PatternVal::Number(*val),

            PatternVal::Bool(val) => PatternVal::Bool(*val),
        };

        Ok(Pattern(val, node_data.clone().into_stage()))
    }
}
