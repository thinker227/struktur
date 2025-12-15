//! Symbols and semantic resolution.

use std::collections::HashMap;
use std::collections::hash_map::Entry;

use derivative::Derivative;

use crate::id::{Id, IdProvider};
use crate::stage::{Parse, Sem, Stage};
use crate::ast::*;

/// A reference to a symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(Id);

impl Symbol {
    #[cfg(test)]
    /// Allows tests to construct symbols for use in "fake" ASTs.
    pub fn next() -> Symbol {
        SYMBOL_PROVIDER.next()
    }
}

static SYMBOL_PROVIDER: IdProvider<Symbol> = IdProvider::new(Symbol);

/// Data for a symbol.
#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub enum SymbolData<S: Stage> {
    /// A variable.
    Var(VariableData<S>),
    /// A function.
    Func(FunctionData<S>),
}

/// Data for a variable symbol.
#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct VariableData<S: Stage> {
    /// The name of the variable.
    pub name: String,
    /// The ID of the declaring node of the variable.
    pub decl: NodeId,
    /// Stage-specific additional for the variable.
    pub data: S::VarData,
}

impl<S: Stage> VariableData<S> {
    pub fn map<T: Stage>(&self, f: impl FnOnce(&S::VarData) -> T::VarData) -> VariableData<T> {
        VariableData {
            name: self.name.clone(),
            decl: self.decl,
            data: f(&self.data)
        }
    }
}

/// Data for a function symbol.
#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct FunctionData<S: Stage> {
    /// The name of the function.
    pub name: String,
    /// The ID of the declaring node of the function.
    pub decl: NodeId,
    /// Stage-specific additional for the function.
    pub data: S::FuncData,
}

impl<S: Stage> FunctionData<S> {
    pub fn map<T: Stage>(&self, f: impl FnOnce(&S::FuncData) -> T::FuncData) -> FunctionData<T> {
        FunctionData {
            name: self.name.clone(),
            decl: self.decl,
            data: f(&self.data)
        }
    }
}

impl<S: Stage> SymbolData<S> {
    /// Gets the name of the symbol.
    pub fn name(&self) -> &String {
        match self {
            SymbolData::Var(variable) => &variable.name,
            SymbolData::Func(function) => &function.name,
        }
    }

    pub fn decl(&self) -> NodeId {
        match self {
            SymbolData::Var(variable) => variable.decl,
            SymbolData::Func(function) => function.decl,
        }
    }
}

/// Contains mappings between [`Symbol`]s and [`SymbolData`].
#[derive(Derivative)]
#[derivative(Debug(bound = ""))]
pub struct Symbols<S: Stage> {
    data: HashMap<Symbol, SymbolData<S>>,
}

impl<S: Stage> Symbols<S> {
    /// Constructs a new [`Symbols`].
    pub fn new() -> Self {
        Self {
            data: HashMap::new(),
        }
    }

    /// Gets the data for a given symbol.
    ///
    /// # Panics
    /// Panics if the given symbol does not originate from this [`Symbols`].
    pub fn get(&self, symbol: Symbol) -> &SymbolData<S> {
        self.data.get(&symbol)
            .expect("symbol ID should be valid")
    }

    /// Registers data for a new symbol and returns it.
    pub fn register(&mut self, data: SymbolData<S>) -> Symbol {
        let symbol = SYMBOL_PROVIDER.next();
        self.data.insert(symbol, data);
        symbol
    }

    pub fn map<T: Stage>(&self, mut f: impl FnMut(Symbol, &SymbolData<S>) -> SymbolData<T>) -> Symbols<T> {
        let data = self.data.iter()
            .map(|(symbol, data)| (
                *symbol,
                f(*symbol, data)
            ))
            .collect();

        Symbols {
            data
        }
    }
}

/// Resolves all the symbols of an AST.
pub fn resolve_symbols(ast: &Ast<Parse>) -> Ast<Sem> {
    let mut resolver = Resolver::new();

    let sem_root = resolver.root(ast.root());
    let symbols = resolver.symbols;

    Ast::new(sem_root, symbols, ())
}

struct Resolver {
    scopes: Vec<HashMap<String, Symbol>>,
    symbols: Symbols<Sem>,
}

impl Resolver {
    fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
            symbols: Symbols::new()
        }
    }

    fn in_scope<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.scopes.push(HashMap::new());
        let res = f(self);
        self.scopes.pop();
        res
    }

    fn register(&mut self, name: String, data: SymbolData<Sem>) -> Result<Symbol, SymbolData<Sem>> {
        let Resolver { scopes, symbols } = self;

        let scope = scopes.last_mut()
            .expect("there should always be a scope");

        match scope.entry(name) {
            Entry::Occupied(_) => Err(data),
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

    fn root(&mut self, Root(items, node_data): &Root<Parse>) -> Root<Sem> {
        // Forward refs
        let mut symbols = Vec::new();
        for item in items {
            let symbol = self.register_item(item);
            symbols.push(symbol);
        }

        let mut sem_items = Vec::new();
        for (item, symbol) in items.iter().zip(symbols) {
            let sem_item = self.item(item, symbol);
            sem_items.push(sem_item);
        }

        Root(sem_items, node_data.clone().into_stage())
    }

    fn register_item(&mut self, Item(item, node_data): &Item<Parse>) -> Symbol {
        let data = match item {
            ItemVal::Binding(function) => {
                SymbolData::Func(FunctionData {
                    name: function.symbol.clone(),
                    decl: node_data.id,
                    data: ()
                })
            }
        };

        self.register(data.name().clone(), data)
            .map_err(|d| format!("duplicate item `{}`", d.name()))
            .unwrap()
    }

    fn item(&mut self, Item(item, node_data): &Item<Parse>, symbol: Symbol) -> Item<Sem> {
        let val = match item {
            ItemVal::Binding(function) => {
                let sem_function = self.function(function, node_data, symbol);
                ItemVal::Binding(sem_function)
            }
        };

        Item(val, node_data.clone().into_stage())
    }

    fn function(&mut self, function: &Binding<Parse>, node_data: &NodeData<Parse>, function_symbol: Symbol) -> Binding<Sem> {
        let (sem_body, param_symbol) = self.in_scope(|this| {
            let param_data = VariableData {
                name: function.param.clone(),
                decl: node_data.id,
                data: ()
            };

            let param_symbol = this.register(function.param.clone(), SymbolData::Var(param_data))
                .map_err(|d| format!("duplicate parameter `{}`", d.name()))
                .unwrap();

            let sem_body = this.expr(&function.body);

            (sem_body, param_symbol)
        });

        Binding {
            body: sem_body,
            symbol: function_symbol,
            param: param_symbol
        }
    }

    fn expr(&mut self, Expr(expr, _, node_data): &Expr<Parse>) -> Expr<Sem> {
        let val = match expr {
            ExprVal::Unit => ExprVal::Unit,

            ExprVal::Int(x) => ExprVal::Int(*x),

            ExprVal::Bool(x) => ExprVal::Bool(*x),

            ExprVal::String(x) => ExprVal::String(x.clone()),

            ExprVal::Var(var_name) => {
                let var_symbol = self.look_up(var_name)
                    .ok_or_else(|| format!("no variable `{}`", var_name))
                    .unwrap();

                ExprVal::Var(var_symbol)
            }

            ExprVal::Bind(binding) => {
                let sem_value = self.expr(&binding.value);

                let (symbol, sem_expr) = self.in_scope(|this| {
                    let var_data = VariableData {
                        name: binding.symbol.clone(),
                        decl: node_data.id,
                        data: ()
                    };

                    let var_symbol = this.register(binding.symbol.clone(), SymbolData::Var(var_data)).unwrap();

                    let sem_expr = this.expr(&binding.expr);

                    (var_symbol, sem_expr)
                });

                ExprVal::bind(Let {
                    symbol,
                    value: sem_value,
                    expr: sem_expr
                })
            }

            ExprVal::Lambda(lambda) => {
                let (param_symbol, sem_body) = self.in_scope(|this| {
                    let param_data = VariableData {
                        name: lambda.param.clone(),
                        decl: node_data.id,
                        data: ()
                    };

                    let param_symbol = this.register(lambda.param.clone(), SymbolData::Var(param_data)).unwrap();

                    let sem_body = this.expr(&lambda.body);

                    (param_symbol, sem_body)
                });

                ExprVal::lambda(Lambda {
                    param: param_symbol ,
                    body: sem_body
                })
            }

            ExprVal::Apply(application) => {
                let sem_target = self.expr(&application.target);
                let sem_arg = self.expr(&application.arg);

                ExprVal::apply(Application {
                    target: sem_target,
                    arg: sem_arg
                })
            }
        };

        Expr(val, (), node_data.clone().into_stage())
    }
}
