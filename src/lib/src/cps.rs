//! Continuation-passing style representation of code.
//!
//! Functions in CPS consist of a [Complex] expression which might have some kind of "effect"
//! (such as introducting a variable or branching)
//! and which eventually terminates in a call to either a [Continuation] or some other function.
//! Importantly, functions in CPS do not return values, they only pass values forward to other functions.

use std::collections::HashMap;

use crate::{ast, id::{Id, IdProvider}, stage::Typed, symbols::Symbol};

/// A binding.
#[derive(Debug, Clone)]
pub struct Binding {
    /// Symbol of the binding.
    pub symbol: Symbol,
    /// The continuation which is passed the value of the binding.
    pub cont: Continuation,
    /// Value bound to the binding.
    pub value: Complex,
}

/// A lambda function.
#[derive(Debug, Clone)]
pub struct Lambda {
    /// Symbol of the lambda parameter.
    pub param: CpsSymbol,
    /// The continuation passed to the lambda.
    /// Only lambdas declared in source have continuations,
    /// lambdas generated during CPS conversion do not.
    pub cont: Option<Continuation>,
    /// Body of the lambda.
    pub body: Complex,
}

/// A function parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CpsSymbol {
    Symbol(Symbol),
    Gen(GenSymbol),
}

/// ID of a continuation parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Continuation(Id);

/// A generated symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct GenSymbol(Id);

/// A complex expression which always terminates in a function call instead of producing a value.
#[derive(Debug, Clone)]
pub enum Complex {
    /// A call to a function produced by an atomic expression, with some value as the argument
    /// and an optional argument to pass as the continuation for the function, if it takes one.
    Call(Target, Atomic, Option<Atomic>),
    /// Introduces a let-binding with a nested complex expression.
    Let(Box<Let>),
    /// Branches to two complex sub-expressions.
    If(Box<IfElse>),
}

/// The target of a function call.
#[derive(Debug, Clone)]
pub enum Target {
    /// Call a function producted by an atomic expression.
    Expr(Atomic),
    /// Halt execution.
    Halt,
}

/// A let-binding introduced in a complex expression.
#[derive(Debug, Clone)]
pub struct Let {
    /// Symbol of the variable.
    pub symbol: Symbol,
    /// Value bound to the binding.
    pub value: Atomic,
    /// Rest of the function body.
    pub expr: Complex,
}

/// Branches a complex expression.
#[derive(Debug, Clone)]
pub struct IfElse {
    /// The value to branch based on.
    pub condition: Atomic,
    /// Rest of the function body if the condition holds.
    pub if_true: Complex,
    /// Rest of the function body if the condition does not hold.
    pub if_false: Complex,
}

/// An an atomic expression which produces a value.
#[derive(Debug, Clone)]
pub enum Atomic {
    Unit,
    Int(u64),
    Bool(bool),
    String(String),
    Var(CpsSymbol),
    Cont(Continuation),
    Lambda(Box<Lambda>),
}

static CONTINUATION_PROVIDER: IdProvider<Continuation> = IdProvider::new(Continuation);

static GEN_PROVIDER: IdProvider<GenSymbol> = IdProvider::new(GenSymbol);

fn m(ast::Expr(expr, _, _): &ast::Expr<Typed>) -> Atomic {
    match expr {
        ast::ExprVal::Unit => Atomic::Unit,
        ast::ExprVal::Int(x) => Atomic::Int(*x),
        ast::ExprVal::Bool(x) => Atomic::Bool(*x),
        ast::ExprVal::String(s) => Atomic::String(s.clone()),
        ast::ExprVal::Var(var) => Atomic::Var(CpsSymbol::Symbol(*var)),
        ast::ExprVal::Bind(_) => unimplemented!(),
        ast::ExprVal::Lambda(lambda) => {
            let cont = CONTINUATION_PROVIDER.next();
            Atomic::Lambda(Box::new(Lambda {
                param: CpsSymbol::Symbol(lambda.param),
                cont: Some(cont),
                body: t(&lambda.body, Atomic::Cont(cont))
            }))
        }
        ast::ExprVal::Apply(_) => unimplemented!(),
        ast::ExprVal::If(_) => unimplemented!()
    }
}

fn t(e@ast::Expr(expr, _, _): &ast::Expr<Typed>, cont: Atomic) -> Complex {
    match expr {
        ast::ExprVal::Bind(binding) => {
            let p = CpsSymbol::Gen(GEN_PROVIDER.next());
            t(
                &binding.value,
                Atomic::Lambda(Box::new(Lambda {
                    param: p,
                    cont: None,
                    body: Complex::Let(Box::new(Let {
                        symbol: binding.symbol,
                        value: Atomic::Var(p),
                        expr: t(&binding.expr, cont)
                    }))
                }))
            )
        }
        ast::ExprVal::Apply(application) => {
            let target = CpsSymbol::Gen(GEN_PROVIDER.next());
            let arg = CpsSymbol::Gen(GEN_PROVIDER.next());
            t(
                &application.target,
                Atomic::Lambda(Box::new(Lambda {
                    param: target,
                    cont: None,
                    body: t(
                        &application.arg,
                        Atomic::Lambda(Box::new(Lambda {
                            param: arg,
                            cont: None,
                            body: Complex::Call(
                                Target::Expr(Atomic::Var(target)),
                                Atomic::Var(arg),
                                Some(cont)
                            )
                        }))
                    )
                }))
            )
        }
        ast::ExprVal::If(if_else) => {
            let condition = CpsSymbol::Gen(GEN_PROVIDER.next());
            t(
                &if_else.condition,
                Atomic::Lambda(Box::new(Lambda {
                    param: condition,
                    cont: None,
                    body: Complex::If(Box::new(IfElse {
                        condition: Atomic::Var(condition),
                        if_true: t(&if_else.if_true, cont.clone()),
                        if_false: t(&if_else.if_false, cont)
                    }))
                }))
            )
        }
        _ => Complex::Call(Target::Expr(cont), m(e), None)
    }
}

/// Contains all info returned by transforming an AST into CPS.
#[derive(Debug, Clone)]
pub struct Cps {
    pub bindings: HashMap<Symbol, Binding>,
}

/// Transforms an AST into CPS representation.
pub fn transform_cps(ast: &ast::Ast<Typed>) -> Cps {
    let mut bindings = HashMap::new();
    for item in &ast.root().0 {
        let ast::ItemVal::Binding(binding) = &item.0;

        let cont = CONTINUATION_PROVIDER.next();
        let symbol = binding.symbol;

        bindings.insert(symbol, Binding {
            symbol: symbol,
            cont,
            value: t(&binding.body, Atomic::Cont(cont))
        });
    }

    Cps { bindings }
}
