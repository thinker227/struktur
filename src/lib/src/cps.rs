//! Continuation-passing style representation of code.
//!
//! Functions in CPS consist of a [Complex] expression which might have some kind of "effect"
//! (such as introducting a variable or branching)
//! and which eventually terminates in a call to either a [Continuation] or some other function.
//! Importantly, functions in CPS do not return values, they only pass values forward to other functions.

use std::collections::HashMap;

use crate::{ast, id::Id, stage::Typed, symbols::Symbol};

/// ID of a continuation parameter.
#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub struct Continuation(Id);

/// A binding.
#[derive(Debug, Clone)]
pub struct Binding {
    /// Symbol of the binding.
    symbol: Symbol,
    /// Value bound to the binding.
    value: Atomic,
}

/// A function.
#[derive(Debug, Clone)]
pub struct Function {
    /// Symbol of the function parameter.
    param: Symbol,
    /// The continuation passed to the function.
    cont: Continuation,
    /// Body of the function.
    body: Complex,
}

/// A complex expression which always terminates in a function call instead of producing a value.
#[derive(Debug, Clone)]
pub enum Complex {
    /// A call to a function produced by an atomic expression, with some value as the argument.
    Call(Target, Atomic),
    /// Introduces a let-binding with a nested complex expression.
    Let(Box<Let>),
    /// Branches to two complex sub-expressions.
    If(Box<IfElse>),
}

/// The target of a function call.
#[derive(Debug, Clone)]
pub enum Target {
    /// Call a continuation.
    Cont(Continuation),
    /// Call a function producted by an atomic expression.
    Expr(Atomic),
    /// Halt execution.
    Halt,
}

/// A let-binding introduced in a complex expression.
#[derive(Debug, Clone)]
pub struct Let {
    /// Symbol of the variable.
    symbol: Symbol,
    /// Value bound to the binding.
    value: Atomic,
    /// Rest of the function body.
    expr: Complex,
}

/// Branches a complex expression.
#[derive(Debug, Clone)]
pub struct IfElse {
    /// The value to branch based on.
    condition: Atomic,
    /// Rest of the function body if the condition holds.
    if_true: Complex,
    /// Rest of the function body if the condition does not hold.
    if_false: Complex,
}

/// An an atomic expression which produces a value.
#[derive(Debug, Clone)]
pub enum Atomic {
    Unit,
    Int(u64),
    Bool(bool),
    String(String),
    Var(Symbol),
    Cont(Continuation),
    Lambda(Box<Function>),
}

/// Contains all info returned by transforming an AST into CPS.
#[derive(Debug, Clone)]
pub struct Cps {
    bindings: HashMap<Symbol, Binding>,
}

/// Transforms an AST into CPS representation.
pub fn transform_cps(ast: &ast::Ast<Typed>) -> Cps {
    todo!()
}
