//! Continuation-passing style representation of code.
//!
//! Functions in CPS consist of a [Complex] expression which might have some kind of "effect"
//! (such as introducting a variable or branching)
//! and which eventually terminates in a call to either a [Continuation] or some other function.
//! Importantly, functions in CPS do not return values, they only pass values forward to other functions.

use petgraph::algo::toposort;

use crate::{ast, id::{Id, IdProvider}, patterns::{self, Constructor, Decision}, stage::Typed, symbols::Symbol};

/// A binding.
#[derive(Debug, Clone)]
pub struct Binding {
    /// Symbol of the binding.
    pub symbol: Symbol,
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
    Discard,
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
    Call(Atomic, Atomic, Option<Atomic>),
    /// Meta-return the value produced by an atomic expression.
    Return(Atomic),
    /// Panics and aborts execution.
    Panic(Panic),
    /// Introduces a let-binding with a nested complex expression.
    Let(Box<Let>),
    /// Branches to two complex sub-expressions.
    If(Box<IfElse>),
}

/// The reason for a panic.
#[derive(Debug, Clone)]
pub enum Panic {
    /// A failure case of a decision tree was reached.
    NonExhaustiveMatch,
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
    Equality(Box<Atomic>, Box<Atomic>),
}

/// A continuation passed during conversion of a complex expression.
#[derive(Debug, Clone)]
enum ConversionContinuation {
    /// The complex expression is in the context of a continuation.
    Continuable(Atomic),
    /// The complex expression is the body of a top-level binding
    /// which will be assigned instead of a continuation being called.
    Assign,
}

static CONTINUATION_PROVIDER: IdProvider<Continuation> = IdProvider::new(Continuation);

static GEN_PROVIDER: IdProvider<GenSymbol> = IdProvider::new(GenSymbol);

fn fold_bindings(action: Complex, value: Atomic, bindings: &[patterns::Binding]) -> Complex {
    bindings.iter().fold(action, |acc, binding| {
        // TODO: This only applies since there are no constructors taking arguments currently.
        assert_eq!(binding.value.path(), &[]);

        Complex::Let(Box::new(Let {
            symbol: binding.variable,
            // This currently doesn't make a whole lot of sense since "each" binding will get the same value,
            // but currently there can only be a single binding per pattern, so this does makes sense.
            value: value.clone(),
            expr: acc
        }))
    })
}

fn multi_pattern(node: &Decision, actions: &[Complex], value: Atomic) -> Complex {
    match node {
        Decision::Success(body) => {
            let action = actions[body.action].clone();
            fold_bindings(action, value, &body.bindings)
        }

        Decision::Failure => Complex::Panic(Panic::NonExhaustiveMatch),

        Decision::Match { target, case, fallback } => {
            assert_eq!(target.path(), &[]);

            let body = multi_pattern(&case.body, actions, value.clone());
            let fallback = multi_pattern(fallback, actions, value.clone());

            let match_value = match &case.constructor {
                Constructor::Bool(bool) => Atomic::Bool(*bool),
                Constructor::Number(number) => Atomic::Int(*number),
            };

            let condition = Atomic::Equality(Box::new(value.clone()), Box::new(match_value));

            Complex::If(Box::new(IfElse {
                condition,
                if_true: body,
                if_false: fallback
            }))
        }
    }
}

fn single_pattern(node: &Decision, action: Complex, value: Atomic) -> Complex {
    let (bindings, condition) = match node {
        Decision::Success(body) => {
            assert_eq!(body.action, 0);
            (&body.bindings, None)
        }

        // It should be impossible for the single pattern in a let-expression to be an immediate failure.
        Decision::Failure => unreachable!(),

        Decision::Match { target, case, fallback } => {
            // TODO: This only applies since there are no constructors taking arguments currently.
            assert_eq!(target.path(), &[]);

            match fallback.as_ref() {
                Decision::Failure => {}
                // It should be impossible for the fallback in a let-expression to be anything but a failure.
                _ => unreachable!()
            }

            let bindings = match &case.body {
                Decision::Success(body) => {
                    assert_eq!(body.action, 0);
                    &body.bindings
                }
                // It should be impossible for the nested pattern in a let-expression to be anything but a success.
                _ => unreachable!()
            };

            let match_value = match &case.constructor {
                Constructor::Bool(bool) => Atomic::Bool(*bool),
                Constructor::Number(number) => Atomic::Int(*number),
            };

            let condition = Atomic::Equality(Box::new(value.clone()), Box::new(match_value));

            (bindings, Some(condition))
        }
    };

    let bind = fold_bindings(action, value, bindings);

    match condition {
        Some(condition) => Complex::If(Box::new(IfElse {
            condition,
            if_true: bind,
            if_false: Complex::Panic(Panic::NonExhaustiveMatch)
        })),
        None => bind
    }
}

fn m(expr: &ast::Expr<Typed>) -> Atomic {
    match expr {
        ast::Expr::Unit(_) => Atomic::Unit,
        ast::Expr::Int(int) => Atomic::Int(int.val),
        ast::Expr::Bool(bool) => Atomic::Bool(bool.val),
        ast::Expr::String(string) => Atomic::String(string.val.clone()),
        ast::Expr::Var(var) => Atomic::Var(CpsSymbol::Symbol(var.symbol)),
        ast::Expr::Bind(_) => unimplemented!(),
        ast::Expr::Lambda(lambda) => {
            let cont = CONTINUATION_PROVIDER.next();
            let param = GEN_PROVIDER.next();

            let actions = lambda.cases.actions.iter()
                .map(|expr| t(
                    expr,
                    ConversionContinuation::Continuable(Atomic::Cont(cont))
                ))
                .collect::<Vec<_>>();

            let body = multi_pattern(
                &lambda.cases.root,
                &actions,
                Atomic::Var(CpsSymbol::Gen(param))
            );

            Atomic::Lambda(Box::new(Lambda {
                param: CpsSymbol::Gen(param),
                cont: Some(cont),
                body
            }))
        }
        ast::Expr::Apply(_) => unimplemented!(),
        ast::Expr::If(_) => unimplemented!(),
        ast::Expr::TyAnn(_) => unreachable!(),
    }
}

fn t(expr: &ast::Expr<Typed>, cont: ConversionContinuation) -> Complex {
    match expr {
        ast::Expr::Bind(binding) => {
            let param = CpsSymbol::Gen(GEN_PROVIDER.next());
            t(
                &binding.value,
                ConversionContinuation::Continuable(Atomic::Lambda(Box::new(Lambda {
                    param,
                    cont: None,
                    body: single_pattern(
                        &binding.pattern,
                        t(&binding.expr, cont),
                        Atomic::Var(param)
                    )
                })))
            )
        }
        ast::Expr::Apply(application) => {
            let target = CpsSymbol::Gen(GEN_PROVIDER.next());
            let arg = CpsSymbol::Gen(GEN_PROVIDER.next());
            let cont = match cont {
                ConversionContinuation::Continuable(cont) => cont,
                ConversionContinuation::Assign => {
                    let param = CpsSymbol::Gen(GEN_PROVIDER.next());
                    Atomic::Lambda(Box::new(Lambda {
                        param,
                        cont: None,
                        body: Complex::Return(Atomic::Var(param))
                    }))
                }
            };
            t(
                &application.target,
                ConversionContinuation::Continuable(Atomic::Lambda(Box::new(Lambda {
                    param: target,
                    cont: None,
                    body: t(
                        &application.arg,
                        ConversionContinuation::Continuable(Atomic::Lambda(Box::new(Lambda {
                            param: arg,
                            cont: None,
                            body: Complex::Call(
                                Atomic::Var(target),
                                Atomic::Var(arg),
                                Some(cont)
                            )
                        })))
                    )
                })))
            )
        }
        ast::Expr::If(if_else) => {
            let condition = CpsSymbol::Gen(GEN_PROVIDER.next());
            t(
                &if_else.condition,
                ConversionContinuation::Continuable(Atomic::Lambda(Box::new(Lambda {
                    param: condition,
                    cont: None,
                    body: Complex::If(Box::new(IfElse {
                        condition: Atomic::Var(condition),
                        if_true: t(&if_else.if_true, cont.clone()),
                        if_false: t(&if_else.if_false, cont)
                    }))
                })))
            )
        }
        _ => match cont {
            ConversionContinuation::Continuable(cont) => Complex::Call(cont, m(expr), None),
            ConversionContinuation::Assign => Complex::Return(m(expr))
        }
    }
}

/// Contains all info returned by transforming an AST into CPS.
#[derive(Debug, Clone)]
pub struct Cps {
    pub bindings: Vec<Binding>,
}

/// Transforms an AST into CPS representation.
pub fn transform_cps(ast: &ast::Ast<Typed>) -> Cps {
    let mut bindings = Vec::new();

    // Ensure that bindings are ordered according to their reference dependencies
    // so that bindings that later bindings depend on will be emitted first.

    let sorted = toposort(ast.ref_graph(), None)
        .expect("binding reference graph should not have cycles");

    // TODO: This is kinda ugly, maybe put this in a helper in the AST or something.
    let order = sorted.iter()
        .map(|index| ast.ref_graph().node_weight(*index).unwrap())
        .map(|symbol| ast.symbols().get(*symbol))
        .map(|symbol| ast.get_node_as::<ast::Binding<Typed>>(symbol.decl()).unwrap())
        .rev();

    for binding in order {
        let symbol = binding.symbol;

        bindings.push(Binding {
            symbol,
            value: t(&binding.body, ConversionContinuation::Assign)
        });
    }

    Cps { bindings }
}
