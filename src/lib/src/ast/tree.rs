//! Definitions of AST nodes.
//!
//! This module uses macros from the companion crate `struktur_macros`
//! to help *significantly* shorten the code required for each node.
//! [`struct_node`] is expanded into a struct with a set of fields and trait implementations
//! for [Node], [ToNodeData], [Drive], [Clone] and [Debug](std::fmt::Debug).
//! [`enum_node`] is expanded into an enum with a set of variants and the same trait implementations
//! as structs, as well as a struct for each variant.

use derivative::Derivative;
use struktur_macros::{struct_node, enum_node};

use crate::{ast::{NodeData, ToNodeData}, stage::Stage};

/*-------*\
|  Nodes  |
\*-------*/

struct_node! {
    Root<S> where
    items: Vec<Item<S>>
}

enum_node! {
    Item<S> where
    Binding<S> as Binding {
        raw symbol: S::Sym,
        ty: S::TyAnn,
        body: Expr<S>
    }
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct ExprData<S: Stage> {
    pub node: NodeData,
    pub expr: S::ExprData,
}

impl<S: Stage> ToNodeData for ExprData<S> {
    fn node_data(&self) -> NodeData {
        self.node.node_data()
    }
}

enum_node! {
    Expr<S> where
    UnitExpr<S> as Unit {
        data: ExprData<S>
    },
    IntExpr<S> as Int {
        data: ExprData<S>,
        raw val: u64
    },
    BoolExpr<S> as Bool {
        data: ExprData<S>,
        raw val: bool
    },
    StringExpr<S> as String {
        data: ExprData<S>,
        raw val: String
    },
    VarExpr<S> as Var {
        data: ExprData<S>,
        raw symbol: S::Sym
    },
    box Let<S> as Bind {
        data: ExprData<S>,
        pattern: S::Pattern,
        value: Expr<S>,
        expr: Expr<S>
    },
    box Lambda<S> as Lambda {
        data: ExprData<S>,
        cases: S::Cases
    },
    box Application<S> as Apply {
        data: ExprData<S>,
        target: Expr<S>,
        arg: Expr<S>
    },
    box IfElse<S> as If {
        data: ExprData<S>,
        condition: Expr<S>,
        if_true: Expr<S>,
        if_false: Expr<S>
    },
    box TyAnn(S::TyAnnExpr)
}

struct_node! {
    TyAnnExpr<S> where
    expr: Expr<S>,
    ty: TyExpr<S>
}

struct_node! {
    Case<S> where
    pattern: S::Pattern,
    body: Expr<S>
}

enum_node! {
    Pattern<S> where
    WildcardPattern as Wildcard {},
    VarPattern<S> as Var {
        raw symbol: S::Sym
    },
    UnitPattern as Unit {},
    NumberPattern as Number {
        raw val: u64
    },
    BoolPattern as Bool {
        raw val: bool
    },
    box TyAnn(S::TyAnnPattern)
}

struct_node! {
    TyAnnPattern<S> where
    pat: Pattern<S>,
    ty: TyExpr<S>
}

enum_node! {
    TyExpr<S> where
    UnitTyExpr as Unit {},
    IntTyExpr as Int {},
    BoolTyExpr as Bool {},
    StringTyExpr as String {},
    VarTyExpr<S> as Var {
        raw symbol: S::Sym
    },
    box FunctionTyExpr<S> as Function {
        param: TyExpr<S>,
        ret: TyExpr<S>
    },
    box ForallTyExpr<S> as Forall {
        raw vars: Vec<S::Sym>,
        ty: TyExpr<S>
    }
}

/*-----------------*\
|  Utility methods  |
\*-----------------*/

impl<S: Stage> From<Let<S>> for Expr<S> {
    fn from(value: Let<S>) -> Self {
        Self::Bind(Box::new(value))
    }
}

impl<S: Stage> From<Lambda<S>> for Expr<S> {
    fn from(value: Lambda<S>) -> Self {
        Self::Lambda(Box::new(value))
    }
}

impl<S: Stage> From<Application<S>> for Expr<S> {
    fn from(value: Application<S>) -> Self {
        Self::Apply(Box::new(value))
    }
}

impl<S: Stage> ExprData<S> {
    pub fn with<T: Stage>(&self, expr: T::ExprData) -> ExprData<T> {
        ExprData {
            node: self.node,
            expr
        }
    }
}

impl<S: Stage> Expr<S> {
    pub fn bind(binding: Let<S>) -> Self {
        Self::Bind(Box::new(binding))
    }

    pub fn lambda(lambda: Lambda<S>) -> Self {
        Self::Lambda(Box::new(lambda))
    }

    pub fn apply(application: Application<S>) -> Self {
        Self::Apply(Box::new(application))
    }

    pub fn if_else(if_else: IfElse<S>) -> Self {
        Self::If(Box::new(if_else))
    }
}
