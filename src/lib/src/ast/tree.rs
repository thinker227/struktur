use derivative::Derivative;

use crate::{ast::{Node, NodeData, ToNodeData, visit::{Drive, Visitor}}, stage::Stage, struct_node, enum_node};

mod macros;

/*-------*\
|  Nodes  |
\*-------*/

struct_node! {
    Root<S> where
    items: Vec<Item<S>>
    => items
}

enum_node! {
    Item<S> where
    Binding<S> as Binding {
        symbol: S::Sym,
        ty: Option<S::TyAnn>,
        body: Expr<S>
        => ty, body
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
        val: u64
    },
    BoolExpr<S> as Bool {
        data: ExprData<S>,
        val: bool
    },
    StringExpr<S> as String {
        data: ExprData<S>,
        val: String
    },
    VarExpr<S> as Var {
        data: ExprData<S>,
        symbol: S::Sym
    },
    Let<S> as Bind use Box {
        data: ExprData<S>,
        pattern: S::Pattern,
        value: Expr<S>,
        expr: Expr<S>
        => pattern, value, expr
    },
    Lambda<S> as Lambda use Box {
        data: ExprData<S>,
        cases: S::Cases
        => cases
    },
    Application<S> as Apply use Box {
        data: ExprData<S>,
        target: Expr<S>,
        arg: Expr<S>
        => target, arg
    },
    IfElse<S> as If use Box {
        data: ExprData<S>,
        condition: Expr<S>,
        if_true: Expr<S>,
        if_false: Expr<S>
        => condition, if_true, if_false
    },
    TyAnnExpr<S> as TyAnn use Box {
        expr: Expr<S>,
        ty: S::TyAnnBranch
        => expr, ty
    }
}

struct_node! {
    Case<S> where
    pattern: S::Pattern,
    body: Expr<S>
    => pattern, body
}

enum_node! {
    Pattern<S> where
    WildcardPattern as Wildcard {},
    VarPattern<S> as Var {
        symbol: S::Sym
    },
    UnitPattern as Unit {},
    NumberPattern as Number {
        val: u64
    },
    BoolPattern as Bool {
        val: bool
    },
    TyAnnPattern<S> as TyAnn use Box {
        pat: Pattern<S>,
        ty: S::TyAnnBranch
        => pat, ty
    }
}

enum_node! {
    TyExpr<S> where
    IntTyExpr as Int {},
    BoolTyExpr as Bool {},
    StringTyExpr as String {},
    VarTyExpr<S> as Var {
        symbol: S::Sym
    },
    FunctionTyExpr<S> as Function use Box {
        param: TyExpr<S>,
        ret: TyExpr<S>
        => param, ret
    },
    ForallTyExpr<S> as Forall use Box {
        vars: Vec<S::Sym>,
        ty: TyExpr<S>
        => ty
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
