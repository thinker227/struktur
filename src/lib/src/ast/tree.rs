use derivative::Derivative;

use crate::{ast::{Node, NodeData}, stage::Stage};

/*-------*\
|  Nodes  |
\*-------*/

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Root<S: Stage>(pub Vec<Item<S>>, pub NodeData);

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub enum Item<S: Stage> {
    Binding(Binding<S>),
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Binding<S: Stage> {
    pub data: NodeData,
    pub symbol: S::Sym,
    pub body: Expr<S>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct ExprData<S: Stage> {
    pub node: NodeData,
    pub expr: S::ExprData,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub enum Expr<S: Stage> {
    Unit(UnitExpr<S>),
    Int(IntExpr<S>),
    Bool(BoolExpr<S>),
    String(StringExpr<S>),
    Var(VarExpr<S>),
    Bind(Box<Let<S>>),
    Lambda(Box<Lambda<S>>),
    Apply(Box<Application<S>>),
    If(Box<IfElse<S>>),
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct UnitExpr<S: Stage> {
    pub data: ExprData<S>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct IntExpr<S: Stage> {
    pub data: ExprData<S>,
    pub val: u64,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct BoolExpr<S: Stage> {
    pub data: ExprData<S>,
    pub val: bool,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct StringExpr<S: Stage> {
    pub data: ExprData<S>,
    pub val: String,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct VarExpr<S: Stage> {
    pub data: ExprData<S>,
    pub symbol: S::Sym,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Let<S: Stage> {
    pub data: ExprData<S>,
    pub pattern: Pattern<S>,
    pub value: Expr<S>,
    pub expr: Expr<S>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Application<S: Stage> {
    pub data: ExprData<S>,
    pub target: Expr<S>,
    pub arg: Expr<S>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct IfElse<S: Stage> {
    pub data: ExprData<S>,
    pub condition: Expr<S>,
    pub if_true: Expr<S>,
    pub if_false: Expr<S>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Lambda<S: Stage> {
    pub data: ExprData<S>,
    pub cases: Vec<Case<S>>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Case<S: Stage> {
    pub pattern: Pattern<S>,
    pub body: Expr<S>,
    pub data: NodeData,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub enum Pattern<S: Stage> {
    Wildcard(WildcardPattern),
    Var(VarPattern<S>),
    Unit(UnitPattern),
    Number(NumberPattern),
    Bool(BoolPattern),
}

#[derive(Debug, Clone, Copy)]
pub struct WildcardPattern {
    pub data: NodeData,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct VarPattern<S: Stage> {
    pub data: NodeData,
    pub symbol: S::Sym,
}

#[derive(Debug, Clone, Copy)]
pub struct UnitPattern {
    pub data: NodeData,
}

#[derive(Debug, Clone, Copy)]
pub struct NumberPattern {
    pub data: NodeData,
    pub val: u64,
}

#[derive(Debug, Clone, Copy)]
pub struct BoolPattern {
    pub data: NodeData,
    pub val: bool,
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

/*----------------------------*\
|  Trait implementations  |
\*----------------------------*/

impl<S: Stage + 'static> Node for Root<S> {
    type S = S;

    fn node_data(&self) -> NodeData {
        self.1
    }
}

impl<S: Stage + 'static> Node for Item<S> {
    type S = S;

    fn node_data(&self) -> NodeData {
        match self {
            Item::Binding(binding) => binding.data,
        }
    }
}

impl<S: Stage + 'static> Node for Expr<S> {
    type S = S;

    fn node_data(&self) -> NodeData {
        match self {
            Expr::Unit(unit) => unit.data.node,
            Expr::Int(int) => int.data.node,
            Expr::Bool(bool) => bool.data.node,
            Expr::String(string) => string.data.node,
            Expr::Var(var) => var.data.node,
            Expr::Bind(binding) => binding.data.node,
            Expr::Lambda(lambda) => lambda.data.node,
            Expr::Apply(application) => application.data.node,
            Expr::If(if_else) => if_else.data.node,
        }
    }
}

impl<S: Stage + 'static> Node for Case<S> {
    type S = S;

    fn node_data(&self) -> NodeData {
        self.data
    }
}

impl<S: Stage + 'static> Node for Pattern<S> {
    type S = S;

    fn node_data(&self) -> NodeData {
        match self {
            Pattern::Wildcard(wildcard) =>  wildcard.data,
            Pattern::Var(var) => var.data,
            Pattern::Unit(unit) => unit.data,
            Pattern::Number(number) => number.data,
            Pattern::Bool(bool) => bool.data,
        }
    }
}
