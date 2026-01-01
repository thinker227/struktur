use derivative::Derivative;

use crate::{ast::NodeData, stage::Stage};

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Root<S: Stage>(pub Vec<Item<S>>, pub NodeData<S>);

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Item<S: Stage>(pub ItemVal<S>, pub NodeData<S>);

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub enum ItemVal<S: Stage> {
    Binding(Binding<S>),
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Binding<S: Stage> {
    pub symbol: S::Sym,
    pub body: Expr<S>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Expr<S: Stage>(pub ExprVal<S>, pub S::ExprData, pub NodeData<S>);

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub enum ExprVal<S: Stage> {
    Unit,
    Int(u64),
    Bool(bool),
    String(String),
    Var(S::Sym),
    Bind(Box<Let<S>>),
    Lambda(Box<Lambda<S>>),
    Apply(Box<Application<S>>),
    If(Box<IfElse<S>>),
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Let<S: Stage> {
    pub pattern: Pattern<S>,
    pub value: Expr<S>,
    pub expr: Expr<S>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Application<S: Stage> {
    pub target: Expr<S>,
    pub arg: Expr<S>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct IfElse<S: Stage> {
    pub condition: Expr<S>,
    pub if_true: Expr<S>,
    pub if_false: Expr<S>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Lambda<S: Stage> {
    pub cases: Vec<Case<S>>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Case<S: Stage> {
    pub pattern: Pattern<S>,
    pub body: Expr<S>,
    pub data: NodeData<S>,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Pattern<S: Stage>(pub PatternVal<S>, pub NodeData<S>);

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub enum PatternVal<S: Stage> {
    Wildcard,
    Var(S::Sym),
    Unit,
    Number(u64),
    Bool(bool),
}
