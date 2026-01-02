use derivative::Derivative;

use crate::{ast::{Node, NodeData}, stage::Stage};

/*-------*\
|  Nodes  |
\*-------*/

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

/*-----------------*\
|  Utility methods  |
\*-----------------*/

impl<S: Stage> From<Let<S>> for ExprVal<S> {
    fn from(value: Let<S>) -> Self {
        Self::Bind(Box::new(value))
    }
}

impl<S: Stage> From<Lambda<S>> for ExprVal<S> {
    fn from(value: Lambda<S>) -> Self {
        Self::Lambda(Box::new(value))
    }
}

impl<S: Stage> From<Application<S>> for ExprVal<S> {
    fn from(value: Application<S>) -> Self {
        Self::Apply(Box::new(value))
    }
}

impl<S: Stage> ExprVal<S> {
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

    fn node_data(&self) -> &NodeData<Self::S> {
        &self.1
    }
}

impl<S: Stage + 'static> Node for Item<S> {
    type S = S;

    fn node_data(&self) -> &NodeData<Self::S> {
        &self.1
    }
}

impl<S: Stage + 'static> Node for Expr<S> {
    type S = S;

    fn node_data(&self) -> &NodeData<Self::S> {
        &self.2
    }
}

impl<S: Stage + 'static> Node for Case<S> {
    type S = S;

    fn node_data(&self) -> &NodeData<Self::S> {
        &self.data
    }
}

impl<S: Stage + 'static> Node for Pattern<S> {
    type S = S;

    fn node_data(&self) -> &NodeData<Self::S> {
        &self.1
    }
}
