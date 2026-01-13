use derivative::Derivative;

use crate::{ast::{Node, NodeData, visit::{Drive, Visitor}}, stage::Stage};

/*-------*\
|  Nodes  |
\*-------*/

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Root<S: Stage> {
    pub data: NodeData,
    pub items: Vec<Item<S>>,
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
    pub pattern: S::Pattern,
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
    pub cases: S::Cases,
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Clone(bound = ""))]
pub struct Case<S: Stage> {
    pub pattern: S::Pattern,
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

/*-----------------------*\
|  Trait implementations  |
\*-----------------------*/

impl<S: Stage + 'static> Drive for Root<S> {
    fn drive(&self, visitor: &mut dyn Visitor) {
        visitor.visit(&self.items);
    }
}

impl<S: Stage + 'static> Drive for Item<S> {
    fn drive(&self, visitor: &mut dyn Visitor) {
        match self {
            Item::Binding(binding) => visitor.visit(binding),
        }
    }
}

impl<S: Stage + 'static> Drive for Binding<S> {
    fn drive(&self, visitor: &mut dyn Visitor) {
        visitor.visit(&self.body);
    }
}

impl<S: Stage + 'static> Drive for Expr<S> {
    fn drive(&self, visitor: &mut dyn Visitor) {
        match self {
            Expr::Unit(unit) => visitor.visit(unit),
            Expr::Int(int) => visitor.visit(int),
            Expr::Bool(bool) => visitor.visit(bool),
            Expr::String(string) => visitor.visit(string),
            Expr::Var(var) => visitor.visit(var),
            Expr::Bind(binding) => visitor.visit(binding.as_ref()),
            Expr::Lambda(lambda) => visitor.visit(lambda.as_ref()),
            Expr::Apply(application) => visitor.visit(application.as_ref()),
            Expr::If(if_else) => visitor.visit(if_else.as_ref()),
        }
    }
}

impl<S: Stage + 'static> Drive for UnitExpr<S> {
    fn drive(&self, _: &mut dyn Visitor) {}
}

impl<S: Stage + 'static> Drive for IntExpr<S> {
    fn drive(&self, _: &mut dyn Visitor) {}
}

impl<S: Stage + 'static> Drive for BoolExpr<S> {
    fn drive(&self, _: &mut dyn Visitor) {}
}

impl<S: Stage + 'static> Drive for StringExpr<S> {
    fn drive(&self, _: &mut dyn Visitor) {}
}

impl<S: Stage + 'static> Drive for VarExpr<S> {
    fn drive(&self, _: &mut dyn Visitor) {}
}

impl<S: Stage + 'static> Drive for Let<S> {
    fn drive(&self, visitor: &mut dyn Visitor) {
        visitor.visit(&self.pattern);
        visitor.visit(&self.value);
        visitor.visit(&self.expr);
    }
}

impl<S: Stage + 'static> Drive for Lambda<S> {
    fn drive(&self, visitor: &mut dyn Visitor) {
        visitor.visit(&self.cases);
    }
}

impl<S: Stage + 'static> Drive for Application<S> {
    fn drive(&self, visitor: &mut dyn Visitor) {
        visitor.visit(&self.target);
        visitor.visit(&self.arg);
    }
}

impl<S: Stage + 'static> Drive for IfElse<S> {
    fn drive(&self, visitor: &mut dyn Visitor) {
        visitor.visit(&self.condition);
        visitor.visit(&self.if_true);
        visitor.visit(&self.if_false);
    }
}

impl<S: Stage + 'static> Drive for Case<S> {
    fn drive(&self, visitor: &mut dyn Visitor) {
        visitor.visit(&self.pattern);
        visitor.visit(&self.body);
    }
}

impl<S: Stage + 'static> Drive for Pattern<S> {
    fn drive(&self, visitor: &mut dyn Visitor) {
        match self {
            Pattern::Wildcard(wildcard) => visitor.visit(wildcard),
            Pattern::Var(var) => visitor.visit(var),
            Pattern::Unit(unit) => visitor.visit(unit),
            Pattern::Number(number) => visitor.visit(number),
            Pattern::Bool(bool) => visitor.visit(bool),
        }
    }
}

impl Drive for WildcardPattern {
    fn drive(&self, _: &mut dyn Visitor) {}
}

impl<S: Stage + 'static> Drive for VarPattern<S> {
    fn drive(&self, _: &mut dyn Visitor) {}
}

impl Drive for UnitPattern {
    fn drive(&self, _: &mut dyn Visitor) {}
}

impl Drive for NumberPattern {
    fn drive(&self, _: &mut dyn Visitor) {}
}

impl Drive for BoolPattern {
    fn drive(&self, _: &mut dyn Visitor) {}
}

impl<S: Stage + 'static> Node for Root<S> {
    fn node_data(&self) -> NodeData {
        self.data
    }
}

impl<S: Stage + 'static> Node for Item<S> {
    fn node_data(&self) -> NodeData {
        match self {
            Item::Binding(binding) => binding.node_data(),
        }
    }
}

impl<S: Stage + 'static> Node for Binding<S> {
    fn node_data(&self) -> NodeData {
        self.data
    }
}

impl<S: Stage + 'static> Node for Expr<S> {
    fn node_data(&self) -> NodeData {
        match self {
            Expr::Unit(unit) => unit.node_data(),
            Expr::Int(int) => int.node_data(),
            Expr::Bool(bool) => bool.node_data(),
            Expr::String(string) => string.node_data(),
            Expr::Var(var) => var.node_data(),
            Expr::Bind(binding) => binding.node_data(),
            Expr::Lambda(lambda) => lambda.node_data(),
            Expr::Apply(application) => application.node_data(),
            Expr::If(if_else) => if_else.node_data(),
        }
    }
}

impl<S: Stage + 'static> Node for UnitExpr<S> {
    fn node_data(&self) -> NodeData {
        self.data.node
    }
}

impl<S: Stage + 'static> Node for IntExpr<S> {
    fn node_data(&self) -> NodeData {
        self.data.node
    }
}

impl<S: Stage + 'static> Node for BoolExpr<S> {
    fn node_data(&self) -> NodeData {
        self.data.node
    }
}

impl<S: Stage + 'static> Node for StringExpr<S> {
    fn node_data(&self) -> NodeData {
        self.data.node
    }
}

impl<S: Stage + 'static> Node for VarExpr<S> {
    fn node_data(&self) -> NodeData {
        self.data.node
    }
}

impl<S: Stage + 'static> Node for Let<S> {
    fn node_data(&self) -> NodeData {
        self.data.node
    }
}

impl<S: Stage + 'static> Node for Lambda<S> {
    fn node_data(&self) -> NodeData {
        self.data.node
    }
}

impl<S: Stage + 'static> Node for Application<S> {
    fn node_data(&self) -> NodeData {
        self.data.node
    }
}

impl<S: Stage + 'static> Node for IfElse<S> {
    fn node_data(&self) -> NodeData {
        self.data.node
    }
}

impl<S: Stage + 'static> Node for Case<S> {
    fn node_data(&self) -> NodeData {
        self.data
    }
}

impl<S: Stage + 'static> Node for Pattern<S> {
    fn node_data(&self) -> NodeData {
        match self {
            Pattern::Wildcard(wildcard) =>  wildcard.node_data(),
            Pattern::Var(var) => var.node_data(),
            Pattern::Unit(unit) => unit.node_data(),
            Pattern::Number(number) => number.node_data(),
            Pattern::Bool(bool) => bool.node_data(),
        }
    }
}

impl Node for WildcardPattern {
    fn node_data(&self) -> NodeData {
        self.data
    }
}
impl<S: Stage + 'static> Node for VarPattern<S> {
    fn node_data(&self) -> NodeData {
        self.data
    }
}
impl Node for UnitPattern {
    fn node_data(&self) -> NodeData {
        self.data
    }
}
impl Node for NumberPattern {
    fn node_data(&self) -> NodeData {
        self.data
    }
}
impl Node for BoolPattern {
    fn node_data(&self) -> NodeData {
        self.data
    }
}
