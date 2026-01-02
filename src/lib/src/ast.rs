//! Abstract syntax tree and nodes.

mod container;
mod tree;
pub mod visit;

use std::any::Any;

use derivative::Derivative;
use crate::{ast::container::RootContainer, id::Id, stage::Stage, text_span::TextSpan};

pub use self::tree::*;

#[derive(Derivative)]
#[derivative(Debug(bound = ""))]
pub struct Ast<S: Stage> {
    container: RootContainer<S>,
    symbols: S::Syms,
}

impl<S: Stage + 'static> Ast<S> {
    pub fn new(root: Root<S>, symbols: S::Syms) -> Self {
        Self {
            container: RootContainer::new(root),
            symbols
        }
    }

    pub fn root(&self) -> &Root<S> {
        self.container.root()
    }

    pub fn symbols(&self) -> &S::Syms {
        &self.symbols
    }

    pub fn get_node(&self, id: NodeId) -> &dyn Node<S = S> {
        self.container.get_node(id)
    }

    pub fn get_node_as<N: Node<S = S>>(&self, id: NodeId) -> Option<&N> {
        (self.get_node(id) as &dyn Any).downcast_ref()
    }
}

/// An ID for a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct NodeId(pub Id);

#[derive(Debug, Clone, Copy)]
pub struct NodeData {
    pub span: TextSpan,
    pub id: NodeId,
}

/// An AST node type.
pub trait Node: Any {
    /// The stage of the node.
    type S: Stage;

    /// Gets the node data for the node.
    fn node_data(&self) -> NodeData;

    /// Gets the ID for the node.
    fn id(&self) -> NodeId {
        self.node_data().id
    }

    fn span(&self) -> TextSpan {
        self.node_data().span
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExprDataBundle<'a, S: Stage>(pub &'a S::ExprData, pub NodeData);

#[allow(unused_variables)]
pub trait Visitor {
    type S: Stage;

    fn root(&mut self, root: &Root<Self::S>) {
        for item in &root.0 {
            self.item(item);
        }
    }

    fn item(&mut self, item: &Item<Self::S>) {
        match &item.0 {
            ItemVal::Binding(binding) => self.binding(binding, item.1),
        }
    }

    fn binding(&mut self, binding: &Binding<Self::S>, node_data: NodeData) {
        self.expr(&binding.body);
    }

    fn expr(&mut self, expr: &Expr<Self::S>) {
        default_visit_expr(self, expr);
    }

    fn unit_expr(&mut self, data: ExprDataBundle<'_, Self::S>) {}

    fn int_expr(&mut self, value: u64, data: ExprDataBundle<'_, Self::S>) {}

    fn bool_expr(&mut self, value: bool, data: ExprDataBundle<'_, Self::S>) {}

    fn string_expr(&mut self, value: &str, data: ExprDataBundle<'_, Self::S>) {}

    fn var_expr(&mut self, symbol: &<Self::S as Stage>::Sym, data: ExprDataBundle<'_, Self::S>) {}

    fn bind_expr(&mut self, binding: &Let<Self::S>, data: ExprDataBundle<'_, Self::S>) {
        self.pattern(&binding.pattern);
        self.expr(&binding.value);
        self.expr(&binding.expr);
    }

    fn apply_expr(&mut self, application: &Application<Self::S>, data: ExprDataBundle<'_, Self::S>) {
        self.expr(&application.target);
        self.expr(&application.arg);
    }

    fn if_else_expr(&mut self, if_else: &IfElse<Self::S>, data: ExprDataBundle<'_, Self::S>) {
        self.expr(&if_else.condition);
        self.expr(&if_else.if_true);
        self.expr(&if_else.if_false);
    }

    fn lambda_expr(&mut self, lambda: &Lambda<Self::S>, data: ExprDataBundle<'_, Self::S>) {
        for case in &lambda.cases {
            self.case(case);
        }
    }

    fn case(&mut self, case: &Case<Self::S>) {
        self.pattern(&case.pattern);
        self.expr(&case.body);
    }

    fn pattern(&mut self, pattern: &Pattern<Self::S>) {
        default_visit_pattern(self, pattern);
    }

    fn wildcard_pattern(&mut self, data: NodeData) {}

    fn var_pattern(&mut self, var: &<Self::S as Stage>::Sym, data: NodeData) {}

    fn unit_pattern(&mut self, data: NodeData) {}

    fn number_pattern(&mut self, val: u64, data: NodeData) {}

    fn bool_pattern(&mut self, val: bool, data: NodeData) {}
}

pub fn default_visit_expr<V: Visitor + ?Sized>(visitor: &mut V, expr: &Expr<V::S>) {
    let data = ExprDataBundle(&expr.1, expr.2);
    match &expr.0 {
        ExprVal::Unit => visitor.unit_expr(data),
        ExprVal::Int(value) => visitor.int_expr(*value, data),
        ExprVal::Bool(value) => visitor.bool_expr(*value, data),
        ExprVal::String(value) => visitor.string_expr(value, data),
        ExprVal::Var(symbol) => visitor.var_expr(symbol, data),
        ExprVal::Bind(binding) => visitor.bind_expr(binding, data),
        ExprVal::Lambda(lambda) => visitor.lambda_expr(lambda, data),
        ExprVal::Apply(application) => visitor.apply_expr(application, data),
        ExprVal::If(if_else) => visitor.if_else_expr(if_else, data),
    }
}

pub fn default_visit_pattern<V: Visitor + ?Sized>(visitor: &mut V, pattern: &Pattern<V::S>) {
    let data = &pattern.1;
    match &pattern.0 {
        PatternVal::Wildcard => visitor.wildcard_pattern(*data),
        PatternVal::Var(var) => visitor.var_pattern(var, *data),
        PatternVal::Unit => visitor.unit_pattern(*data),
        PatternVal::Number(val) => visitor.number_pattern(*val, *data),
        PatternVal::Bool(val) => visitor.bool_pattern(*val, *data),
    }
}
