use crate::{ast::{self, AsNode, visit::{Drive, Visitor}}, stage::Sem};

/// A compiled pattern decision tree.
#[derive(Debug, Clone)]
pub struct Pattern {

}

impl AsNode for Pattern {}

impl Drive for Pattern {
    fn drive(&self, _: &mut dyn Visitor) {}
}

/// Compiles a semantically resolved pattern into a decision tree.
pub fn compile_pattern(pattern: &ast::Pattern<Sem>) -> Pattern {
    todo!()
}
