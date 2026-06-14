//! Pretty-printing types into a nice and readable format, primarily for use in diagnostics.

use std::{
    collections::HashMap,
    fmt::{self, Write as _},
};

use crate::{
    symbols::Symbols,
    types::{FunctionType, PrimitiveType, Ty, TypeVar},
};

use super::{MetaVar, MonoType, PolyType, excel_column_name};

/// A context for pretty-printing types.
pub struct PrintContext<'a> {
    meta_names: HashMap<MetaVar, usize>,
    inferred_var_names: HashMap<usize, usize>,
    symbols: &'a Symbols,
}

impl<'a> PrintContext<'a> {
    /// Constructs a new printing context.
    pub fn new(symbols: &'a Symbols) -> Self {
        Self {
            meta_names: HashMap::new(),
            inferred_var_names: HashMap::new(),
            symbols,
        }
    }

    /// Gets a new sequentially generated name for a unification variable.
    pub fn meta_name(&mut self, var: MetaVar) -> String {
        let count = self.meta_names.len();
        let index = *self.meta_names.entry(var).or_insert(count);
        excel_column_name(index)
    }

    /// Gets the explicit name of a type variable, or a new sequentially generated name.
    pub fn var_name(&mut self, var: TypeVar) -> String {
        match var {
            TypeVar::Declared(symbol) => self.symbols.get(symbol).name().to_owned(),
            // Todo: It would be nice to generate unique names for inferred type variables
            // which do not overlap with existing explicitly named type variables.
            TypeVar::Inferred(inferred) => {
                let count = self.inferred_var_names.len();
                let index = *self.inferred_var_names.entry(inferred).or_insert(count);
                excel_column_name(index)
            }
        }
    }
}

/// Formats a set of types into a pretty display string.
///
/// The types are all formatted using the same [PrintContext],
/// so things like meta variables will have sequential non-overlapping names.
pub fn pretty_print<const N: usize>(vals: [&dyn PrettyPrint; N], symbols: &Symbols) -> [String; N] {
    let mut ctx = PrintContext::new(symbols);
    pretty_print_with(vals, &mut ctx)
}

/// Formats a set of types into a pretty display string.
///
/// The types are all formatted using the passed-in [PrintContext],
/// so things like meta variables will have sequential non-overlapping names.
/// If the context is only needed for a single call to format a set of types,
/// [pretty_print] can be used instead which will create a one-shot context.
pub fn pretty_print_with<const N: usize>(
    vals: [&dyn PrettyPrint; N],
    ctx: &mut PrintContext,
) -> [String; N] {
    let mut result = Vec::with_capacity(N);

    for val in vals {
        let mut buf = String::new();
        val.print(&mut buf, ctx)
            .expect("failed to pretty print type");
        result.push(buf);
    }

    result.try_into().unwrap()
}

/// Trait for pretty-printing types.
pub trait PrettyPrint {
    /// Pretty-prints the value into the provided string buffer using the given context.
    fn print(&self, buf: &mut String, ctx: &mut PrintContext) -> fmt::Result;

    /// Returns whether the value is "trivial" and does *not* needs parentheses when in function parameter position.
    fn is_trivial(&self) -> bool {
        true
    }
}

impl PrettyPrint for PolyType {
    fn print(&self, buf: &mut String, ctx: &mut PrintContext) -> fmt::Result {
        match self {
            PolyType::Forall(Ty { ty: forall, .. }) => {
                write!(buf, "forall")?;
                for var in &forall.vars {
                    write!(buf, " ")?;
                    var.print(buf, ctx)?;
                }
                write!(buf, ". ")?;
                forall.generalized.print(buf, ctx)?;
            }

            PolyType::Type(ty) => {
                ty.print(buf, ctx)?;
            }
        }

        Ok(())
    }
}

impl PrettyPrint for MonoType {
    fn print(&self, buf: &mut String, ctx: &mut PrintContext) -> fmt::Result {
        match self {
            MonoType::Primitive(Ty { ty: prim, .. }) => prim.print(buf, ctx),
            MonoType::Function(Ty { ty: fun, .. }) => fun.print(buf, ctx),
            MonoType::Var(Ty { ty: var, .. }) => var.print(buf, ctx),
            MonoType::Meta(var) => var.print(buf, ctx),
            MonoType::Hole => write!(buf, "_"), // Todo: Not sure about this.
        }
    }
}

impl PrettyPrint for PrimitiveType {
    fn print(&self, buf: &mut String, _ctx: &mut PrintContext) -> fmt::Result {
        match self {
            PrimitiveType::Unit => write!(buf, "()"),
            PrimitiveType::Int => write!(buf, "Int"),
            PrimitiveType::Bool => write!(buf, "Bool"),
            PrimitiveType::String => write!(buf, "String"),
        }
    }
}

impl PrettyPrint for FunctionType {
    fn print(&self, buf: &mut String, ctx: &mut PrintContext) -> fmt::Result {
        if self.param.is_trivial() {
            self.param.print(buf, ctx)?;
        } else {
            write!(buf, "(")?;
            self.param.print(buf, ctx)?;
            write!(buf, ")")?;
        }

        write!(buf, " -> ")?;

        self.ret.print(buf, ctx)?;

        Ok(())
    }

    fn is_trivial(&self) -> bool {
        false
    }
}

impl PrettyPrint for TypeVar {
    fn print(&self, buf: &mut String, ctx: &mut PrintContext) -> fmt::Result {
        write!(buf, "'{}", ctx.var_name(*self))?;
        Ok(())
    }
}

impl PrettyPrint for MetaVar {
    fn print(&self, buf: &mut String, ctx: &mut PrintContext) -> fmt::Result {
        write!(buf, "${}", ctx.meta_name(self.clone()))?;
        Ok(())
    }
}
