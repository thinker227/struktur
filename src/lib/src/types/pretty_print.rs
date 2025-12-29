//! Pretty-printing for types.

use std::{char, collections::hash_map::HashMap, fmt::Write};

use crate::types::{Forall, FunctionType, MonoType, PolyType, Primitive, Repr, TypeVar, inference::MetaVar};

/// Pretty-prints a type.
pub fn pretty_print<P: PrettyPrint>(val: &P) -> String {
    let mut ctx = PrintCtx::new();
    pretty_print_with(val, &mut ctx)
}

/// Pretty-prints a type with a shared context.
pub fn pretty_print_with<P: PrettyPrint>(val: &P, ctx: &mut PrintCtx) -> String {
    let mut buf = String::new();
    val.pretty_print(&mut buf, ctx).unwrap();
    buf
}

/// Types which can be pretty-printed.
pub trait PrettyPrint {
    /// Appends the type to a buffer with a context.
    fn pretty_print(&self, buf: &mut String, ctx: &mut PrintCtx) -> std::fmt::Result;

    /// Whether the type is trivial and does not require parentheses in function parameter position.
    fn is_trivial(&self) -> bool {
        true
    }
}

/// A context for pretty-printing.
pub struct PrintCtx {
    var_names: HashMap<TypeVar, String>,
    meta_names: HashMap<MetaVar, String>,
}

impl PrintCtx {
    /// Creates a new context.
    pub fn new() -> Self {
        Self {
            var_names: HashMap::new(),
            meta_names: HashMap::new(),
        }
    }

    pub fn var_name(&mut self, var: TypeVar) -> &str {
        let next_index = self.var_names.len();
        self.var_names.entry(var)
            .or_insert_with(|| excel_column_name(next_index))
    }

    pub(super) fn meta_name(&mut self, var: MetaVar) -> &str {
        let next_index = self.meta_names.len();
        self.meta_names.entry(var)
            .or_insert_with(|| excel_column_name(next_index))
    }
}

fn excel_column_name(mut index: usize) -> String {
    let mut result = String::new();
    index += 1;

    while index > 0 {
        let m = (index - 1) % 26;
        let c = char::from_u32('a' as u32 + m as u32).unwrap();
        result.insert(0, c);
        index = (index - m) / 26;
    }

    result
}

impl PrettyPrint for Primitive {
    fn pretty_print(&self, buf: &mut String, _ctx: &mut PrintCtx) -> std::fmt::Result {
        match self {
            Primitive::Unit => write!(buf, "()"),
            Primitive::Int => write!(buf, "Int"),
            Primitive::Bool => write!(buf, "Bool"),
            Primitive::String => write!(buf, "String"),
        }
    }
}

impl PrettyPrint for TypeVar {
    fn pretty_print(&self, buf: &mut String, ctx: &mut PrintCtx) -> std::fmt::Result {
        let name = ctx.var_name(*self);
        write!(buf, "'{name}")
    }
}

impl<R: Repr> PrettyPrint for MonoType<R> {
    fn pretty_print(&self, buf: &mut String, ctx: &mut PrintCtx) -> std::fmt::Result {
        match self {
            MonoType::Primitive(primitive) => primitive.pretty_print(buf, ctx),
            MonoType::Function(function) => function.pretty_print(buf, ctx),
            MonoType::Var(var) => var.pretty_print(buf, ctx),
        }
    }

    fn is_trivial(&self) -> bool {
        !matches!(self, MonoType::Function(_))
    }
}

impl<R: Repr> PrettyPrint for FunctionType<R> {
    fn pretty_print(&self, buf: &mut String, ctx: &mut PrintCtx) -> std::fmt::Result {
        let parens = !self.param.is_trivial();

        if parens {
            write!(buf, "(")?;
        }
        self.param.pretty_print(buf, ctx)?;
        if parens {
            write!(buf, ")")?;
        }

        write!(buf, " -> ")?;

        self.ret.pretty_print(buf, ctx)?;

        Ok(())
    }
}

impl<Ty: PrettyPrint> PrettyPrint for PolyType<Ty> {
    fn pretty_print(&self, buf: &mut String, ctx: &mut PrintCtx) -> std::fmt::Result {
        match self {
            PolyType::Forall(forall) => forall.pretty_print(buf, ctx),
            PolyType::Type(ty) => ty.pretty_print(buf, ctx),
        }
    }
}

impl<Ty: PrettyPrint> PrettyPrint for Forall<Ty> {
    fn pretty_print(&self, buf: &mut String, ctx: &mut PrintCtx) -> std::fmt::Result {
        write!(buf, "∀")?;
        for var in &self.vars {
            write!(buf, " ")?;
            var.pretty_print(buf, ctx)?;
        }
        write!(buf, ". ")?;
        self.target.pretty_print(buf, ctx)?;
        Ok(())
    }
}

#[test]
fn foo() {
    use crate::{id::IdProvider, types::{Pruned, FunctionType}};

    let vars = IdProvider::new(TypeVar);
    let a = vars.next();
    let b = vars.next();

    let ty: Forall<FunctionType<Pruned>> = Forall {
        vars: vec![a, b],
        target: FunctionType {
            param: MonoType::function(
                MonoType::Var(a),
                MonoType::Var(b),
            ),
            ret: MonoType::function(
                MonoType::Var(a),
                MonoType::Var(b),
            ),
        }
    };
    println!("{}", pretty_print(&ty));

    let ty: Forall<FunctionType<Pruned>> = Forall {
        vars: vec![a, b],
        target: FunctionType {
            param: MonoType::Var(a),
            ret: MonoType::function(
                MonoType::Var(b),
                MonoType::Var(a)
            )
        },
    };
    println!("{}", pretty_print(&ty));
}
