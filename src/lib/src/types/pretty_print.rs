use std::{char, collections::hash_map::HashMap, fmt::Write};

use crate::types::{Forall, FunctionType, MonoType, PolyType, Primitive, Pruned, TypeVar};

pub fn pretty_print<P: PrettyPrint>(val: &P) -> String {
    let mut ctx = PrintCtx {
        var_names: HashMap::new(),
        buf: String::new()
    };
    val.pretty_print(&mut ctx).unwrap();
    ctx.buf
}

pub trait PrettyPrint {
    fn pretty_print(&self, ctx: &mut PrintCtx) -> std::fmt::Result;

    fn is_trivial(&self) -> bool {
        true
    }
}

pub struct PrintCtx {
    var_names: HashMap<TypeVar, String>,
    buf: String,
}

impl Write for PrintCtx {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.buf.push_str(s);
        Ok(())
    }
}

impl PrettyPrint for Primitive {
    fn pretty_print(&self, ctx: &mut PrintCtx) -> std::fmt::Result {
        match self {
            Primitive::Unit => write!(ctx, "()"),
            Primitive::Int => write!(ctx, "Int"),
            Primitive::Bool => write!(ctx, "Bool"),
            Primitive::String => write!(ctx, "String"),
        }
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

impl PrettyPrint for TypeVar {
    fn pretty_print(&self, ctx: &mut PrintCtx) -> std::fmt::Result {
        let next_index = ctx.var_names.len();
        let name = ctx.var_names.entry(*self)
            .or_insert_with(|| excel_column_name(next_index));

        // `ctx` is borrowed so have to use `buf` directly
        write!(ctx.buf, "'{}", name)
    }
}

impl PrettyPrint for MonoType<Pruned> {
// impl<R: Repr> PrettyPrint for MonoType<R>
// where R::RecTy: PrettyPrint
// {
    fn pretty_print(&self, ctx: &mut PrintCtx) -> std::fmt::Result {
        match self {
            MonoType::Primitive(primitive) => primitive.pretty_print(ctx),
            MonoType::Function(function) => function.pretty_print(ctx),
            MonoType::Var(var) => var.pretty_print(ctx),
        }
    }

    fn is_trivial(&self) -> bool {
        !matches!(self, MonoType::Function(_))
    }
}

impl PrettyPrint for FunctionType<Pruned> {
    fn pretty_print(&self, ctx: &mut PrintCtx) -> std::fmt::Result {
        let parens = !self.param.is_trivial();

        if parens {
            write!(ctx, "(")?;
        }
        self.param.pretty_print(ctx)?;
        if parens {
            write!(ctx, ")")?;
        }

        write!(ctx, " -> ")?;

        self.ret.pretty_print(ctx)?;

        Ok(())
    }
}

impl<Ty: PrettyPrint> PrettyPrint for PolyType<Ty> {
    fn pretty_print(&self, ctx: &mut PrintCtx) -> std::fmt::Result {
        match self {
            PolyType::Forall(forall) => forall.pretty_print(ctx),
            PolyType::Type(ty) => ty.pretty_print(ctx),
        }
    }
}

impl<Ty: PrettyPrint> PrettyPrint for Forall<Ty> {
    fn pretty_print(&self, ctx: &mut PrintCtx) -> std::fmt::Result {
        write!(ctx, "∀")?;
        for var in &self.vars {
            write!(ctx, " ")?;
            var.pretty_print(ctx)?;
        }
        write!(ctx, ". ")?;
        self.target.pretty_print(ctx)?;
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
