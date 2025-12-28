use std::{collections::hash_map::HashMap, fmt::{self, Write}};

use crate::{cps::{Atomic, Binding, Complex, Continuation, Cps, CpsSymbol}, symbols::Symbol};

#[derive(Debug, Clone, Copy)]
enum ComplexContext {
    TopLevel(Symbol),
    Lambda,
}

struct Codegen {
    out: String,
    names: HashMap<CpsSymbol, String>,
    cont_names: HashMap<Continuation, String>,
}

impl Write for Codegen {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.out.push_str(s);
        Ok(())
    }
}

impl Codegen {
    pub fn new() -> Self {
        Self {
            out: String::new(),
            names: HashMap::new(),
            cont_names: HashMap::new()
        }
    }

    fn name(&mut self, symbol: CpsSymbol) -> &str {
        let x = self.names.len();
        self.names.entry(symbol).or_insert_with(
            || format!("s{}", x)
        )
    }

    fn cont_name(&mut self, cont: Continuation) -> &str {
        let x = self.names.len();
        self.cont_names.entry(cont).or_insert_with(
            || format!("c{}", x)
        )
    }

    pub fn header(&mut self) -> fmt::Result {
        write!(self, "{}", include_str!("./header.js"))
    }

    pub fn binding(&mut self, value: &Binding) -> fmt::Result {
        let name = self.name(CpsSymbol::Symbol(value.symbol)).to_owned();
        write!(self, "let {name};")?;
        self.complex(&value.value, ComplexContext::TopLevel(value.symbol))?;

        Ok(())
    }

    fn complex(&mut self, value: &Complex, ctx: ComplexContext) -> fmt::Result {
        match value {
            Complex::Call(target, arg, cont) => {
                match ctx {
                    ComplexContext::TopLevel(symbol) => {
                        let name = self.name(CpsSymbol::Symbol(symbol)).to_owned();
                        write!(self, "{name}=run(thunk(")?;
                    }
                    ComplexContext::Lambda => write!(self, "return thunk(")?
                }
                self.atomic(target)?;
                write!(self, ",")?;
                self.atomic(arg)?;
                if let Some(cont) = cont {
                    write!(self, ",")?;
                    self.atomic(cont)?;
                }
                match ctx {
                    ComplexContext::TopLevel(_) => write!(self, "));")?,
                    ComplexContext::Lambda => write!(self, ");")?,
                }
            }
            Complex::Return(value) => {
                // write!(self, "return ")?;
                match ctx {
                    ComplexContext::TopLevel(symbol) => {
                        let name = self.name(CpsSymbol::Symbol(symbol)).to_owned();
                        write!(self, "{name}=")?;
                    }
                    ComplexContext::Lambda => write!(self, "return ")?
                }
                self.atomic(value)?;
                write!(self, ";")?;
            }
            Complex::Let(binding) => {
                let name = self.name(CpsSymbol::Symbol(binding.symbol)).to_owned();
                write!(self, "const {name}=")?;
                self.atomic(&binding.value)?;
                write!(self, ";")?;
                self.complex(&binding.expr, ctx)?;
            }
            Complex::If(if_else) => {
                write!(self, "if(")?;
                self.atomic(&if_else.condition)?;
                write!(self, "){{")?;
                self.complex(&if_else.if_true, ctx)?;
                write!(self, "}}else{{")?;
                self.complex(&if_else.if_false, ctx)?;
                write!(self, "}}")?;
            }
        }

        Ok(())
    }

    fn atomic(&mut self, value: &Atomic) -> fmt::Result {
        match value {
            Atomic::Unit => {
                write!(self, "null")?;
            }
            Atomic::Int(x) => {
                write!(self, "{x}")?;
            }
            Atomic::Bool(x) => {
                write!(self, "{x}")?;
            }
            Atomic::String(s) => {
                write!(self, "\"{s}\"")?;
            }
            Atomic::Var(symbol) => {
                let name = self.name(*symbol).to_owned();
                write!(self, "{name}")?;
            }
            Atomic::Cont(continuation) => {
                let name = self.cont_name(*continuation).to_owned();
                write!(self, "{name}")?;
            }
            Atomic::Lambda(lambda) => {
                let param_name = self.name(lambda.param).to_owned();
                write!(self, "({param_name}")?;
                if let Some(cont) = lambda.cont {
                    let cont_name = self.cont_name(cont).to_owned();
                    write!(self, ",{cont_name}")?;
                }
                write!(self, ")=>{{")?;
                self.complex(&lambda.body, ComplexContext::Lambda)?;
                write!(self, "}}")?;
            }
        }

        Ok(())
    }
}

pub fn emit(cps: &Cps) -> String {
    let mut codegen = Codegen::new();
    codegen.header().unwrap();

    for binding in cps.bindings.values() {
        codegen.binding(binding).unwrap();
    }

    writeln!(codegen).unwrap();

    codegen.out
}
