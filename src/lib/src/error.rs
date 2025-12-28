use crate::{parse::ParseError, symbols::SymbolResError, types::TypeCheckError};

#[derive(Debug, thiserror::Error, miette::Diagnostic)]
pub enum CompileError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    Parse(#[from] ParseError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    SymbolRes(#[from] SymbolResError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    TypeCheck(#[from] TypeCheckError),
}
