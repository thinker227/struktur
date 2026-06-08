use ariadne::Label;

use crate::{
    diagnostic::{Category, Code, Diagnostic},
    text::TextLocation,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
enum TypeErrorCode {
    UnusedTypeVariable = 1,
    ForallProhibited = 2,
}

impl From<TypeErrorCode> for u16 {
    fn from(value: TypeErrorCode) -> Self {
        value as u16
    }
}

fn code(val: TypeErrorCode) -> Code {
    Code::new(Category::TypeCheck, val.into())
}

pub fn unused_type_variable(
    var_name: &str,
    var_span: TextLocation,
    ty_span: TextLocation,
) -> Diagnostic {
    Diagnostic::error(
        code(TypeErrorCode::UnusedTypeVariable),
        var_span,
        |report| {
            report
            .with_message(format!("The type variable `'{var_name}` declared in a forall generalization is not used within the generalized type"))
            .with_label(Label::new(var_span).with_message(format!("`'{var_name}` declared here")))
            .with_label(Label::new(ty_span).with_message(format!("`'{var_name}` has to be used within this type")))
        },
    )
}

pub fn forall_prohibited() -> Diagnostic {
    todo!()
    // Diagnostic::error(
    //     code(TypeErrorCode::ForallProhibited),
    //     forall_span,
    //     |report| {
    //         report.with_message("Forall generalizations are not allowed to be nested within other types, nor to be annotated as the type of an expression")
    //         .with_label(Label::new(forall_span).with_message("This forall is not allowed"))
    //     },
    // )
}
