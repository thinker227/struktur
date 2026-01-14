use quote::ToTokens;
use syn::{Ident, Type, parse_macro_input};

mod parse;
mod write;

/// Generates node type as a struct.
///
/// # Syntax
/// ```
/// struct_node! {
///     // Define the name as well as an optional stage type parameter:
///     Name where
///     // or:
///     Name<S> where
///
///     // Optional! Override the default type of `data` (`NodeData`):
///     data: DataType,
///
///     // Define the node's fields:
///     // Use `raw` to annotate that a field should not be visited.
///     field_1: FieldType,
///     field_2: FieldType,
///     raw field_3: u32
/// }
/// ```
#[proc_macro]
pub fn struct_node(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    parse_macro_input!(input as StructNode)
        .into_token_stream().into()
}

/// Generates a node type as an enum.
///
/// # Syntax
/// ```
/// enum_node! {
///     // Define the name as well as an optional stage type parameter:
///     Name where
///     // or:
///     Name<S> where
///
///     // Define the node's variants:
///
///     // Each variant can optionally specify a stage type parameter,
///     // as well as whether the variant should be boxed.
///     // Note that a stage type parameter can only be specified
///     // if the enum itself specifies one.
///     VariantNode as Variant
///     VariantNode<S> as Variant
///     box VariantNode as Variant
///     box VariantNode<S> as Variant
///
///     // An actual variant:
///     VariantNode as Variant {
///         // Optional! Override the default type of `data` (`NodeData`):
///         data: DataType,
///
///         // Define the variant's fields:
///         // Use `raw` to annotate that a field should not be visited.
///         field_1: FieldType,
///         field_2: FieldType,
///         raw field_3: u32
///     }
/// }
/// ```
#[proc_macro]
pub fn enum_node(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    parse_macro_input!(input as EnumNode)
        .into_token_stream().into()
}

struct Stage(Option<Ident>);

struct StructNode {
    name: Ident,
    stage: Stage,
    data_ty: Option<Type>,
    fields: Vec<Field>,
}

struct Field {
    name: Ident,
    is_raw: bool,
    ty: Type,
}

struct EnumNode {
    name: Ident,
    stage: Stage,
    variants: Vec<Variant>,
}

struct Variant {
    alias: Ident,
    boxed: bool,
    kind: VariantKind,
}

enum VariantKind {
    Def(StructNode),
    Type(Type),
}
