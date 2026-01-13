/// Expands to one of two different branches depending on whether a sequence of tokens is empty or not.
///
/// This macro takes three arguments:
/// - The "condition" to branch on.
/// - The "true" branch which the macro expands to if the condition is non-empty.
/// - The "false" branch which the macro expands to if the condition *is* empty.
#[macro_export]
macro_rules! if_else {
    (($($target:tt)+) ($($if_true:tt)*) ($($if_false:tt)*)) => {
        $($if_true)*
    };

    (() ($($if_true:tt)*) ($($if_false:tt)*)) => {
        $($if_false)*
    };
}

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
///     field_1: FieldType,
///     field_2: FieldType,
///     field_3: FieldType
///
///     // Optional! Define the fields to drive a visitor through:
///     => field_1, field_3
/// }
/// ```
#[macro_export]
macro_rules! struct_node {
    (
        $name:ident$(<$stage:ident>)? where
        data: $data:ty
        $(,$field:ident: $field_ty:ty)*
        $(=> $drive_head:ident $(, $drive:ident)*)?
    ) => {
        // Struct definition

        pub struct $name$(<$stage: Stage>)? {
            pub data: $data,
            $(pub $field: $field_ty),*
        }

        // Trait impls

        impl$(<$stage: Stage>)? ToNodeData for $name$(<$stage>)? {
            fn node_data(&self) -> NodeData {
                self.data.node_data()
            }
        }

        impl$(<$stage: Stage + 'static>)? Node for $name$(<$stage>)? {}

        impl$(<$stage: Stage + 'static>)? Drive for $name$(<$stage>)? {
            #[allow(unused_variables)]
            fn drive(&self, visitor: &mut dyn Visitor) {
                $(
                    visitor.visit(&self.$drive_head);
                    $( visitor.visit(&self.$drive); )*
                )?
            }
        }

        impl$(<$stage: Stage>)? Clone for $name$(<$stage>)? {
            #[allow(clippy::clone_on_copy)]
            fn clone(&self) -> Self {
                Self {
                    data: self.data.clone(),
                    $( $field: self.$field.clone() ),*
                }
            }
        }

        impl$(<$stage: Stage>)? std::fmt::Debug for $name$(<$stage>)? {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_struct(stringify!($name))
                    .field("data", &self.data)
                    $(.field(stringify!($field), &self.$field))*
                    .finish()
            }
        }
    };

    // Secondary arm to allow defaulting `data` to be `NodeData`.
    (
        $name:ident$(<$stage:ident>)? where
        $($field:ident: $field_ty:ty),*
        $(=> $drive_head:ident $(, $drive:ident)*)?
    ) => {
        struct_node! {
            $name$(<$stage>)? where
            data: NodeData
            $(, $field: $field_ty)*
            $(=> $drive_head $(, $drive)*)?
        }
    }
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
///     // as well as a wrapper type.
///     VariantNode as Variant
///     VariantNode as Variant use Box
///     VariantNode<S> as Variant
///     VariantNode<S> as Variant use Box
///
///     // An actual variant:
///     VariantNode as Variant {
///         // Optional! Override the default type of `data` (`NodeData`):
///
///         // Define the variant's fields:
///         field_1: FieldType,
///         field_2: FieldType,
///         field_3: FieldType
///
///         // Optional! Define the fields to drive a visitor through:
///         => field_1, field_3
///     }
/// }
/// ```
#[macro_export]
macro_rules! enum_node {
    (
        $name:ident$(<$stage:ident>)? where
        $($variant_name:ident$(<$variant_stage:ident>)? as $variant:ident $(use $wrapper:ident)? {
            $($field:ident: $field_ty:ty),*
            $(=> $drive_head:ident $(, $drive:ident)*)?
        }),*
    ) => {
        // Enum definition

        pub enum $name$(<$stage: Stage>)? {
            $(
                // Branch based on whether `wrapper` is non-empty in order to
                // enclose the variant type in `<>` if a wrapper type is specified.
                $variant($crate::if_else!(
                    ($($wrapper)?)
                    ($($wrapper)?<$variant_name$(<$variant_stage>)?>)
                    ($variant_name$(<$variant_stage>)?)
                ))
            ),*
        }

        // Trait impls

        impl$(<$stage: Stage>)? ToNodeData for $name$(<$stage>)? {
            fn node_data(&self) -> NodeData {
                match self {
                    $(Self::$variant(x) => x.node_data()),*
                }
            }
        }

        impl$(<$stage: Stage + 'static>)? Node for $name$(<$stage>)? {}

        impl$(<$stage: Stage + 'static>)? Drive for $name$(<$stage>)? {
            #[allow(unused_variables)]
            fn drive(&self, visitor: &mut dyn Visitor) {
                match self {
                    $(
                        // Branch on whether `wrapper` is non-empty in order to
                        // use `x.as_ref()` instead of just `x` is a wrapper type is specified.
                        Self::$variant(x) => $crate::if_else!(
                            ($($wrapper)?)
                            (visitor.visit(x.as_ref()))
                            (visitor.visit(x))
                        )
                    ),*
                }
            }
        }

        impl$(<$stage: Stage>)? Clone for $name$(<$stage>)? {
            #[allow(clippy::clone_on_copy)]
            fn clone(&self) -> Self {
                match self {
                    $(Self::$variant(x) => Self::$variant(x.clone())),*
                }
            }
        }

        impl$(<$stage: Stage>)? std::fmt::Debug for $name$(<$stage>)? {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    $(
                        Self::$variant(x) => f
                            .debug_tuple(stringify!($variant))
                            .field(x)
                            .finish()
                    ),*
                }
            }
        }

        // Sub-nodes

        // Use `struct_node` to define the structs for each variant.
        $(struct_node! {
            $variant_name$(<$variant_stage>)? where
            $($field: $field_ty),*
            $(=> $drive_head $(, $drive)*)?
        })*
    };
}
