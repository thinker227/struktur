use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

use crate::{EnumNode, Field, Stage, StructNode, Variant, VariantKind};

impl Stage {
    fn use_site(&self) -> TokenStream {
        match &self.0 {
            Some(name) => quote! { <#name> },
            None => quote! {}
        }
    }

    fn def_site(&self) -> TokenStream {
        match &self.0 {
            Some(name) => quote! { <#name: Stage> },
            None => quote! {}
        }
    }

    fn def_site_static(&self) -> TokenStream {
        match &self.0 {
            Some(name) => quote! { <#name: Stage + 'static> },
            None => quote! {}
        }
    }
}

impl ToTokens for StructNode {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let StructNode { name, stage, data_ty, fields } = self;

        let stage_use = stage.use_site();
        let stage_def = stage.def_site();
        let stage_def_static = stage.def_site_static();

        let name_string = name.to_string();

        let field_names = fields.iter()
            .map(|field| &field.name)
            .collect::<Vec<_>>();

        let field_strings = fields.iter()
            .map(|field| field.name.to_string());

        let drive_fields = fields.iter()
            .filter(|field| !field.is_raw)
            .map(|field| &field.name);

        let data_ty = match data_ty {
            Some(ty) => quote! { #ty },
            None => quote! { NodeData },
        };

        tokens.extend(quote! {
            pub struct #name #stage_def {
                pub data: #data_ty,
                #(#fields),*
            }

            impl #stage_def ToNodeData for #name #stage_use {
                fn node_data(&self) -> NodeData {
                    self.data.node_data()
                }
            }

            impl #stage_def_static Node for #name #stage_use {}

            impl #stage_def_static Drive for #name #stage_use {
                #[allow(unused_variables)]
                fn drive(&self, visitor: &mut dyn Visitor) {
                    #( visitor.visit(&self.#drive_fields); )*
                }
            }

            impl #stage_def Clone for #name #stage_use {
                #[allow(clippy::clone_on_copy)]
                fn clone(&self) -> Self {
                    Self {
                        data: self.data.clone(),
                        #( #field_names: self.#field_names.clone() ),*
                    }
                }
            }

            impl #stage_def std::fmt::Debug for #name #stage_use {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    f.debug_struct(stringify!(#name_string))
                        .field("data", &self.data)
                        #( .field(#field_strings, &self.#field_names) )*
                        .finish()
                }
            }
        });
    }
}

impl ToTokens for Field {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Field { name, ty, .. } = self;

        tokens.extend(quote! {
            pub #name: #ty
        });
    }
}

impl ToTokens for EnumNode {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let EnumNode { name, stage, variants } = self;

        let stage_use = stage.use_site();
        let stage_def = stage.def_site();
        let stage_def_static = stage.def_site_static();

        let variant_strings = variants.iter()
            .map(|variant| variant.alias.to_string());

        let structs = variants.iter()
            .filter_map(|variant| match &variant.kind {
                VariantKind::Def(node) => Some(node),
                _ => None
            });

        let variant_names = variants.iter()
            .map(|variant| &variant.alias)
            .collect::<Vec<_>>();

        let variant_visit_arms = variants.iter()
            .map(variant_visit_arm);

        let variants = variants.iter()
            .map(|variant| variant_to_tokens(variant, self))
            .collect::<Vec<_>>();

        tokens.extend(quote! {
            pub enum #name #stage_def {
                #(#variants),*
            }

            impl #stage_def ToNodeData for #name #stage_use {
                fn node_data(&self) -> NodeData {
                    match self {
                        #( Self::#variant_names(x) => x.node_data() ),*
                    }
                }
            }

            impl #stage_def_static Node for #name #stage_use {}

            impl #stage_def_static Drive for #name #stage_use {
                #[allow(unused_variables)]
                fn drive(&self, visitor: &mut dyn Visitor) {
                    match self {
                        #( #variant_visit_arms ),*
                    }
                }
            }

            impl #stage_def Clone for #name #stage_use {
                #[allow(clippy::clone_on_copy)]
                fn clone(&self) -> Self {
                    match self {
                        #( Self::#variant_names(x) => Self::#variant_names(x.clone()) ),*
                    }
                }
            }

            impl #stage_def std::fmt::Debug for #name #stage_use {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    match self {
                        #(
                            Self::#variant_names(x) => f
                                .debug_tuple(#variant_strings)
                                .field(x)
                                .finish()
                        ),*
                    }
                }
            }

            #(#structs)*
        });
    }
}

fn variant_visit_arm(variant: &Variant) -> TokenStream {
    let expr = if variant.boxed {
        quote! { x.as_ref() }
    } else {
        quote! { x }
    };

    let name = &variant.alias;
    quote! {
        Self::#name(x) => visitor.visit(#expr)
    }
}

fn variant_to_tokens(variant: &Variant, node: &EnumNode) -> TokenStream {
    let ty = match &variant.kind {
        VariantKind::Def(StructNode { name, stage, .. }) => {
            let stage = if stage.0.is_some() {
                let s = node.stage.use_site();
                quote! { #s }
            } else {
                quote! { }
            };

            quote! { #name #stage }
        },
        VariantKind::Type(ty) => quote! { #ty },
    };

    let ty = if variant.boxed {
        quote! { Box<#ty> }
    } else {
        ty
    };

    let alias = &variant.alias;

    quote! {
        #alias(#ty)
    }
}
