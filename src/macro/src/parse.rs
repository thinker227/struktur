use syn::{Error, Ident, Token, Type, braced, parenthesized, parse::{Parse, ParseStream, Result}, token::Paren};

use crate::{EnumNode, Field, Stage, StructNode, Variant, VariantKind};

fn parse_node_name(input: ParseStream) -> Result<(Ident, Option<Ident>)> {
    let name = input.parse::<Ident>()?;

    let open_angle = input.parse::<Option<Token![<]>>()?;
    let stage = if open_angle.is_some() {
        let stage = input.parse::<Ident>()?;

        input.parse::<Token![>]>()?;

        Some(stage)
    } else {
        None
    };

    Ok((name, stage))
}

fn parse_fields(input: ParseStream) -> Result<(Vec<Field>, Option<Type>)> {
    let fields = input.parse_terminated(Field::parse, Token![,])?;

    let mut fields = fields.into_iter().collect::<Vec<_>>();

    let index = fields.iter()
        .enumerate()
        .find(|(_, field)| field.name == "data");

    let data_ty = if let Some((index, _)) = index {
        Some(fields.remove(index).ty)
    } else {
        None
    };

    Ok((fields, data_ty))
}

impl Parse for StructNode {
    fn parse(input: ParseStream) -> Result<Self> {
        let (name, stage) = parse_node_name(input)?;

        input.parse::<Token![where]>()?;

        let (fields, data_ty) = parse_fields(input)?;

        Ok(StructNode {
            name,
            stage: Stage(stage),
            data_ty,
            fields,
        })
    }
}

impl Parse for Field {
    fn parse(input: ParseStream) -> Result<Self> {
        let r#raw = input.parse::<Option<Token![raw]>>()?;

        let name = input.parse::<Ident>()?;

        input.parse::<Token![:]>()?;

        let ty = input.parse::<Type>()?;

        Ok(Field {
            name,
            is_raw: r#raw.is_some(),
            ty
        })
    }
}

impl Parse for EnumNode {
    fn parse(input: ParseStream) -> Result<Self> {
        let (name, stage) = parse_node_name(input)?;

        input.parse::<Token![where]>()?;

        let parse_variant = if stage.is_some() {
            |i| parse_variant(i, true)
        } else {
            |i| parse_variant(i, false)
        };
        let variants = input.parse_terminated(parse_variant, Token![,])?;

        Ok(EnumNode {
            name,
            stage: Stage(stage),
            variants: variants.into_iter().collect()
        })
    }
}

fn parse_variant(input: ParseStream, has_stage: bool) -> Result<Variant> {
    let r#box = input.parse::<Option<Token![box]>>()?;

    let name = input.parse::<Ident>()?;

    let open_angle = input.parse::<Option<Token![<]>>()?;
    if let Some(open_angle) = open_angle {
        return if has_stage {
            let stage = input.parse::<Ident>()?;

            input.parse::<Token![>]>()?;

            parse_def_variant(input, r#box.is_some(), name, Some(stage))
        } else {
            Err(Error::new(
                open_angle.span,
                format!("Specifying a stage parameter for `{name}` is not allowed since the enclosing enum does not specify one")
            ))
        }
    }

    let lookahead = input.lookahead1();
    if lookahead.peek(Paren) {
        let content;
        parenthesized!(content in input);

        let ty = content.parse::<Type>()?;

        Ok(Variant {
            alias: name,
            boxed: r#box.is_some(),
            kind: VariantKind::Type(ty)
        })
    } else if lookahead.peek(Token![as]) {
        parse_def_variant(input, r#box.is_some(), name, None)
    } else {
        Err(lookahead.error())
    }
}

fn parse_def_variant(input: ParseStream, boxed: bool, name: Ident, stage: Option<Ident>) -> Result<Variant> {
    input.parse::<Token![as]>()?;

    let alias = input.parse::<Ident>()?;

    let content;
    braced!(content in input);

    let (fields, data_ty) = parse_fields(&content)?;

    Ok(Variant {
        alias,
        boxed,
        kind: VariantKind::Def(StructNode {
            name,
            stage: Stage(stage),
            data_ty,
            fields
        })
    })
}
