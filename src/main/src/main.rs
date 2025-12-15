use std::{env, fs};

use struktur::parse::parse;
use miette::{NamedSource, Report};

// use struktur::stage::Parse;
// use struktur::ast::*;
// use struktur::symbols::resolve_symbols;
// use struktur::types::{Type, type_check};

fn main() {
    let args = env::args().skip(1).collect::<Vec<_>>();
    let path = &args[0];
    let text = fs::read_to_string(path).unwrap();
    let source = NamedSource::new(path, text);

    let parsed = match parse(source.inner()) {
        Ok(x) => x,
        Err(e) => {
            let report = Report::from(e)
                .with_source_code(NamedSource::new(path, source));
            println!("{:?}", report);
            return;
        }
    };

    // let x = NodeId::next();

    // let id: Item<Parse> = Item(
    //     ItemVal::Function(Function {
    //         symbol: String::from("id"),
    //         param: String::from("x"),
    //         body: Expr(
    //             ExprVal::Var(String::from("x")),
    //             (),
    //             NodeData {
    //                 data: (),
    //                 id: NodeId::next()
    //             }
    //         )
    //     }),
    //     NodeData {
    //         data: (),
    //         id: NodeId::next()
    //     }
    // );

    // let main: Item<Parse> = Item(
    //     ItemVal::Function(Function {
    //         symbol: String::from("main"),
    //         param: String::from("_"),
    //         body: Expr(
    //             Application {
    //                 target: Expr(
    //                     ExprVal::Var(String::from("id")),
    //                     (),
    //                     NodeData {
    //                         data: (),
    //                         id: NodeId::next()
    //                     }
    //                 ),
    //                 arg: Expr(
    //                     ExprVal::Bool(true),
    //                     (),
    //                     NodeData {
    //                         data: (),
    //                         id: x
    //                     }
    //                 )
    //             }.into(),
    //             (),
    //             NodeData {
    //                 data: (),
    //                 id: NodeId::next()
    //             }
    //         )
    //     }),
    //     NodeData {
    //         data: (),
    //         id: NodeId::next()
    //     }
    // );

    // let root = Root(
    //     vec![id, main],
    //     NodeData {
    //         data: (),
    //         id: NodeId::next()
    //     }
    // );
    // let parse = Ast::new(root, (), ());
    // dbg!(parse.get_node(x).id());
    // dbg!(parse.get_node_as::<Expr<Parse>>(x));

    // let sem = resolve_symbols(&parse);

    // let _typed = type_check(&sem);

    // let _t = Type::function(Type::int(), Type::bool());
}
