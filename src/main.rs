use std::fs;

use crate::{
    binder::bind,
    checker::{check, TypeCheckContext},
    globals::get_globals,
    interfaces::get_interfaces,
    parser::parse,
};

mod ast;
mod binder;
mod checker;
mod globals;
mod interfaces;
mod parser;
mod symbol;
mod ty;

fn main() {
    let code = fs::read_to_string("./tmp/realworld.rules").unwrap();

    let ast = parse(&code);

    // println!("{:#?}", ast);

    let globals = get_globals();

    let (bindings, symbol_references, bind_lint_result) = bind(&ast, &globals);

    let interfaces = get_interfaces();

    let type_check_context = TypeCheckContext {
        bindings: &bindings,
        symbol_references: &symbol_references,
        interfaces: &interfaces,
    };

    let type_check_result = check(&ast, &type_check_context);

    println!("\n\n");

    for result in bind_lint_result {
        let range = result.node.get_span().0;
        println!(
            "{:?} - \x1b[31merror\x1b[m {:?}\n\n{}\n\n",
            result.node.get_span(),
            result.kind,
            &code[range.start_byte..range.end_byte],
        );
    }

    for result in type_check_result {
        let range = result.node.get_span().0;
        println!(
            "{:?} - error {:?}\n\n{}\n\n",
            result.node.get_span(),
            result.reason,
            &code[range.start_byte..range.end_byte],
        );
    }
}
