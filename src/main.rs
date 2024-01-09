use miette::Report;
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

    let results: Vec<Report> = bind_lint_result
        .into_iter()
        .chain(type_check_result.iter().map(|x| Report::from(x.clone())))
        .collect();

    for result in results {
        println!("{:?}", result.with_source_code(code.clone()));
    }
}
