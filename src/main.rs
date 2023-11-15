use std::fs;

use crate::{
    binder::bind,
    checker::{check, TypeCheckContext},
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

    let ast = parse(&code.into());

    let (bindings, symbol_references, bind_lint_result) = bind(&ast);

    let type_check_context = TypeCheckContext {
        bindings: &bindings,
        symbol_references: &symbol_references,
    };

    let type_check_result = check(&ast, &type_check_context);

    println!("{:#?}", ast);
    println!("{:#?}", bindings);
    println!("{:#?}", symbol_references);
    println!("{:#?}", bind_lint_result);
    println!("{:#?}", type_check_result);
}
