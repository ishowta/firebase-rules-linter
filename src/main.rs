use std::fs;

use crate::{binder::bind, parser::parse};

mod ast;
mod binder;
mod parser;

fn main() {
    let code = fs::read_to_string("./tmp/realworld.rules").unwrap();

    let ast = parse(&code.into());

    let (bindings, symbol_references, bind_lint_result) = bind(&ast);

    println!("{:#?}", ast);
    println!("{:#?}", bindings);
    println!("{:#?}", symbol_references);
    println!("{:#?}", bind_lint_result);
}
