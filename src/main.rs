use miette::Report;
use std::{collections::HashSet, fs};

use crate::{
    binder::bind,
    checker::{check, TypeCheckContext, TypeCheckResult},
    globals::get_globals,
    parser::parse,
};

mod ast;
mod binder;
mod checker;
mod globals;
mod interfaces;
mod orany;
mod parser;
mod symbol;
mod ty;

fn main() {
    env_logger::init();

    let code = fs::read_to_string("./tmp/realworld.rules").unwrap();

    let ast = parse(&code);

    // println!("{:#?}", ast);

    let (flow, globals, request_resource_data_ty_id) = get_globals();

    let (bindings, symbol_references, bind_lint_result) = bind(&ast, &globals);

    let type_check_context = TypeCheckContext {
        bindings: &bindings,
        symbol_references: &symbol_references,
        source_code: &code,
    };

    let type_check_result = check(
        &ast,
        &type_check_context,
        &flow,
        &request_resource_data_ty_id,
    );

    let mut type_check_result: Vec<&TypeCheckResult> = type_check_result
        .iter()
        .collect::<HashSet<&TypeCheckResult>>()
        .iter()
        .cloned()
        .collect();
    type_check_result.sort_by(|a, b| a.at.offset().cmp(&b.at.offset()));

    let results: Vec<Report> = bind_lint_result
        .into_iter()
        .chain(type_check_result.iter().map(|x| Report::from((*x).clone())))
        .collect();

    let result_count = results.len();
    for result in results {
        println!("{:?}", result.with_source_code(code.clone()));
    }

    println!("{} errors found.", result_count);
}
