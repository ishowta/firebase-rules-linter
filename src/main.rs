use miette::Report;
use std::{collections::HashSet, fs};

use crate::{
    analyser::{analyze, types::AnalysysGlobalContext},
    binder::bind,
    checker::{check, TypeCheckContext, TypeCheckResult},
    globals::get_globals,
    parser::parse,
};

mod analyser;
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
    let bind_lint_result_len = bind_lint_result.len();

    for result in bind_lint_result {
        println!("{:?}", result.with_source_code(code.clone()));
    }

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

    for result in type_check_result.iter().map(|x| Report::from((*x).clone())) {
        println!("{:?}", result.with_source_code(code.clone()));
    }

    let analysys_global_context = AnalysysGlobalContext {
        bindings: &bindings,
        symbol_references: &symbol_references,
        source_code: &code,
    };

    let analyse_result = analyze(&analysys_global_context, &ast);

    for result in analyse_result.iter().map(|x| Report::from((*x).clone())) {
        println!("{:?}", result.with_source_code(code.clone()));
    }

    let result_count = bind_lint_result_len + type_check_result.len() + analyse_result.len();

    println!("{} errors found.", result_count);
}
