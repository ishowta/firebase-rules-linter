use clap::{command, Parser, ValueEnum};
use itertools::Itertools;
use log::debug;
use miette::Report;
use serde::{Deserialize, Serialize};
use std::{
    collections::HashSet,
    fs::{self, File},
    io::BufReader,
};

use crate::{
    analyser::{analyze, types::AnalysysGlobalContext},
    binder::bind,
    checker::{check, TypeCheckContext},
    config::{Config, LintError},
    globals::get_globals,
    parser::parse,
};

mod analyser;
mod ast;
mod binder;
mod checker;
mod config;
mod globals;
mod interfaces;
mod orany;
mod parser;
mod symbol;
mod ty;

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum, Serialize, Deserialize, Hash)]
pub enum Feature {
    #[serde(rename = "linter")]
    Linter,
    #[serde(rename = "static-analyzer")]
    StaticAnalyzer,
}

#[derive(Parser)]
#[command(version, about)]
struct Args {
    #[arg(short, long = "input")]
    input_path: String,

    #[arg(short, long = "config", default_value = ".ruleslintrc.json")]
    config_path: std::path::PathBuf,

    #[arg(long, value_delimiter = ',')]
    only: Vec<Feature>,
}

fn main() {
    env_logger::init();

    let args = Args::parse();

    // Get config file
    let config = if let Ok(file) = File::open(&args.config_path) {
        // Parse config with serde
        match serde_json::from_reader::<_, Config>(BufReader::new(file)) {
            // merge config already parsed from clap
            Ok(config) => config,
            Err(err) => panic!("Error in configuration file:\n{}", err),
        }
    } else {
        Config::default()
    };

    let only = HashSet::<Feature>::from_iter(args.only.iter().cloned());

    let code = fs::read_to_string(args.input_path).unwrap();

    let mut error_count = 0;

    let ast = parse(&code);

    debug!("{:#?}", ast);

    let (flow, globals, request_resource_data_ty_id) = get_globals();

    let (bindings, symbol_references, bind_lint_result) = bind(&config, &ast, &globals);
    error_count += bind_lint_result.len();

    if only.is_empty() || only.contains(&Feature::Linter) {
        for result in bind_lint_result {
            println!("{:?}", result.report.with_source_code(code.clone()));
        }

        let type_check_context = TypeCheckContext {
            bindings: &bindings,
            symbol_references: &symbol_references,
            source_code: &code,
            config: &config,
        };

        let type_check_result = check(
            &ast,
            &type_check_context,
            &flow,
            &request_resource_data_ty_id,
        );

        let mut type_check_result: Vec<LintError> = type_check_result
            .into_iter()
            .unique_by(|lint_error| format!("{}", lint_error.report))
            .collect();
        type_check_result.sort_by(|a, b| a.span.offset().cmp(&b.span.offset()));

        error_count += type_check_result.len();

        for result in type_check_result {
            println!("{:?}", result.report.with_source_code(code.clone()));
        }
    }

    if only.is_empty() || only.contains(&Feature::StaticAnalyzer) {
        let analysys_global_context = AnalysysGlobalContext {
            bindings: &bindings,
            symbol_references: &symbol_references,
            source_code: &code,
            config: &config,
        };

        let analyse_result = analyze(&analysys_global_context, &ast);

        error_count += analyse_result.len();

        for result in analyse_result.iter().map(|x| Report::from((*x).clone())) {
            println!("{:?}", result.with_source_code(code.clone()));
        }
    }

    println!("{} errors found.", error_count);
}
