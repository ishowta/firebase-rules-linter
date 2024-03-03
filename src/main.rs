use clap_serde_derive::{
    clap::{command, Parser, ValueEnum},
    ClapSerde,
};
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum, Serialize, Deserialize, Hash)]
pub enum Feature {
    #[serde(rename = "linter")]
    Linter,
    #[serde(rename = "type-checker")]
    TypeChecker,
    #[serde(rename = "static-analyzer")]
    StaticAnalyzer,
}

#[derive(Parser)]
#[command(version, about)]
struct Args {
    #[arg(short, long = "input")]
    input_path: String,

    #[arg(short, long = "config", default_value = "rules-linter-config.yml")]
    config_path: std::path::PathBuf,

    #[command(flatten)]
    pub config: <Config as ClapSerde>::Opt,
}

#[derive(ClapSerde)]
struct Config {
    #[arg(long, value_delimiter = ',')]
    only: Vec<Feature>,
}

fn main() {
    env_logger::init();

    let mut args = Args::parse();

    // Get config file
    let config = if let Ok(file) = File::open(&args.config_path) {
        // Parse config with serde
        match serde_yaml::from_reader::<_, <Config as ClapSerde>::Opt>(BufReader::new(file)) {
            // merge config already parsed from clap
            Ok(config) => Config::from(config).merge(&mut args.config),
            Err(err) => panic!("Error in configuration file:\n{}", err),
        }
    } else {
        // If there is not config file return only config parsed from clap
        Config::from(&mut args.config)
    };

    let only = HashSet::<Feature>::from_iter(config.only.iter().cloned());

    let code = fs::read_to_string(args.input_path).unwrap();

    let mut error_count = 0;

    let ast = parse(&code);

    // println!("{:#?}", ast);

    let (flow, globals, request_resource_data_ty_id) = get_globals();

    let (bindings, symbol_references, bind_lint_result) = bind(&ast, &globals);
    error_count += bind_lint_result.len();

    for result in bind_lint_result {
        println!("{:?}", result.with_source_code(code.clone()));
    }

    if only.is_empty() || only.contains(&Feature::TypeChecker) {
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

        error_count += type_check_result.len();

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
    }

    if only.is_empty() || only.contains(&Feature::StaticAnalyzer) {
        let analysys_global_context = AnalysysGlobalContext {
            bindings: &bindings,
            symbol_references: &symbol_references,
            source_code: &code,
        };

        let analyse_result = analyze(&analysys_global_context, &ast);

        error_count += analyse_result.len();

        for result in analyse_result.iter().map(|x| Report::from((*x).clone())) {
            println!("{:?}", result.with_source_code(code.clone()));
        }
    }

    println!("{} errors found.", error_count);
}
