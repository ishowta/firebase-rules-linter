use clap::{command, Parser, ValueEnum};
use miette::Report;
use serde::{Deserialize, Serialize};
use serde_inline_default::serde_inline_default;
use std::{
    collections::{HashMap, HashSet},
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

    #[arg(short, long = "config", default_value = ".ruleslintrc.json")]
    config_path: std::path::PathBuf,

    #[arg(long, value_delimiter = ',')]
    only: Vec<Feature>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Hash)]
pub enum RuleSeverity {
    #[serde(rename = "off")]
    Off,
    #[serde(rename = "warn")]
    Warn,
    #[serde(rename = "error")]
    Error,
}

#[serde_inline_default]
#[derive(Clone, Debug, Deserialize)]
pub struct LinterRules {
    #[serde_inline_default(<LinterRules as Default>::default().no_unnecessary_condition)]
    no_unnecessary_condition: RuleSeverity,

    #[serde_inline_default(<LinterRules as Default>::default().no_dupe_args)]
    no_dupe_args: RuleSeverity,

    #[serde_inline_default(<LinterRules as Default>::default().no_dupe_keys)]
    no_dupe_keys: RuleSeverity,

    #[serde_inline_default(<LinterRules as Default>::default().no_unused_vars)]
    no_unused_vars: RuleSeverity,

    #[serde_inline_default(<LinterRules as Default>::default().no_shadow)]
    no_shadow: RuleSeverity,

    #[serde_inline_default(<LinterRules as Default>::default().no_list_field)]
    no_list_field: RuleSeverity,

    #[serde_inline_default(<LinterRules as Default>::default().no_read_rule)]
    no_read_rule: RuleSeverity,

    #[serde_inline_default(<LinterRules as Default>::default().no_write_rule)]
    no_write_rule: RuleSeverity,

    #[serde_inline_default(<LinterRules as Default>::default().check_path_injection)]
    check_path_injection: RuleSeverity,

    #[serde_inline_default(<LinterRules as Default>::default().unexpected_field)]
    unexpected_field: RuleSeverity,

    #[serde_inline_default(<LinterRules as Default>::default().untyped_field)]
    untyped_field: RuleSeverity,

    #[serde_inline_default(<LinterRules as Default>::default().insufficient_upper_size_limit)]
    insufficient_upper_size_limit: RuleSeverity,
}

impl Default for LinterRules {
    fn default() -> Self {
        Self {
            no_unnecessary_condition: RuleSeverity::Error,
            no_dupe_args: RuleSeverity::Error,
            no_dupe_keys: RuleSeverity::Error,
            no_unused_vars: RuleSeverity::Error,
            no_shadow: RuleSeverity::Error,
            no_list_field: RuleSeverity::Error,
            no_read_rule: RuleSeverity::Warn,
            no_write_rule: RuleSeverity::Warn,
            check_path_injection: RuleSeverity::Error,
            unexpected_field: RuleSeverity::Error,
            untyped_field: RuleSeverity::Error,
            insufficient_upper_size_limit: RuleSeverity::Error,
        }
    }
}

#[derive(Clone, Debug, Deserialize, Default)]
struct Config {
    #[serde(default)]
    rules: LinterRules,
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
            config: &config,
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
