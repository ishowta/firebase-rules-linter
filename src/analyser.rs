use std::{cell::RefCell, collections::HashMap};

use async_recursion::async_recursion;
use futures::{future::join_all, join};
use indicatif::ProgressBar;
use log::{debug, info};
use serde_json::to_string_pretty;

mod check_expression;
mod check_function;
mod check_global_function;
mod destruct_sort;
mod parser;
mod solver;
mod z3;

pub mod types;

use crate::{
    analyser::{
        check_expression::check_expression,
        parser::parse_smt2_result,
        solver::{solve, SolverResult},
        types::{AnalysysContext, Res},
        z3::{Assert, Ast, Constraint, Declaration, Symbol},
    },
    ast::{Node, Permission, Rule, RuleGroup},
};

use self::types::{AnalysysError, AnalysysGlobalContext};

async fn check_rule<'a>(
    global_ctx: &AnalysysGlobalContext<'a>,
    rule: &Rule,
    progress_bar: &ProgressBar,
) -> Vec<AnalysysError> {
    info!(
        "check rule at {} line",
        rule.get_span().0.start_point.row + 1
    );

    let mut errors = vec![];

    let check_always_false_mode = true;

    // check always false
    let mut is_always_false_unsat: bool = false;
    if check_always_false_mode
        && rule
            .permissions
            .iter()
            .any(|permission| [Permission::Write, Permission::Create].contains(permission))
        && !rule
            .permissions
            .iter()
            .any(|permission| [Permission::Update].contains(permission))
    {
        debug!("check always false");
        let ctx = AnalysysContext {
            bindings: global_ctx.bindings,
            symbol_references: global_ctx.symbol_references,
            source_code: global_ctx.source_code,
            quick_mode: false,
            variable_bindings: &HashMap::new(),
            declarations: &RefCell::new(vec![Declaration {
                smtlib2: include_str!("analyser/lib.smt2").to_owned(),
            }]),
        };

        let Res {
            value: condition_value,
            constraints: condition_constraints,
        } = check_expression(&ctx, &rule.condition);
        let source_code = format!(
            "{}

{}

{}
{}
{}
",
            ctx.declarations
                .borrow()
                .iter()
                .map(|declaration| declaration.as_smtlib2())
                .collect::<Vec<String>>()
                .join("\n"),
            condition_constraints
                .iter()
                .map(|constraint| Assert::new(constraint).as_smtlib2())
                .collect::<Vec<String>>()
                .join("\n"),
            Assert::new(&Constraint::new1(
                "refl-is-valid-data",
                &Constraint::mono("resource_data")
            ))
            .as_smtlib2(),
            Assert::new(&Constraint::new1(
                "refl-is-valid-data",
                &Constraint::mono("request_resource_data")
            ))
            .as_smtlib2(),
            Assert::new(&Constraint::new2(
                "=",
                &condition_value,
                &Constraint::new1("bool", &true)
            ))
            .as_smtlib2(),
        );
        match solve(&source_code).await {
            SolverResult::Sat(example) => {
                debug!("sat");
                debug!("truthly example:\n{}", example);
            }
            SolverResult::Unsat => {
                info!("Always false");
                is_always_false_unsat = true;
                errors.push(AnalysysError::new(format!("Always false"), rule))
            }
            SolverResult::Unknown | SolverResult::Timeout => errors.push(AnalysysError::new(
                format!("Static analysis failed because this conditions are too complex."),
                rule,
            )),
        }
    }

    if !is_always_false_unsat
        && rule.permissions.iter().any(|permission| {
            [Permission::Write, Permission::Update, Permission::Create].contains(permission)
        })
    {
        // field check
        if global_ctx.config.rules.unexpected_field
            || global_ctx.config.rules.untyped_field
            || global_ctx.config.rules.insufficient_upper_size_limit
        {
            debug!("field check");
            let ctx = AnalysysContext {
                bindings: global_ctx.bindings,
                symbol_references: global_ctx.symbol_references,
                source_code: global_ctx.source_code,
                quick_mode: true,
                variable_bindings: &HashMap::new(),
                declarations: &RefCell::new(vec![Declaration {
                    smtlib2: include_str!("analyser/lib.smt2").to_owned(),
                }]),
            };

            let Res {
                value: condition_value,
                constraints: condition_constraints,
            } = check_expression(&ctx, &rule.condition);
            let source_code = format!(
                "{}

{}
{}
{}
",
                ctx.declarations
                    .borrow()
                    .iter()
                    .map(|declaration| declaration.as_smtlib2())
                    .collect::<Vec<String>>()
                    .join("\n"),
                condition_constraints
                    .iter()
                    .map(|constraint| Assert::new(constraint).as_smtlib2())
                    .collect::<Vec<String>>()
                    .join("\n"),
                Assert::new(&Constraint::new2(
                    "=",
                    &condition_value,
                    &Constraint::new1("bool", &true)
                ))
                .as_smtlib2(),
                // Assert::new(&Constraint::new2(
                //     "=",
                //     &Constraint::new1(
                //         "list-has-untyped-data",
                //         &Constraint::mono("request_resource_data_inner")
                //     ),
                //     &true
                // ))
                // .as_smtlib2(),
                // TODO: 1MB limit
                if global_ctx.config.rules.insufficient_upper_size_limit {
                    Assert::new(&Constraint::new2(
                        ">",
                        &Constraint::new1(
                            "list-sum",
                            &Symbol {
                                smtlib2: "request_resource_data_inner".to_string(),
                            },
                        ),
                        &(1024 * 1024),
                    ))
                    .as_smtlib2()
                } else if global_ctx.config.rules.untyped_field {
                    Assert::new(&Constraint::new1(
                        "not",
                        &Constraint::new1(
                            "list-is-valid-data",
                            &Symbol {
                                smtlib2: "request_resource_data_inner".to_string(),
                            },
                        ),
                    ))
                    .as_smtlib2()
                } else {
                    Assert::new(&Constraint::new1(
                        "list-has-unexpected-field",
                        &Symbol {
                            smtlib2: "request_resource_data_inner".to_string(),
                        },
                    ))
                    .as_smtlib2()
                }
            );
            match solve(&source_code).await {
                SolverResult::Sat(example) => {
                    let example_as_json =
                        to_string_pretty(&parse_smt2_result(example.clone())).unwrap();
                    let message = if global_ctx.config.rules.insufficient_upper_size_limit {
                        "1MB detected (insufficient-upper-size-limit)"
                    } else if global_ctx.config.rules.untyped_field {
                        "untyped field detected (untyped-field)"
                    } else {
                        "unexpected field detected (unexpected-field)"
                    };
                    errors.push(AnalysysError::new(
                        format!("{}\n\n{}", message, example_as_json),
                        rule,
                    ));
                    info!("detected");
                    info!("example:\n{}\n\n{}", example, example_as_json);
                }
                SolverResult::Unsat => {
                    debug!("unsat");
                }
                SolverResult::Unknown | SolverResult::Timeout => {
                    info!("timeout, skip");
                    errors.push(AnalysysError::new(
                        format!("Static analysis failed because this conditions are too complex."),
                        rule,
                    ))
                }
            }
        }
    }

    progress_bar.inc(1);

    errors
}

#[async_recursion(?Send)]
async fn check_rule_group<'a>(
    ctx: &AnalysysGlobalContext<'a>,
    rule_group: &RuleGroup,
    progress_bar: &ProgressBar,
) -> Vec<AnalysysError> {
    let (rule_res, rule_group_res) = join!(
        join_all(
            rule_group
                .rules
                .iter()
                .map(|rule| check_rule(ctx, rule, progress_bar))
        ),
        join_all(
            rule_group
                .rule_groups
                .iter()
                .map(|rule_group| check_rule_group(ctx, rule_group, progress_bar)),
        ),
    );
    rule_res
        .into_iter()
        .flatten()
        .chain(rule_group_res.into_iter().flatten())
        .collect()
}

fn count_rule_in_rule_group(rule_group: &RuleGroup) -> u64 {
    rule_group.rules.len() as u64
        + rule_group
            .rule_groups
            .iter()
            .map(|rule_group| count_rule_in_rule_group(rule_group))
            .sum::<u64>()
}

fn count_rule(ast: &crate::ast::Ast) -> u64 {
    ast.tree
        .services
        .iter()
        .map(|service| {
            service
                .rule_groups
                .iter()
                .map(|rule_group| count_rule_in_rule_group(rule_group))
                .sum::<u64>()
        })
        .sum::<u64>()
}

#[tokio::main]
pub async fn analyze(ctx: &AnalysysGlobalContext, ast: &crate::ast::Ast) -> Vec<AnalysysError> {
    let rule_count = count_rule(ast);
    let progress_bar = ProgressBar::new(rule_count);
    join_all(ast.tree.services.iter().map(|service| {
        join_all(
            service
                .rule_groups
                .iter()
                .map(|rule_group| check_rule_group(ctx, rule_group, &progress_bar)),
        )
    }))
    .await
    .into_iter()
    .flatten()
    .flatten()
    .collect()
}
