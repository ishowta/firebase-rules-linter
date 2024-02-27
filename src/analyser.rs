use std::{cell::RefCell, collections::HashMap};

use log::{debug, info};

mod check_expression;
mod check_function;
mod check_global_function;
mod destruct_sort;
mod solver;
mod z3;

pub mod types;

use crate::{
    analyser::{
        check_expression::check_expression,
        solver::{solve, SolverResult},
        types::{AnalysysContext, Res},
        z3::{Assert, Ast, Constraint, Declaration, Symbol},
    },
    ast::{Node, Permission, Rule, RuleGroup},
};

use self::types::{AnalysysError, AnalysysGlobalContext};

fn check_rule(ctx: &AnalysysGlobalContext, rule: &Rule) -> Vec<AnalysysError> {
    info!(
        "check rule at {} line",
        rule.get_span().0.start_point.row + 1
    );

    let mut errors = vec![];

    let check_always_false_mode = true;

    // check always false
    let mut is_always_false_unsat: bool = true;
    if check_always_false_mode {
        debug!("check always false");
        let ctx = AnalysysContext {
            bindings: ctx.bindings,
            symbol_references: ctx.symbol_references,
            source_code: ctx.source_code,
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
        match solve(&source_code) {
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

    let check_limit_mode = true;

    if rule.permissions.iter().any(|permission| {
        [Permission::Write, Permission::Update, Permission::Create].contains(permission)
    })
    //if is_always_false_unsat == false && check_limit_mode {
    // untyped field check
    {
        debug!("1MB check");
        let ctx = AnalysysContext {
            bindings: ctx.bindings,
            symbol_references: ctx.symbol_references,
            source_code: ctx.source_code,
            quick_mode: true,
            variable_bindings: &HashMap::new(),
            declarations: &RefCell::new(vec![Declaration {
                smtlib2: include_str!("analyser/lib.smtlib2").to_owned(),
            }]),
        };

        let Res {
            value: condition_value,
            constraints: condition_constraints,
        } = check_expression(&ctx, &rule.condition);
        let source_code = format!(
            "{}

{}

;(declare-const request_resource_data_inner_inner (List (Entry String Refl)))
;(assert (= request_resource_data_inner (insert undefined request_resource_data_inner_inner)))

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
            Assert::new(&Constraint::new2(
                ">",
                &Constraint::new1(
                    "list-sum",
                    &Symbol {
                        smtlib2: "request_resource_data_inner".to_string()
                    }
                ),
                &(1024 * 1024)
            ))
            .as_smtlib2()
        );
        match solve(&source_code) {
            SolverResult::Sat(example) => {
                errors.push(AnalysysError::new(format!("1MB detected"), rule));
                info!("1MB detected");
                info!("example:\n{}", example);
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
    //}

    errors
}

fn check_rule_group(ctx: &AnalysysGlobalContext, rule_group: &RuleGroup) -> Vec<AnalysysError> {
    rule_group
        .rules
        .iter()
        .map(|rule| check_rule(ctx, rule))
        .flatten()
        .chain(
            rule_group
                .rule_groups
                .iter()
                .map(|rule_group| check_rule_group(ctx, rule_group))
                .flatten(),
        )
        .collect()
}

pub fn analyze(ctx: &AnalysysGlobalContext, ast: &crate::ast::Ast) -> Vec<AnalysysError> {
    ast.tree
        .services
        .iter()
        .map(|service| {
            service
                .rule_groups
                .iter()
                .map(|rule_group| check_rule_group(ctx, rule_group))
                .flatten()
        })
        .flatten()
        .collect()
}
