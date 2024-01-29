use std::cell::RefCell;

use log::debug;
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;
use z3::{Config, Context as Z3Context, SatResult, Solver};

use crate::{
    ast::{Ast, Expression, Node, Rule, RuleGroup},
    symbol::{Bindings, SymbolReferences},
};

// TODO: use z3 wrapper
type Symbol = String;
type Declaration = String;
type Constraint = String;

#[derive(Clone, Debug, Error, Diagnostic, PartialEq, Eq, Hash)]
#[error("{reason}")]
#[diagnostic()]
pub struct AnalysysError {
    pub reason: String,
    #[label]
    pub at: SourceSpan,
}

impl AnalysysError {
    pub fn new(reason: String, node: &dyn Node) -> AnalysysError {
        AnalysysError {
            reason: reason,
            at: node.get_span().into(),
        }
    }
}

#[derive(Clone, Debug)]
struct ExpressionProperties {
    symbol: Symbol,
    constraints: Vec<Constraint>,
    errors: Vec<AnalysysError>,
}

#[derive(Clone, Debug)]
pub struct AnalysysGlobalContext<'a> {
    pub bindings: &'a Bindings<'a>,
    pub symbol_references: &'a SymbolReferences<'a>,
    pub source_code: &'a String,
}

#[derive(Clone, Debug)]
struct AnalysysContext<'a, 'ctx> {
    pub bindings: &'a Bindings<'a>,
    pub symbol_references: &'a SymbolReferences<'a>,
    pub source_code: &'a String,
    pub z3_context: &'ctx Z3Context,
    pub declarations: &'ctx RefCell<Vec<Declaration>>,
}

fn check_expression(ctx: &AnalysysContext, rule: &Expression) -> ExpressionProperties {
    ctx.declarations.borrow_mut().push(
        r#"
(declare-const keys (Array String Bool))

(declare-const arr (Seq String))

(declare-const foo Refl)

(declare-const literal_3 (Int))

(declare-const bar_inner String)
(declare-const bar Refl)
"#
        .to_owned(),
    );
    ExpressionProperties {
        symbol: "".to_owned(),
        constraints: vec![
            // keys = data.keys()
            format!("(forall ((key String)) (= (not (= (select request_resource_data_inner key) undefined)) (= (select keys key) true)))"),
            // arr = ['foo', 'baz']
            format!("(= arr (seq.++ (seq.unit \"foo\") (seq.unit \"bar\")))"),
            // keys.hasOnly(arr)
            format!("(forall ((key String)) (implies (= (select keys key) true) (seq.contains arr (seq.unit key))))"),
            format!("(= arr request_resource_data_shape)"),
            // 'foo' in data
            format!("(= (select request_resource_data_inner \"foo\") foo)"),
            // 3
            format!("(= literal_3 3)"),
            // foo == 3
            format!("(= foo (int literal_3))"),
            // 'bar' in data
            format!("(= (select request_resource_data_inner \"bar\") bar)"),
            // bar.len() < n
            format!("(< (str.len bar_inner) 1000)"),
            format!("(= bar (str bar_inner))"),
        ],
        errors: vec![],
    }
}

fn check_rule(ctx: &AnalysysGlobalContext, rule: &Rule) -> Vec<AnalysysError> {
    debug!(
        "check rule at {} line",
        rule.get_span().0.start_point.row + 1
    );

    let config = Config::default();
    let ctx = AnalysysContext {
        bindings: ctx.bindings,
        symbol_references: ctx.symbol_references,
        source_code: ctx.source_code,
        z3_context: &Z3Context::new(&config),
        declarations: &RefCell::new(vec![format!(
            r#"
(declare-datatypes ((Refl 0)) (
    (
        (undefined)
        ;(null)
        ;(bool (bool_val Bool))
        (int (int_val Int))
        ;(float (float_val Float64))
        (str (str_val String))
        ;(char (char_val Unicode))
        ;(duration)
        ;(latlng)
        ;(timestamp)
        ;(list (list_val (Seq Refl)))
        (map (map_val (Array String Refl)) (map_shape (Seq String)))
        ;(mapdiff (mapdiff_left (Array String Refl)) (mapdiff_right (Array String Refl)))
        ;(path (path_val String))
        ;(pathubt (pathubt_val (Seq String)))
        ;(pathbt (pathbt_val (Seq String)))
    )
))

(declare-const request_resource_data Refl)
(declare-const request_resource_data_inner (Array String Refl))
(declare-const request_resource_data_shape (Seq String))
;(assert (forall ((key String)) (= (not (= (select request_resource_data_inner key) undefined)) (seq.contains request_resource_data_shape (seq.unit key)))))
(assert (= request_resource_data (map request_resource_data_inner request_resource_data_shape)))

(declare-const request_resource Refl)
(declare-const request_resource_inner (Array String Refl))
(declare-const request_resource_shape (Seq String))
(assert (= (select request_resource_inner "data") request_resource_data))
(assert (= request_resource (map request_resource_inner request_resource_shape)))

(declare-const request Refl)
(declare-const request_inner (Array String Refl))
(declare-const request_shape (Seq String))
(assert (= (select request_inner "resource") request_resource))
(assert (= request (map request_inner request_shape)))
"#
        )]),
    };

    let ExpressionProperties {
        symbol: _,
        constraints,
        mut errors,
    } = check_expression(&ctx, &rule.condition);

    // check always false
    {
        debug!("check always false");
        let constraint = constraints.iter().fold("".to_owned(), |acc, constraint| {
            format!("{}\n(assert {})", acc, constraint)
        });
        let solver = Solver::new(&ctx.z3_context);
        let source_code = format!(
            "
{}
{}
",
            ctx.declarations.borrow().join("\n"),
            constraint
        );
        debug!("source code:\n{}", source_code);
        solver.from_string(source_code);
        match solver.check() {
            SatResult::Sat => {
                debug!("sat");
                let model = solver.get_model().unwrap();
                debug!("truthly example:\n{}", model);
            }
            SatResult::Unsat => errors.push(AnalysysError::new(format!("Always false"), rule)),
            SatResult::Unknown => errors.push(AnalysysError::new(
                format!("Static analysis failed because this conditions are too complex."),
                rule,
            )),
        }
    }

    //     // check always true
    //     {
    //         debug!("check always true");
    //         let constraint = constraints
    //             .iter()
    //             .fold("true".to_owned(), |acc, constraint| {
    //                 format!("(and {} {})", acc, constraint)
    //             });
    //         let solver = Solver::new(&ctx.z3_context);
    //         let source_code = format!(
    //             "
    // {}

    // (assert (not {}))
    // ",
    //             ctx.declarations.borrow().join("\n"),
    //             constraint
    //         );
    //         debug!("source code:\n{}", source_code);
    //         solver.from_string(source_code);
    //         match solver.check() {
    //             SatResult::Sat => {
    //                 debug!("sat");
    //                 let model = solver.get_model().unwrap();
    //                 debug!("falthy example:\n{:#?}", model);
    //             }
    //             SatResult::Unsat => errors.push(AnalysysError::new(format!("Always true"), rule)),
    //             SatResult::Unknown => errors.push(AnalysysError::new(
    //                 format!("Static analysis failed because this conditions are too complex."),
    //                 rule,
    //             )),
    //         }
    //     }

    // 1MB limit
    {
        let limit_constraint = r#"
; 1MB limit
(declare-const sizes (Array String Int))
;(assert (forall ((key String) (value Int)) (implies (= (select request_resource_data_inner key) (int value)) (= (select sizes key) 8))))
;(assert (forall ((key String)) (implies (= (select request_resource_data_inner key) undefined) (= (select sizes key) 0))))
(assert
    (=
        true
        (seq.foldl
            (lambda
                ((acc Bool) (key String))
                (and
                    acc
                    (forall
                        ((value Int))
                        (implies
                            (=
                                (select request_resource_data_inner key)
                                (int value)
                            )
                            (=
                                (select sizes key)
                                8
                            )
                        )
                    )
                    (forall
                        ((value String))
                        (implies
                            (=
                                (select request_resource_data_inner key)
                                (str value)
                            )
                            (=
                                (select sizes key)
                                (str.len value)
                            )
                        )
                    )
                    (forall
                        ((value (Array String Refl)) (shape (Seq String)))
                        (implies
                            (=
                                (select request_resource_data_inner key)
                                (map value shape)
                            )
                            (=
                                (select sizes key)
                                0
                            )
                        )
                    )
                    (implies
                        (=
                            (select request_resource_data_inner key)
                            undefined
                        )
                        (=
                            (select sizes key)
                            0
                        )
                    )
                )
            )
            true
            arr
        )
    )
)
;(declare-const size_list (Seq Int))
;(assert (forall ((key String)) (implies (not (= (select sizes key) 0)) (not (= (seq.indexof size_list (seq.unit (select sizes key))) -1)))))
(assert (> (seq.foldl (lambda ((acc Int) (key String)) (+ acc (select sizes key))) 0 arr) 262144))
        "#;
        debug!("check 1MB limit");
        let constraint = constraints.iter().fold("".to_owned(), |acc, constraint| {
            format!("{}\n(assert {})", acc, constraint)
        });
        let solver = Solver::new(&ctx.z3_context);
        let source_code = format!(
            "
{}
{}

{}
",
            ctx.declarations.borrow().join("\n"),
            constraint,
            limit_constraint
        );
        debug!("source code:\n{}", source_code);
        solver.from_string(source_code);
        match solver.check() {
            SatResult::Sat => {
                errors.push(AnalysysError::new(format!("over 1MB limit"), rule));
                debug!("sat");
                let model = solver.get_model().unwrap();
                debug!("truthly example:\n{}", model);
            }
            SatResult::Unsat => {
                debug!("success unsat");
            }
            SatResult::Unknown => errors.push(AnalysysError::new(
                format!("Static analysis failed because this conditions are too complex."),
                rule,
            )),
        }
    }

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

pub fn analyze(ctx: &AnalysysGlobalContext, ast: &Ast) -> Vec<AnalysysError> {
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
