use std::{cell::RefCell, io::Write, process::Command};

use log::debug;
use miette::{Diagnostic, SourceSpan};
use tempfile::NamedTempFile;
use thiserror::Error;

use crate::{
    ast::{Ast, Expression, Node, Rule, RuleGroup},
    symbol::{Bindings, SymbolReferences},
};

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
    pub declarations: &'ctx RefCell<Vec<Declaration>>,
}

fn check_expression(ctx: &AnalysysContext, rule: &Expression) -> ExpressionProperties {
    ctx.declarations.borrow_mut().push(
        r#"
(declare-const keys (Seq String))

(declare-const arr (Seq String))

(declare-const foo Refl)

(declare-const literal_3 (Int))

(declare-const bar_inner Int)
(declare-const bar Refl)
"#
        .to_owned(),
    );
    ExpressionProperties {
        symbol: "".to_owned(),
        constraints: vec![
            // keys = data.keys()
            format!("(= keys (list-keys request_resource_data_inner))"),
            //format!("(forall ((key String)) (= (not (= (list-get request_resource_data_inner key) undefined)) (= (select keys key) true)))"),
            // arr = ['foo', 'baz']
            format!("(= arr (seq.++ (seq.unit \"foo\") (seq.unit \"bar\") (seq.unit \"hoge\")))"),
            // keys.hasOnly(arr)
            //format!("(forall ((key String)) (implies (= (select keys key) true) (seq.contains arr (seq.unit key))))"),
            format!("(= arr keys)"),
            // 'foo' in data
            format!("(= (list-get request_resource_data_inner \"foo\") foo)"),
            // 3
            format!("(= literal_3 3)"),
            // foo == 3
            format!("(= foo (int literal_3))"),
            // 'bar' in data
            format!("(= (list-get request_resource_data_inner \"bar\") bar)"),
            // bar is string
            format!("(= bar (str bar_inner))"),
            // bar.len() < n
            format!("(< bar_inner 100)"),
        ],
        errors: vec![],
    }
}

fn run_z3(source: &String) -> String {
    let mut source_file = NamedTempFile::new().unwrap();
    let _ = source_file.write_all(source.as_bytes());
    let command_result = Command::new("z3").arg(source_file.path()).output();
    let command_output = String::from_utf8_lossy(&command_result.unwrap().stdout)
        .trim()
        .into();
    command_output
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SolverResult {
    Sat(String),
    Unsat,
    Unknown,
}

fn solve(source: &String) -> SolverResult {
    let input = format!(
        "
{}

(check-sat)
(get-model)
",
        source
    );
    let output = run_z3(&input);
    match output.split("\n").nth(0) {
        Some("sat") => {
            SolverResult::Sat(output.split("\n").skip(1).collect::<Vec<&str>>().join("\n"))
        }
        Some("unsat") => SolverResult::Unsat,
        Some("unknown") => SolverResult::Unknown,
        _ => panic!(),
    }
}

fn check_rule(ctx: &AnalysysGlobalContext, rule: &Rule) -> Vec<AnalysysError> {
    debug!(
        "check rule at {} line",
        rule.get_span().0.start_point.row + 1
    );

    let ctx = AnalysysContext {
        bindings: ctx.bindings,
        symbol_references: ctx.symbol_references,
        source_code: ctx.source_code,
        declarations: &RefCell::new(vec![format!(
            r#"
(declare-datatypes (T1 T2) ((Entry (entry (key T1) (value T2)))))

(declare-datatypes ((Refl 0)) (
    (
        (undefined)
        ;(null)
        ;(bool (bool_val Bool))
        (int (int_val Int))
        ;(float (float_val Float64))
        (str (str_bytes Int))
        ;(char (char_val Unicode))
        ;(duration)
        ;(latlng)
        ;(timestamp)
        ;(list (list_val (Seq Refl)))
        (map (map_val (List (Entry String Refl))))
        ;(mapdiff (mapdiff_left (Array String Refl)) (mapdiff_right (Array String Refl)))
        ;(path (path_val String))
        ;(pathubt (pathubt_val (Seq String)))
        ;(pathbt (pathbt_val (Seq String)))
    )
))

(define-fun-rec
    list-get
    (
        (lst (List (Entry String Refl)))
        (sk String)
    )
    Refl
    (if
        (= lst nil)
        undefined
        (if
            (= (key (head lst)) sk)
            (value (head lst))
            (list-get (tail lst) sk)
        )
    )
)

(define-fun-rec
    list-keys
    (
        (lst (List (Entry String Refl)))
    )
    (Seq String)
    (if
        (= lst nil)
        (as seq.empty (Seq String))
        (seq.++
            (seq.unit (key (head lst)))
            (list-keys (tail lst))
        )
    )
)

;(declare-const request_resource_data Refl)
(declare-const request_resource_data_inner (List (Entry String Refl)))
;(assert (= request_resource_data (map request_resource_data_inner)))

;(declare-const request_resource Refl)
;(declare-const request_resource_inner (List (Entry String Refl)))
;(assert (= (list-get request_resource_inner "data") request_resource_data))
;(assert (= request_resource (map request_resource_inner)))

;(declare-const request Refl)
;(declare-const request_inner (List (Entry String Refl)))
;(assert (= (list-get request_inner "resource") request_resource))
;(assert (= request (map request_inner)))
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
        let source_code = format!(
            "
{}
{}
",
            ctx.declarations.borrow().join("\n"),
            constraint
        );
        debug!("source code:\n{}", source_code);
        match solve(&source_code) {
            SolverResult::Sat(example) => {
                debug!("sat");
                debug!("truthly example:\n{}", example);
            }
            SolverResult::Unsat => errors.push(AnalysysError::new(format!("Always false"), rule)),
            SolverResult::Unknown => errors.push(AnalysysError::new(
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

(define-fun-rec
    list-sum
    (
        (lst (List (Entry String Refl)))
    )
    Int
    (if
        (= lst nil)
        0
        (+
            (match (value (head lst)) (
                ((int x) 8)
                ((str x) x)
                (undefined 0)
                ((map x) (list-sum x))
            ))
            (list-sum (tail lst))
        )
    )
)
(assert (> (list-sum request_resource_data_inner) 1000))
        "#;
        debug!("check 1MB limit");
        let constraint = constraints.iter().fold("".to_owned(), |acc, constraint| {
            format!("{}\n(assert {})", acc, constraint)
        });
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
        match solve(&source_code) {
            SolverResult::Sat(example) => {
                errors.push(AnalysysError::new(format!("over 1MB limit"), rule));
                debug!("sat");
                debug!("truthly example:\n{}", example);
            }
            SolverResult::Unsat => {
                debug!("success unsat");
            }
            SolverResult::Unknown => errors.push(AnalysysError::new(
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
