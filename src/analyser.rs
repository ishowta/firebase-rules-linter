use std::{cell::RefCell, collections::HashMap, io::Write, process::Command};

use log::{debug, info};
use miette::{Diagnostic, SourceSpan};
use tempfile::NamedTempFile;
use thiserror::Error;

use crate::{
    ast::{Ast, Expression, ExpressionKind, Literal, Node, NodeID, Rule, RuleGroup},
    symbol::{Bindings, SymbolReferences, VariableNodeRef},
    ty::FunctionKind,
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
struct Res {
    val_sym: Symbol,
    bytes_sym: Symbol,
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
    pub variable_bindings: &'ctx HashMap<&'a NodeID, &'ctx Res>,
}

fn or(params: &Vec<Constraint>) -> Constraint {
    let mut res = "(or\n".to_owned();
    for param in params {
        res.push_str("  ");
        res.push_str(param);
        res.push_str("\n");
    }
    res += "\n)";
    res
}

fn and(params: &Vec<Constraint>) -> Constraint {
    let mut res = "(and\n".to_owned();
    for param in params {
        res.push_str("  ");
        res.push_str(param);
        res.push_str("\n");
    }
    res += "\n)";
    res
}

fn check_function_calling(
    cur_expr: &dyn Node,
    ctx: &AnalysysContext,
    func: &FunctionKind,
    args: &Vec<&Res>,
    cur_val_sym: &Symbol,
    cur_bytes_sym: &Symbol,
) -> Vec<Constraint> {
    match func {
        FunctionKind::Function(_) => todo!(),
        FunctionKind::UnaryOp(_) => todo!(),
        FunctionKind::BinaryOp(binary_op) => match binary_op {
            crate::ast::BinaryLiteral::LogicalAnd => {
                let arg_bool_syms: Vec<_> = args
                    .iter()
                    .map(|arg| {
                        (
                            arg.val_sym.clone(),
                            format!("{}_{}_bool_sym", cur_expr.get_id().0, arg.val_sym),
                        )
                    })
                    .collect();
                let mut declarations: Vec<_> = arg_bool_syms
                    .iter()
                    .flat_map(|(arg_val_sym, arg_bool_sym)| {
                        vec![
                            format!("(declare-const {} Bool)", arg_bool_sym),
                            format!("(assert (= {} (bool {})))", arg_val_sym, arg_bool_sym),
                        ]
                    })
                    .collect();
                declarations.push(format!(
                    "(assert (= {} (bool {})))",
                    cur_val_sym,
                    and(&arg_bool_syms
                        .iter()
                        .map(|(_, arg_bool_sym)| arg_bool_sym.clone())
                        .collect())
                ));
                declarations
            }
            crate::ast::BinaryLiteral::LogicalOr => todo!(),
            crate::ast::BinaryLiteral::BitwiseAnd => todo!(),
            crate::ast::BinaryLiteral::BitwiseOr => todo!(),
            crate::ast::BinaryLiteral::BitwiseXor => todo!(),
            crate::ast::BinaryLiteral::Add => todo!(),
            crate::ast::BinaryLiteral::Sub => todo!(),
            crate::ast::BinaryLiteral::Mul => todo!(),
            crate::ast::BinaryLiteral::Div => todo!(),
            crate::ast::BinaryLiteral::Mod => todo!(),
            crate::ast::BinaryLiteral::Gt => todo!(),
            crate::ast::BinaryLiteral::Gte => todo!(),
            crate::ast::BinaryLiteral::Lt => todo!(),
            crate::ast::BinaryLiteral::Lte => todo!(),
            crate::ast::BinaryLiteral::Eq => vec![
                format!(
                    "(assert (= {} (bool (= {} {}))))",
                    cur_val_sym, args[0].val_sym, args[1].val_sym
                ),
                format!("(assert (= {} {}))", args[0].bytes_sym, args[1].bytes_sym),
                format!("(assert (= {} 1))", cur_bytes_sym),
            ],
            crate::ast::BinaryLiteral::NotEq => vec![
                format!(
                    "(assert (= {} (bool (not (= {} {})))))",
                    cur_val_sym, args[0].val_sym, args[1].val_sym
                ),
                format!(
                    "(assert (not (= {} {})))",
                    args[0].bytes_sym, args[1].bytes_sym
                ),
                format!("(assert (= {} 1))", cur_bytes_sym),
            ],
            crate::ast::BinaryLiteral::In => todo!(),
        },
        FunctionKind::Subscript => todo!(),
        FunctionKind::SubscriptRange => todo!(),
    }
}

fn check_expression(ctx: &AnalysysContext, cur_expr: &Expression) -> Res {
    let cur_val_sym = format!("{}_val", cur_expr.get_id().0);
    let cur_bytes_sym = format!("{}_bytes", cur_expr.get_id().0);
    ctx.declarations
        .borrow_mut()
        .push(format!("(declare-const {} Refl)", cur_val_sym));
    ctx.declarations
        .borrow_mut()
        .push(format!("(declare-const {} Int)", cur_bytes_sym));

    let mut declarations = match &cur_expr.kind {
        ExpressionKind::Literal(lit) => match lit {
            Literal::Null => vec![
                format!("(assert (= {} null))", cur_val_sym),
                format!("(assert (= {} 1))", cur_bytes_sym),
            ],
            Literal::Bool(lit) => vec![
                format!("(assert (= {} (bool {})))", cur_val_sym, lit),
                format!("(assert (= {} 1))", cur_bytes_sym),
            ],
            Literal::Int(lit) => vec![
                format!("(assert (= {} (int {})))", cur_val_sym, lit),
                format!("(assert (= {} 8))", cur_bytes_sym),
            ],
            Literal::Float(lit) => vec![
                format!("(assert (= {} (float {})))", cur_val_sym, lit),
                format!("(assert (= {} 8))", cur_bytes_sym),
            ],
            Literal::String(lit) => vec![
                format!(
                    "(assert (= {} (str \"{}\" {})))",
                    cur_val_sym,
                    lit,
                    lit.len()
                ),
                format!("(assert (= {} {}))", cur_bytes_sym, lit.len()),
            ],
            Literal::List(lit) => {
                let elems_res: Vec<_> = lit
                    .iter()
                    .map(|elem_lit| check_expression(ctx, elem_lit))
                    .collect();
                [
                    format!(
                        "(assert (= {} {}))",
                        cur_val_sym,
                        elems_res
                            .iter()
                            .fold("(as seq.empty (Seq Refl))".to_owned(), |acc, elem| {
                                format!("(seq.++ (seq.unit {}) {})", elem.val_sym, acc)
                            })
                    ),
                    format!(
                        "(assert (= {} {}))",
                        cur_bytes_sym,
                        elems_res.iter().fold("".to_owned(), |acc, elem| {
                            format!("(+ {} {})", elem.bytes_sym, acc)
                        })
                    ),
                ]
                .into()
            }
            Literal::Map(lit) => {
                let elems_res: Vec<_> = lit
                    .iter()
                    .map(|(key, value_expr)| (key, check_expression(ctx, value_expr)))
                    .collect();
                [
                    format!(
                        "(assert (= {} {}))",
                        cur_val_sym,
                        elems_res
                            .iter()
                            .fold("nil".to_owned(), |acc, (key, value)| {
                                format!("(cons (entry \"{}\" {}) {})", key, value.val_sym, acc)
                            })
                    ),
                    format!(
                        "(assert (= {} {}))",
                        cur_bytes_sym,
                        elems_res.iter().fold("".to_owned(), |acc, (_, value)| {
                            format!("(+ {} (+ 2 {}))", value.bytes_sym, acc)
                        })
                    ),
                ]
                .into()
            }
            Literal::Path(_) => vec![
                format!("(assert (= cur_sym path))"),
                format!("(assert (<= {} {}))", cur_bytes_sym, 6 * 1024),
            ],
        },
        ExpressionKind::Variable(_) => match ctx
            .bindings
            .variable_table
            .get(&cur_expr.id)
            .and_then(|node| Some(node.1))
        {
            None => vec![],
            Some(variable_node_ref) => match variable_node_ref {
                VariableNodeRef::LetBinding(node) => {
                    let Res { val_sym, bytes_sym } = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![
                        format!("(assert (= {} {}))", cur_val_sym, val_sym),
                        format!("(assert (= {} {}))", cur_bytes_sym, bytes_sym),
                    ]
                }
                VariableNodeRef::FunctionArgument(node) => {
                    let Res { val_sym, bytes_sym } = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![
                        format!("(assert (= {} {}))", cur_val_sym, val_sym),
                        format!("(assert (= {} {}))", cur_bytes_sym, bytes_sym),
                    ]
                }
                VariableNodeRef::PathCapture(node) => {
                    let Res { val_sym, bytes_sym } = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![
                        format!("(assert (= {} {}))", cur_val_sym, val_sym),
                        format!("(assert (= {} {}))", cur_bytes_sym, bytes_sym),
                    ]
                }
                VariableNodeRef::PathCaptureGroup(node) => {
                    let Res { val_sym, bytes_sym } = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![
                        format!("(assert (= {} {}))", cur_val_sym, val_sym),
                        format!("(assert (= {} {}))", cur_bytes_sym, bytes_sym),
                    ]
                }
                VariableNodeRef::GlobalVariable(_) => {
                    // TODO
                    vec![format!(
                        "(assert (= {} {}))",
                        cur_val_sym, "request_resource_data"
                    )]
                }
            },
        },
        ExpressionKind::TypeCheckOperation(target_expr, type_name) => {
            let target_res = check_expression(ctx, &target_expr);
            match type_name.as_str() {
                "bool" => {
                    let any_bool_sym = format!("{}_{}", target_res.val_sym, type_name);
                    ctx.declarations
                        .borrow_mut()
                        .push(format!("(declare-const {} Bool)", any_bool_sym));
                    vec![
                        format!(
                            "(assert (= {} (bool {})))",
                            target_res.val_sym, any_bool_sym
                        ),
                        format!("(assert (= {} {}))", target_res.bytes_sym, 1),
                    ]
                }
                "int" => {
                    let any_int_sym = format!("{}_{}", target_res.val_sym, type_name);
                    ctx.declarations
                        .borrow_mut()
                        .push(format!("(declare-const {} Int)", any_int_sym));
                    vec![
                        format!("(assert (= {} (int {})))", target_res.val_sym, any_int_sym),
                        format!("(assert (= {} {}))", target_res.bytes_sym, 8),
                    ]
                }
                "float" => {
                    let any_float_sym = format!("{}_{}", target_res.val_sym, type_name);
                    ctx.declarations
                        .borrow_mut()
                        .push(format!("(declare-const {} Float64)", any_float_sym));
                    vec![
                        format!(
                            "(assert (= {} (float {})))",
                            target_res.val_sym, any_float_sym
                        ),
                        format!("(assert (= {} {}))", target_res.bytes_sym, 8),
                    ]
                }
                "number" => {
                    let any_int_sym = format!("{}_{}", target_res.val_sym, type_name);
                    ctx.declarations
                        .borrow_mut()
                        .push(format!("(declare-const {} Int)", any_int_sym));
                    let any_float_sym = format!("{}_{}", target_res.val_sym, type_name);
                    ctx.declarations
                        .borrow_mut()
                        .push(format!("(declare-const {} Float64)", any_float_sym));
                    vec![
                        format!(
                            "(assert {})",
                            or(&vec![
                                format!("(= {} (int {}))", target_res.val_sym, any_int_sym),
                                format!("(= {} (float {}))", target_res.val_sym, any_float_sym),
                            ])
                        ),
                        format!("(assert (= {} {}))", target_res.bytes_sym, 8),
                    ]
                }
                "string" => {
                    let any_str_sym = format!("{}_{}", target_res.val_sym, type_name);
                    ctx.declarations
                        .borrow_mut()
                        .push(format!("(declare-const {} String)", any_str_sym));
                    let any_str_bytes_sym = format!("{}_{}_bytes", target_res.val_sym, type_name);
                    ctx.declarations
                        .borrow_mut()
                        .push(format!("(declare-const {} Int)", any_str_bytes_sym));
                    vec![
                        format!(
                            "(assert (= {} (str {} {})))",
                            target_res.val_sym, any_str_sym, any_str_bytes_sym
                        ),
                        format!(
                            "(assert (= {} {}))",
                            target_res.bytes_sym, any_str_bytes_sym
                        ),
                    ]
                }
                "list" => {
                    let any_list_sym = format!("{}_{}", target_res.val_sym, type_name);
                    ctx.declarations
                        .borrow_mut()
                        .push(format!("(declare-const {} (Seq Refl))", any_list_sym));
                    let any_list_bytes_sym = format!("{}_{}", target_res.val_sym, type_name);
                    ctx.declarations
                        .borrow_mut()
                        .push(format!("(declare-const {} Int)", any_list_bytes_sym));
                    vec![
                        format!(
                            "(assert (= {} (list {} {})))",
                            target_res.val_sym, any_list_sym, any_list_bytes_sym
                        ),
                        format!(
                            "(assert (= {} {}))",
                            target_res.bytes_sym, any_list_bytes_sym
                        ),
                    ]
                }
                "map" => {
                    let any_map_sym = format!("{}_{}", target_res.val_sym, type_name);
                    ctx.declarations.borrow_mut().push(format!(
                        "(declare-const {} (List (Entry String Refl)))",
                        any_map_sym
                    ));
                    vec![
                        format!("(assert (= {} (map {})))", target_res.val_sym, any_map_sym),
                        format!(
                            "(assert (= {} (list-sum {})))",
                            target_res.bytes_sym, any_map_sym
                        ),
                    ]
                }
                "timestamp" => {
                    vec![
                        format!("(assert (= {} timestamp))", target_res.val_sym),
                        format!("(assert (= {} {}))", target_res.bytes_sym, 8),
                    ]
                }
                "duration" => {
                    vec![
                        format!("(assert (= {} duration))", target_res.val_sym),
                        format!("(assert (= {} {}))", target_res.bytes_sym, 8),
                    ]
                }
                "path" => {
                    vec![
                        format!("(assert (= {} path))", target_res.val_sym),
                        format!("(assert (<= {} {}))", target_res.bytes_sym, 6 * 1024),
                    ]
                }
                "latlng" => {
                    vec![
                        format!("(assert (= {} latlng))", target_res.val_sym),
                        format!("(assert (= {} {}))", target_res.bytes_sym, 8),
                    ]
                }
                _ => vec![],
            }
        }
        ExpressionKind::UnaryOperation(op_lit, op_param_expr) => {
            let op_param_res = check_expression(ctx, &op_param_expr);
            check_function_calling(
                cur_expr,
                ctx,
                &FunctionKind::UnaryOp(*op_lit),
                &vec![&op_param_res],
                &cur_val_sym,
                &cur_bytes_sym,
            )
        }
        ExpressionKind::BinaryOperation(op_lit, op_param1_expr, op_param2_expr) => {
            let op_param1_res = check_expression(ctx, &op_param1_expr);
            let op_param2_res = check_expression(ctx, &op_param2_expr);
            check_function_calling(
                cur_expr,
                ctx,
                &FunctionKind::BinaryOp(*op_lit),
                &vec![&op_param1_res, &op_param2_res],
                &cur_val_sym,
                &cur_bytes_sym,
            )
        }
        ExpressionKind::SubscriptExpression(obj_expr, param_expr) => {
            let obj_res = check_expression(ctx, &obj_expr);
            let param_res = check_expression(ctx, &param_expr);
            check_function_calling(
                cur_expr,
                ctx,
                &FunctionKind::Subscript,
                &vec![&obj_res, &param_res],
                &cur_val_sym,
                &cur_bytes_sym,
            )
        }
        ExpressionKind::FunctionCallExpression(fn_name, params_expr) => {
            let params_res: Vec<_> = params_expr
                .iter()
                .map(|expr| check_expression(ctx, expr))
                .collect();
            check_function_calling(
                cur_expr,
                ctx,
                &FunctionKind::Function(fn_name.clone()),
                &params_res.iter().map(|x| x).collect(),
                &cur_val_sym,
                &cur_bytes_sym,
            )
        }
        ExpressionKind::TernaryOperation(cond_expr, left_expr, right_expr) => {
            let cond_res = check_expression(ctx, &cond_expr);
            let left_res = check_expression(ctx, &left_expr);
            let right_res = check_expression(ctx, &right_expr);
            vec![
                format!(
                    "(assert (= {} (ite (= {} (bool true)) {} {})))",
                    cur_val_sym, cond_res.val_sym, left_res.val_sym, right_res.val_sym
                ),
                format!(
                    "(assert (= {} (ite (= {} (bool true)) {} {})))",
                    cur_bytes_sym, cond_res.bytes_sym, left_res.bytes_sym, right_res.bytes_sym
                ),
            ]
        }
        ExpressionKind::MemberExpression(obj_expr, member_expr) => match &member_expr.kind {
            ExpressionKind::Variable(variable_name) => {
                let obj_res = check_expression(ctx, &obj_expr);
                let member_res = check_expression(ctx, &member_expr);

                let obj_inner_sym = format!("{}_inner", obj_expr.get_id().0);

                vec![
                    format!(
                        "(declare-const {} (List (Entry String Refl)))",
                        obj_inner_sym
                    ),
                    format!("(assert (= {} (map {})))", obj_res.val_sym, obj_inner_sym),
                    format!(
                        "(assert (= {} (str \"{}\" {})))",
                        member_res.val_sym, variable_name, member_res.bytes_sym
                    ),
                    format!(
                        "(assert (= (list-get {} \"{}\") {}))",
                        obj_inner_sym, variable_name, cur_val_sym
                    ),
                ]
            }
            _ => panic!(),
        },
    };
    ctx.declarations.borrow_mut().append(&mut declarations);
    Res {
        val_sym: cur_val_sym,
        bytes_sym: cur_bytes_sym,
    }
}

fn run_z3(source: &String) -> String {
    debug!("{}", source);
    let mut debug_source = "".to_owned();
    let mut line_count = 0;
    for line in source.split("\n") {
        debug_source += format!("{}: {}\n", line_count + 1, line).as_str();
        line_count += 1;
    }
    info!("RUN Z3:\n{}", debug_source);
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
        Some(error) => {
            eprintln!("Z3 Error: {}", error);
            panic!()
        }
        _ => panic!(),
    }
}

fn check_rule(ctx: &AnalysysGlobalContext, rule: &Rule) -> Vec<AnalysysError> {
    info!(
        "check rule at {} line",
        rule.get_span().0.start_point.row + 1
    );

    let ctx = AnalysysContext {
        bindings: ctx.bindings,
        symbol_references: ctx.symbol_references,
        source_code: ctx.source_code,
        variable_bindings: &HashMap::new(),
        declarations: &RefCell::new(vec![format!(
            r#"
(declare-datatypes (T1 T2) ((Entry (entry (key T1) (value T2)))))

(declare-datatypes ((Refl 0)) (
    (
        (undefined)
        (null)
        (bool (bool_val Bool))
        (int (int_val Int))
        (float (float_val Float64))
        (str (str_val String) (str_bytes Int))
        (char (char_val Unicode) (char_bytes Int))
        (duration)
        (latlng)
        (timestamp)
        (list (list_val (Seq Refl)) (list_bytes Int))
        (map (map_val (List (Entry String Refl))))
        (mapdiff (mapdiff_left (List (Entry String Refl))) (mapdiff_right (List (Entry String Refl))))
        (path)
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
    list-exists
    (
        (lst (List (Entry String Refl)))
        (sk String)
    )
    Bool
    (if
        (= lst nil)
        false
        (if
            (= (key (head lst)) sk)
            true
            (list-exists (tail lst) sk)
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

(define-fun-rec
    list-sum
    (
        (lst (List (Entry String Refl)))
    )
    Int
    (if
        (= lst nil)
        0
        (if
            (= (value (head lst)) undefined)
            0
            (+
                2
                (match (value (head lst)) (
                    (undefined (* 1024 1024))
                    (null 1)
                    ((bool x) 1)
                    ((int x) 8)
                    ((float x) 8)
                    ((str v b) b)
                    ((char v b) b)
                    (duration 8)
                    (latlng 16)
                    (timestamp 8)
                    ((list v b) b)
                    ((map x) (list-sum x))
                    ((mapdiff l r) (* 1024 1024))
                    (path (* 6 1024))
                ))
                (list-sum (tail lst))
            )
        )
    )
)

(declare-const request_resource_data Refl)
(declare-const request_resource_data_inner (List (Entry String Refl)))
(assert (= request_resource_data (map request_resource_data_inner)))

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

    let Res {
        val_sym: condition_val_sym,
        bytes_sym: _,
    } = check_expression(&ctx, &rule.condition);

    let mut errors = vec![];

    // check always false
    {
        info!("check always false");
        let source_code = format!(
            "{}

{}
",
            ctx.declarations.borrow().join("\n"),
            format!("(assert (= {} (bool true)))", condition_val_sym)
        );
        match solve(&source_code) {
            SolverResult::Sat(example) => {
                info!("sat");
                info!("truthly example:\n{}", example);
            }
            SolverResult::Unsat => {
                info!("unsat");
                errors.push(AnalysysError::new(format!("Always false"), rule))
            }
            SolverResult::Unknown => errors.push(AnalysysError::new(
                format!("Static analysis failed because this conditions are too complex."),
                rule,
            )),
        }
    }

    // 1MB limit
    {
        info!("check 1MB limit");
        let source_code = format!(
            "{}

{}
{}
",
            ctx.declarations.borrow().join("\n"),
            format!("(assert (= {} (bool true)))", condition_val_sym),
            format!("(assert (> (list-sum request_resource_data_inner) 262144))")
        );
        match solve(&source_code) {
            SolverResult::Sat(example) => {
                errors.push(AnalysysError::new(format!("over 1MB limit"), rule));
                info!("sat");
                info!("truthly example:\n{}", example);
            }
            SolverResult::Unsat => {
                info!("unsat");
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
