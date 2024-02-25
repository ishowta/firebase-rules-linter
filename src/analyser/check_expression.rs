use std::{borrow::BorrowMut, iter::zip};

use crate::{
    analyser::destruct_sort::destruct_string,
    ast::{Expression, ExpressionKind},
    symbol::{FunctionNodeRef, VariableNodeRef},
    ty::FunctionKind,
};

use super::{
    check_function::check_function_calling,
    check_global_function::check_global_function_calling,
    destruct_sort::destruct_bool,
    types::{AnalysysContext, Res},
    z3::{Constraint, Declaration, Literal, Sort, Symbol},
};

fn expression_to_name(expr: &Expression) -> String {
    match expr.kind.clone() {
        ExpressionKind::Literal(lit) => format!(
            "lit_{}",
            match lit {
                crate::ast::Literal::Null => "null",
                crate::ast::Literal::Bool(_) => "bool",
                crate::ast::Literal::Int(_) => "int",
                crate::ast::Literal::Float(_) => "float",
                crate::ast::Literal::String(_) => "str",
                crate::ast::Literal::List(_) => "list",
                crate::ast::Literal::Map(_) => "map",
                crate::ast::Literal::Path(_) => "path",
            }
        ),
        ExpressionKind::Variable(x) => x,
        ExpressionKind::UnaryOperation(lit, _) => match lit {
            crate::ast::UnaryLiteral::Not => "not".to_owned(),
            crate::ast::UnaryLiteral::Minus => "minus".to_owned(),
        },
        ExpressionKind::BinaryOperation(lit, _, _) => match lit {
            crate::ast::BinaryLiteral::And => "and".to_owned(),
            crate::ast::BinaryLiteral::Or => "or".to_owned(),
            crate::ast::BinaryLiteral::Add => "add".to_owned(),
            crate::ast::BinaryLiteral::Sub => "sub".to_owned(),
            crate::ast::BinaryLiteral::Mul => "mul".to_owned(),
            crate::ast::BinaryLiteral::Div => "div".to_owned(),
            crate::ast::BinaryLiteral::Mod => "mod".to_owned(),
            crate::ast::BinaryLiteral::Gt => "gt".to_owned(),
            crate::ast::BinaryLiteral::Gte => "gte".to_owned(),
            crate::ast::BinaryLiteral::Lt => "lt".to_owned(),
            crate::ast::BinaryLiteral::Lte => "lte".to_owned(),
            crate::ast::BinaryLiteral::Eq => "eq".to_owned(),
            crate::ast::BinaryLiteral::NotEq => "notEq".to_owned(),
            crate::ast::BinaryLiteral::In => "in".to_owned(),
        },
        ExpressionKind::TernaryOperation(_, _, _) => format!("if"),
        ExpressionKind::TypeCheckOperation(_, ty) => format!("is_{}", ty),
        ExpressionKind::MemberExpression(obj, member) => {
            format!(
                "{}_{}",
                expression_to_name(&obj),
                expression_to_name(&member)
            )
        }
        ExpressionKind::SubscriptExpression(obj, member) => format!(
            "{}_{}",
            expression_to_name(&obj),
            expression_to_name(&member)
        ),
        ExpressionKind::FunctionCallExpression(name, _) => name,
    }
}

pub fn check_expression(ctx: &AnalysysContext, cur_expr: &Expression) -> Res {
    let cur_value = Symbol::new(cur_expr, expression_to_name(cur_expr).as_str());
    ctx.declarations
        .borrow_mut()
        .push(Declaration::new(&cur_value, &Sort::Refl));

    let constraints = match &cur_expr.kind {
        ExpressionKind::Literal(lit) => match lit {
            crate::ast::Literal::Null => {
                vec![Constraint::new2("=", &cur_value, &Constraint::mono("null"))]
            }
            crate::ast::Literal::Bool(lit) => {
                vec![Constraint::new2(
                    "=",
                    &cur_value,
                    &Constraint::new1("bool", lit),
                )]
            }
            crate::ast::Literal::Int(lit) => {
                vec![Constraint::new2(
                    "=",
                    &cur_value,
                    &Constraint::new1("int", lit),
                )]
            }
            crate::ast::Literal::Float(_) => {
                vec![Constraint::new2(
                    "=",
                    &cur_value,
                    &Constraint::mono("float"),
                )]
            }
            crate::ast::Literal::String(lit) => vec![Constraint::new2(
                "=",
                &cur_value,
                &Constraint::new2("str", lit, &Literal::from(lit.len())),
            )],
            crate::ast::Literal::List(lit) => {
                let elems_res: Vec<_> = lit
                    .iter()
                    .map(|elem_lit| check_expression(ctx, elem_lit))
                    .collect();

                vec![
                    Constraint::new2(
                        "=",
                        &cur_value,
                        &Constraint::new2(
                            "list",
                            &elems_res.iter().fold(
                                Constraint::new1("as nil", &Sort::List(Box::new(Sort::Refl))),
                                |acc, elem| Constraint::new2("insert", &elem.value, &acc),
                            ),
                            &elems_res.iter().fold(
                                Constraint::from(Literal::from(0)),
                                |acc, elem| {
                                    Constraint::new2(
                                        "+",
                                        &Constraint::new1("refl-sum", &(elem.value)),
                                        &acc,
                                    )
                                },
                            ),
                        ),
                    ),
                    Constraint::new(
                        "and",
                        elems_res.iter().flat_map(|res| &res.constraints).collect(),
                    ),
                ]
            }
            crate::ast::Literal::Map(lit) => {
                let elems_res: Vec<_> = lit
                    .iter()
                    .map(|(key, value_expr)| (key, check_expression(ctx, value_expr)))
                    .collect();

                vec![
                    Constraint::new2(
                        "=",
                        &cur_value,
                        &Constraint::new1(
                            "map",
                            &elems_res.iter().fold(
                                Constraint::new1("as nil", &Sort::Map),
                                |acc, (key, value)| {
                                    Constraint::new2(
                                        "insert",
                                        &Constraint::new2("entry", *key, &value.value),
                                        &acc,
                                    )
                                },
                            ),
                        ),
                    ),
                    Constraint::new(
                        "and",
                        elems_res
                            .iter()
                            .flat_map(|(_, res)| &res.constraints)
                            .collect(),
                    ),
                ]
            }
            crate::ast::Literal::Path(_) => {
                vec![Constraint::new2("=", &cur_value, &Constraint::mono("path"))]
            }
        },
        ExpressionKind::Variable(name) => match ctx
            .bindings
            .variable_table
            .get(&cur_expr.id)
            .and_then(|node| Some(node.1))
        {
            None => vec![],
            Some(variable_node_ref) => match variable_node_ref {
                VariableNodeRef::LetBinding(node) => {
                    let value = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![Constraint::new2("=", &cur_value, value)]
                }
                VariableNodeRef::FunctionArgument(node) => {
                    let value = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![Constraint::new2("=", &cur_value, value)]
                }
                VariableNodeRef::PathCapture(_) => {
                    let path_capture_sym = Symbol::new(cur_expr, "path_capture");
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&path_capture_sym, &Sort::Refl));
                    let (_, _, path_capture_constraint) = destruct_string(
                        &path_capture_sym,
                        cur_expr,
                        ctx.declarations.borrow_mut().as_mut(),
                    );
                    vec![
                        path_capture_constraint,
                        Constraint::new2("=", &cur_value, &path_capture_sym),
                    ]
                }
                VariableNodeRef::PathCaptureGroup(_) => {
                    let path_capture_group_sym = Symbol::new(cur_expr, "path_capture_group");
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&path_capture_group_sym, &Sort::Refl));
                    let (_, _, path_capture_group_constraint) = destruct_string(
                        &path_capture_group_sym,
                        cur_expr,
                        ctx.declarations.borrow_mut().as_mut(),
                    );
                    vec![
                        path_capture_group_constraint,
                        Constraint::new2("=", &cur_value, &path_capture_group_sym),
                    ]
                }
                VariableNodeRef::GlobalVariable(_) => match name.as_str() {
                    "request" => {
                        vec![Constraint::new2(
                            "=",
                            &cur_value,
                            &Symbol {
                                smtlib2: "request".to_string(),
                            },
                        )]
                    }
                    "resource" => {
                        vec![Constraint::new2(
                            "=",
                            &cur_value,
                            &Symbol {
                                smtlib2: "resource".to_string(),
                            },
                        )]
                    }
                    _ => panic!(),
                },
            },
        },
        ExpressionKind::TypeCheckOperation(target_expr, type_name) => {
            let target_res = check_expression(ctx, &target_expr);
            let (current_val, current_constraint) = destruct_bool(
                &cur_value,
                target_expr as &Expression,
                ctx.declarations.borrow_mut().as_mut(),
            );
            let mut constraints = target_res.constraints;
            constraints.push(current_constraint);
            constraints.extend(match type_name.as_str() {
                "bool" => {
                    let inner_sym = Symbol::new(target_expr as &Expression, "bool");
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_sym, &Sort::Bool));
                    vec![Constraint::new2(
                        "=",
                        &current_val,
                        &Constraint::new2(
                            "=",
                            &target_res.value,
                            &Constraint::new1("bool", &inner_sym),
                        ),
                    )]
                }
                "int" => {
                    let inner_sym = Symbol::new(target_expr as &Expression, "int");
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_sym, &Sort::Int));
                    vec![Constraint::new2(
                        "=",
                        &current_val,
                        &Constraint::new2(
                            "=",
                            &target_res.value,
                            &Constraint::new1("int", &inner_sym),
                        ),
                    )]
                }
                "float" => {
                    vec![Constraint::new2(
                        "=",
                        &current_val,
                        &Constraint::new2("=", &target_res.value, &Constraint::mono("float")),
                    )]
                }
                "number" => {
                    let inner_int_sym = Symbol::new(target_expr as &Expression, "number");
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_int_sym, &Sort::Int));
                    vec![Constraint::new2(
                        "=",
                        &current_val,
                        &Constraint::new2(
                            "or",
                            &Constraint::new2(
                                "=",
                                &target_res.value,
                                &Constraint::new1("int", &inner_int_sym),
                            ),
                            &Constraint::new2("=", &target_res.value, &Constraint::mono("float")),
                        ),
                    )]
                }
                "string" => {
                    let inner_value = Symbol::new(target_expr as &Expression, "str");
                    let inner_bytes_sym = Symbol::new(target_expr as &Expression, "str_bytes");
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_value, &Sort::String));
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_bytes_sym, &Sort::Int));
                    vec![Constraint::new2(
                        "=",
                        &current_val,
                        &Constraint::new2(
                            "=",
                            &target_res.value,
                            &Constraint::new2("str", &inner_value, &inner_bytes_sym),
                        ),
                    )]
                }
                "list" => {
                    let inner_value = Symbol::new(target_expr as &Expression, "list");
                    let inner_bytes_sym = Symbol::new(target_expr as &Expression, "list_bytes");
                    ctx.declarations.borrow_mut().push(Declaration::new(
                        &inner_value,
                        &Sort::List(Box::new(Sort::Refl)),
                    ));
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_bytes_sym, &Sort::Int));
                    vec![Constraint::new2(
                        "=",
                        &current_val,
                        &Constraint::new2(
                            "=",
                            &target_res.value,
                            &Constraint::new2("list", &inner_value, &inner_bytes_sym),
                        ),
                    )]
                }
                "map" => {
                    let inner_sym = Symbol::new(target_expr as &Expression, "map");
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_sym, &Sort::Map));
                    vec![Constraint::new2(
                        "=",
                        &current_val,
                        &Constraint::new2(
                            "=",
                            &target_res.value,
                            &Constraint::new1("map", &inner_sym),
                        ),
                    )]
                }
                "timestamp" => {
                    vec![Constraint::new2(
                        "=",
                        &current_val,
                        &Constraint::new2("=", &target_res.value, &Constraint::mono("timestamp")),
                    )]
                }
                "duration" => {
                    vec![Constraint::new2(
                        "=",
                        &current_val,
                        &Constraint::new2("=", &target_res.value, &Constraint::mono("duration")),
                    )]
                }
                "path" => {
                    vec![Constraint::new2(
                        "=",
                        &current_val,
                        &Constraint::new2("=", &target_res.value, &Constraint::mono("path")),
                    )]
                }
                "latlng" => {
                    vec![Constraint::new2(
                        "=",
                        &current_val,
                        &Constraint::new2("=", &target_res.value, &Constraint::mono("latlng")),
                    )]
                }
                _ => vec![],
            });
            constraints
        }
        ExpressionKind::UnaryOperation(op_lit, op_param_expr) => {
            let op_param_res = check_expression(ctx, &op_param_expr);
            check_function_calling(
                cur_expr,
                ctx,
                &FunctionKind::UnaryOp(*op_lit),
                &vec![&op_param_res],
                &cur_value,
                ctx.declarations.borrow_mut().as_mut(),
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
                &cur_value,
                ctx.declarations.borrow_mut().as_mut(),
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
                &cur_value,
                ctx.declarations.borrow_mut().as_mut(),
            )
        }
        ExpressionKind::FunctionCallExpression(fn_name, params_expr) => {
            let params_res: Vec<_> = params_expr
                .iter()
                .map(|expr| check_expression(ctx, expr))
                .collect();
            match ctx
                .bindings
                .function_table
                .get(&cur_expr.id)
                .and_then(|node| Some(&node.1))
            {
                Some(FunctionNodeRef::Function(function)) => {
                    let mut constraints: Vec<Constraint> = params_res
                        .iter()
                        .flat_map(|res| res.constraints.clone())
                        .collect();
                    let mut variable_bindings = ctx.variable_bindings.clone();

                    // args
                    if function.arguments.len() != params_expr.len() {
                        panic!()
                    }
                    for (arg, param) in zip(&function.arguments, params_res) {
                        variable_bindings.insert(&arg.id, param.value.clone());
                    }

                    // let bindings
                    for let_binding in &function.let_bindings {
                        let let_res = check_expression(
                            &AnalysysContext {
                                bindings: ctx.bindings,
                                symbol_references: ctx.symbol_references,
                                source_code: ctx.source_code,
                                declarations: ctx.declarations,
                                quick_mode: ctx.quick_mode,
                                variable_bindings: &variable_bindings,
                            },
                            &let_binding.expression,
                        );
                        variable_bindings.insert(&let_binding.id, let_res.value.clone());
                        constraints.extend(let_res.constraints);
                    }

                    // return expression
                    let return_res = check_expression(
                        &AnalysysContext {
                            bindings: ctx.bindings,
                            symbol_references: ctx.symbol_references,
                            source_code: ctx.source_code,
                            declarations: ctx.declarations,
                            quick_mode: ctx.quick_mode,
                            variable_bindings: &variable_bindings,
                        },
                        &function.return_expression,
                    );
                    constraints.extend(return_res.constraints);
                    constraints.push(Constraint::new2("=", &return_res.value, &cur_value));

                    constraints
                }
                Some(FunctionNodeRef::GlobalFunction(namespace, _, _)) => {
                    check_global_function_calling(
                        cur_expr,
                        ctx,
                        namespace,
                        &fn_name,
                        &params_res.iter().map(|x| x).collect(),
                        &cur_value,
                        ctx.declarations.borrow_mut().as_mut(),
                    )
                }
                None => panic!(),
            }
        }
        ExpressionKind::TernaryOperation(cond_expr, left_expr, right_expr) => {
            let cond_res = check_expression(ctx, &cond_expr);
            let left_res = check_expression(ctx, &left_expr);
            let right_res = check_expression(ctx, &right_expr);
            let (left_val, left_constraint) = destruct_bool(
                &left_res.value,
                left_expr as &Expression,
                ctx.declarations.borrow_mut().as_mut(),
            );
            let (right_val, right_constraint) = destruct_bool(
                &right_res.value,
                right_expr as &Expression,
                ctx.declarations.borrow_mut().as_mut(),
            );
            vec![Constraint::new2(
                "=",
                &cur_value,
                &Constraint::new1(
                    "bool",
                    &Constraint::new3(
                        "and",
                        &left_constraint,
                        &right_constraint,
                        &Constraint::new3(
                            "ite",
                            &Constraint::new2(
                                "and",
                                &Constraint::new2(
                                    "=",
                                    &cond_res.value,
                                    &Constraint::new1("bool", &true),
                                ),
                                &Constraint::new("and", cond_res.constraints.iter().collect()),
                            ),
                            &Constraint::new2(
                                "and",
                                &left_val,
                                &Constraint::new("and", left_res.constraints.iter().collect()),
                            ),
                            &Constraint::new2(
                                "and",
                                &right_val,
                                &Constraint::new("and", right_res.constraints.iter().collect()),
                            ),
                        ),
                    ),
                ),
            )]
        }
        ExpressionKind::MemberExpression(obj_expr, member_expr) => {
            // check is namespace
            if let Some(_) = ctx.bindings.function_table.get(&member_expr.id) {
                return check_expression(ctx, &member_expr);
            }

            match &member_expr.kind {
                ExpressionKind::Variable(variable_name) => {
                    let obj_res = check_expression(ctx, &obj_expr);
                    let member_res = check_expression(ctx, &member_expr);

                    let obj_inner_sym = Symbol::new(obj_expr as &Expression, "obj_map");
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&obj_inner_sym, &Sort::Map));

                    obj_res
                        .constraints
                        .iter()
                        .chain(member_res.constraints.iter())
                        .chain(
                            [
                                Constraint::new2(
                                    "=",
                                    &obj_res.value,
                                    &Constraint::new1("map", &obj_inner_sym),
                                ),
                                Constraint::new2("=", &cur_value, &member_res.value),
                                Constraint::new2(
                                    "=",
                                    &member_res.value,
                                    &Constraint::new2("list-get", &obj_inner_sym, variable_name),
                                ),
                            ]
                            .iter(),
                        )
                        .cloned()
                        .collect()
                }
                ExpressionKind::FunctionCallExpression(fn_name, params_expr) => {
                    let obj_res = check_expression(ctx, &obj_expr);
                    let params_res: Vec<_> = params_expr
                        .iter()
                        .map(|expr| check_expression(ctx, expr))
                        .collect();
                    let mut params = vec![&obj_res];
                    params.extend(params_res.iter().map(|x| x));
                    check_function_calling(
                        cur_expr,
                        ctx,
                        &FunctionKind::Function(fn_name.clone()),
                        &params,
                        &cur_value,
                        ctx.declarations.borrow_mut().as_mut(),
                    )
                }
                _ => panic!(),
            }
        }
    };
    Res {
        value: cur_value,
        constraints: constraints,
    }
}
