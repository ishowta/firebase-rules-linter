use crate::{
    ast::{Expression, ExpressionKind},
    symbol::VariableNodeRef,
    ty::FunctionKind,
};

use super::{
    check_function::check_function_calling,
    types::{AnalysysContext, Res},
    z3::{Constraint, Declaration, Literal, Sort, Symbol},
};

pub fn check_expression(ctx: &AnalysysContext, cur_expr: &Expression) -> Res {
    let cur_value = Symbol::new(cur_expr);
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
                        &Constraint::new2(
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
                            &elems_res.iter().fold(
                                Constraint::from(Literal::from(0)),
                                |acc, (_, value)| {
                                    Constraint::new2(
                                        "+",
                                        &2,
                                        &Constraint::new2(
                                            "+",
                                            &Constraint::new1("refl-sum", &value.value),
                                            &acc,
                                        ),
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
            crate::ast::Literal::Path(_) => vec![Constraint::new2("=", &cur_value, &"path")],
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
                    let value = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![Constraint::new2("=", &cur_value, *value)]
                }
                VariableNodeRef::FunctionArgument(node) => {
                    let value = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![Constraint::new2("=", &cur_value, *value)]
                }
                VariableNodeRef::PathCapture(node) => {
                    let value = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![Constraint::new2("=", &cur_value, *value)]
                }
                VariableNodeRef::PathCaptureGroup(node) => {
                    let value = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![Constraint::new2("=", &cur_value, *value)]
                }
                VariableNodeRef::GlobalVariable(_) => {
                    // TODO
                    vec![Constraint::new2(
                        "=",
                        &cur_value,
                        &Symbol {
                            smtlib2: "request_resource_data".to_string(),
                        },
                    )]
                }
            },
        },
        ExpressionKind::TypeCheckOperation(target_expr, type_name) => {
            let target_res = check_expression(ctx, &target_expr);
            match type_name.as_str() {
                "bool" => {
                    let inner_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_sym, &Sort::Bool));
                    vec![Constraint::new2(
                        "=",
                        &target_res.value,
                        &Constraint::new1("bool", &inner_sym),
                    )]
                }
                "int" => {
                    let inner_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_sym, &Sort::Int));
                    vec![Constraint::new2(
                        "=",
                        &target_res.value,
                        &Constraint::new1("int", &inner_sym),
                    )]
                }
                "float" => {
                    vec![Constraint::new2(
                        "=",
                        &target_res.value,
                        &Constraint::mono("float"),
                    )]
                }
                "number" => {
                    let inner_int_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_int_sym, &Sort::Int));
                    vec![Constraint::new2(
                        "or",
                        &Constraint::new2(
                            "=",
                            &target_res.value,
                            &Constraint::new1("int", &inner_int_sym),
                        ),
                        &Constraint::new2("=", &target_res.value, &Constraint::mono("float")),
                    )]
                }
                "string" => {
                    let inner_value = Symbol::new(target_expr as &Expression);
                    let inner_bytes_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_value, &Sort::String));
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_bytes_sym, &Sort::Int));
                    vec![Constraint::new2(
                        "=",
                        &target_res.value,
                        &Constraint::new2("str", &inner_value, &inner_bytes_sym),
                    )]
                }
                "list" => {
                    let inner_value = Symbol::new(target_expr as &Expression);
                    let inner_bytes_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations.borrow_mut().push(Declaration::new(
                        &inner_value,
                        &Sort::List(Box::new(Sort::Refl)),
                    ));
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_bytes_sym, &Sort::Int));
                    vec![Constraint::new2(
                        "=",
                        &target_res.value,
                        &Constraint::new2("list", &inner_value, &inner_bytes_sym),
                    )]
                }
                "map" => {
                    let inner_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_sym, &Sort::Map));
                    vec![Constraint::new2(
                        "=",
                        &target_res.value,
                        &Constraint::new2(
                            "map",
                            &inner_sym,
                            &Constraint::new1("list-sum", &inner_sym),
                        ),
                    )]
                }
                "timestamp" => {
                    vec![Constraint::new2(
                        "=",
                        &target_res.value,
                        &Constraint::mono("timestamp"),
                    )]
                }
                "duration" => {
                    vec![Constraint::new2(
                        "=",
                        &target_res.value,
                        &Constraint::mono("duration"),
                    )]
                }
                "path" => {
                    vec![Constraint::new2(
                        "=",
                        &target_res.value,
                        &Constraint::mono("path"),
                    )]
                }
                "latlng" => {
                    vec![Constraint::new2(
                        "=",
                        &target_res.value,
                        &Constraint::mono("latlng"),
                    )]
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
            check_function_calling(
                cur_expr,
                ctx,
                &FunctionKind::Function(fn_name.clone()),
                &params_res.iter().map(|x| x).collect(),
                &cur_value,
                ctx.declarations.borrow_mut().as_mut(),
            )
        }
        ExpressionKind::TernaryOperation(cond_expr, left_expr, right_expr) => {
            let cond_res = check_expression(ctx, &cond_expr);
            let left_res = check_expression(ctx, &left_expr);
            let right_res = check_expression(ctx, &right_expr);
            vec![Constraint::new2(
                "=",
                &cur_value,
                &Constraint::new3(
                    "ite",
                    &Constraint::new2(
                        "and",
                        &Constraint::new2("=", &cond_res.value, &Constraint::new1("bool", &true)),
                        &Constraint::new("and", cond_res.constraints.iter().collect()),
                    ),
                    &Constraint::new2(
                        "and",
                        &left_res.value,
                        &Constraint::new("and", left_res.constraints.iter().collect()),
                    ),
                    &Constraint::new2(
                        "and",
                        &right_res.value,
                        &Constraint::new("and", right_res.constraints.iter().collect()),
                    ),
                ),
            )]
        }
        ExpressionKind::MemberExpression(obj_expr, member_expr) => match &member_expr.kind {
            ExpressionKind::Variable(variable_name) => {
                let obj_res = check_expression(ctx, &obj_expr);
                let member_res = check_expression(ctx, &member_expr);

                let obj_inner_sym = Symbol::new(obj_expr as &Expression);
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
        },
    };
    Res {
        value: cur_value,
        constraints: constraints,
    }
}
