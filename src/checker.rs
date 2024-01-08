use core::panic;
use std::{collections::HashMap, iter::zip};

use crate::{
    ast::{
        Ast, BinaryLiteral, Expression, ExpressionKind, Function, Literal, Node, NodeID, Rule,
        RuleGroup,
    },
    symbol::{Bindings, FunctionNodeRef, SymbolReferences, VariableNodeRef},
    ty::{FunctionKind, Interface, MemberKind, TypeKind},
};

#[derive(Clone, Debug)]
pub struct TypeCheckResult<'a> {
    pub node: &'a dyn Node,
    pub reason: String,
}

#[derive(Clone, Debug)]
pub struct TypeCheckContext<'a> {
    pub bindings: &'a Bindings<'a>,
    pub symbol_references: &'a SymbolReferences<'a>,
    pub interfaces: &'a HashMap<TypeKind, Interface>,
}

#[derive(Clone, Debug)]
pub struct Flow<'a> {
    pub context: HashMap<&'a NodeID, TypeKind>,
}

fn assert_type<'a, 'b>(
    ty: &'b TypeKind,
    kind: &'b TypeKind,
    expr: &'a Expression,
) -> Option<TypeCheckResult<'a>> {
    if ty != kind && *ty != TypeKind::Any && *kind != TypeKind::Any {
        Some(TypeCheckResult {
            node: expr,
            reason: format!("Expected {:?}, Get {:?}", kind, ty).into(),
        })
    } else {
        None
    }
}

fn assert_type_candidates<'a, 'b>(
    ty: &'b TypeKind,
    kind_candidates: Vec<&'b TypeKind>,
    expr: &'a Expression,
) -> Option<TypeCheckResult<'a>> {
    let passed = !kind_candidates.iter().all(|kind_candidate| {
        ty != *kind_candidate && *ty != TypeKind::Any && **kind_candidate != TypeKind::Any
    });
    if passed {
        None
    } else {
        Some(TypeCheckResult {
            node: expr,
            reason: format!("Expected {:?}, Get {:?}", kind_candidates, ty).into(),
        })
    }
}

fn check_function_args<'a>(
    expr: &'a dyn Node,
    functions: &Vec<(Vec<TypeKind>, TypeKind)>,
    args: Vec<TypeKind>,
) -> (TypeKind, Vec<TypeCheckResult<'a>>) {
    if let Some(return_ty) = functions.iter().find_map(|(params, return_ty)| {
        if zip(&args, params)
            .all(|(arg, param)| arg == param || *arg == TypeKind::Any || *param == TypeKind::Any)
        {
            Some(return_ty)
        } else {
            None
        }
    }) {
        (*return_ty, vec![])
    } else {
        (
            TypeKind::Any,
            vec![TypeCheckResult {
                node: expr,
                reason: "function or operator type mismatch".into(),
            }],
        )
    }
}

fn check_interface_function_calling<'a>(
    node: &'a dyn Node,
    context: &'a TypeCheckContext,
    interface_ty: TypeKind,
    function_kind: FunctionKind,
    args: Vec<TypeKind>,
) -> (TypeKind, Vec<TypeCheckResult<'a>>) {
    if interface_ty == TypeKind::Any {
        return (TypeKind::Any, vec![]);
    }
    if function_kind == FunctionKind::BinaryOp(BinaryLiteral::Eq)
        || function_kind == FunctionKind::BinaryOp(BinaryLiteral::NotEq)
    {
        if interface_ty == TypeKind::Null || args[0] == TypeKind::Null {
            return (TypeKind::Boolean, vec![]);
        }
    }
    if let Some(functions) = context
        .interfaces
        .get(&interface_ty)
        .unwrap()
        .functions
        .get(&function_kind)
    {
        check_function_args(node, functions, args)
    } else {
        (
            TypeKind::Any,
            vec![TypeCheckResult {
                node: node,
                reason: format!(
                    "function or operator not found. {:?} with {:?}",
                    interface_ty, function_kind
                )
                .into(),
            }],
        )
    }
}

fn check_function<'a, 'b, 'c>(
    caller: &'a dyn Node,
    function: &'a Function,
    params: &'b Vec<TypeKind>,
    context: &'a TypeCheckContext<'a>,
    flow: &'c Flow,
) -> (TypeKind, Vec<TypeCheckResult<'a>>) {
    let mut res: Vec<TypeCheckResult<'a>> = vec![];
    if function.arguments.len() != params.len() {
        res.push(TypeCheckResult {
            node: caller,
            reason: format!(
                "params length not matched. expected {} but get {}",
                function.arguments.len(),
                params.len()
            )
            .into(),
        })
    }
    let mut flow = flow.clone();
    for (arg, param) in zip(&function.arguments, params) {
        flow.context.insert(&arg.id, *param);
    }
    let (return_ty, return_res) = check_expression(&function.return_expression, context, &flow);
    (return_ty, res.into_iter().chain(return_res).collect())
}

fn check_expression<'a, 'b>(
    expr: &'a Expression,
    context: &'a TypeCheckContext<'a>,
    flow: &'b Flow,
) -> (TypeKind, Vec<TypeCheckResult<'a>>) {
    match &expr.kind {
        ExpressionKind::Literal(Literal::Bool(_)) => (TypeKind::Boolean, vec![]),
        ExpressionKind::Literal(Literal::Float(_)) => (TypeKind::Float, vec![]),
        ExpressionKind::Literal(Literal::Int(_)) => (TypeKind::Integer, vec![]),
        ExpressionKind::Literal(Literal::String(_)) => (TypeKind::String, vec![]),
        ExpressionKind::Literal(Literal::List(_)) => (TypeKind::List, vec![]),
        ExpressionKind::Literal(Literal::Path(_)) => (TypeKind::Path, vec![]),
        ExpressionKind::Literal(Literal::Null) => (TypeKind::Null, vec![]),
        ExpressionKind::Variable(_) => match context
            .bindings
            .variable_table
            .get(&expr.id)
            .and_then(|node| Some(node.1))
        {
            Some(VariableNodeRef::LetBinding(node)) => {
                check_expression(&node.expression, context, flow)
            }
            Some(VariableNodeRef::FunctionArgument(arg)) => {
                (*flow.context.get(&arg.id).unwrap(), vec![])
            }
            Some(VariableNodeRef::PathCapture(_)) => (TypeKind::String, vec![]),
            Some(VariableNodeRef::PathCaptureGroup(_)) => (TypeKind::String, vec![]),
            Some(VariableNodeRef::GlobalVariable(type_kind)) => (*type_kind, vec![]),
            None => panic!(
                "{:?} not found in {:?}",
                expr, context.bindings.variable_table
            ),
        },
        ExpressionKind::UnaryOperation(literal, op_expr) => {
            let (op_ty, op_res) = check_expression(&op_expr, context, flow);
            let (return_ty, return_res) = check_interface_function_calling(
                expr,
                context,
                op_ty,
                FunctionKind::UnaryOp(*literal),
                vec![],
            );
            (return_ty, op_res.into_iter().chain(return_res).collect())
        }
        ExpressionKind::BinaryOperation(literal, left_expr, right_expr) => {
            let (left_ty, left_res) = check_expression(&left_expr, context, flow);
            let (right_ty, right_res) = check_expression(&right_expr, context, flow);
            let (return_ty, return_res) = if *literal == BinaryLiteral::In {
                check_interface_function_calling(
                    expr,
                    context,
                    right_ty,
                    FunctionKind::BinaryOp(*literal),
                    vec![left_ty],
                )
            } else {
                check_interface_function_calling(
                    expr,
                    context,
                    left_ty,
                    FunctionKind::BinaryOp(*literal),
                    vec![right_ty],
                )
            };
            (
                return_ty,
                left_res
                    .into_iter()
                    .chain(right_res)
                    .chain(return_res)
                    .collect(),
            )
        }
        ExpressionKind::TernaryOperation(cond_expr, true_expr, false_expr) => {
            let (cond_ty, mut cond_res) = check_expression(&cond_expr, context, flow);
            if let Some(res_assert) = assert_type(&cond_ty, &TypeKind::Boolean, &cond_expr) {
                cond_res.push(res_assert);
            }
            let (true_ty, true_res) = check_expression(&true_expr, context, flow);
            let (false_ty, false_res) = check_expression(&false_expr, context, flow);
            let assert_res = assert_type(&true_ty, &false_ty, expr);
            (
                if true_ty == TypeKind::Any {
                    false_ty
                } else {
                    true_ty
                },
                cond_res
                    .into_iter()
                    .chain(true_res)
                    .chain(false_res)
                    .chain(if let Some(res) = assert_res {
                        vec![res]
                    } else {
                        vec![]
                    })
                    .collect(),
            )
        }
        ExpressionKind::TypeCheckOperation(target_expr, type_str) => {
            let type_str_ty_candidates = match &**type_str {
                "bool" => vec![&TypeKind::Boolean],
                "int" => vec![&TypeKind::Integer],
                "float" => vec![&TypeKind::Float],
                "number" => vec![&TypeKind::Integer, &TypeKind::Float],
                "string" => vec![&TypeKind::String],
                "list" => vec![&TypeKind::List],
                "map" => vec![&TypeKind::Map],
                "timestamp" => vec![&TypeKind::Timestamp],
                "duration" => vec![&TypeKind::Duration],
                "path" => vec![&TypeKind::Path],
                "latlng" => vec![&TypeKind::LatLng],
                _ => panic!(),
            };
            let (target_ty, mut res) = check_expression(&target_expr, context, flow);
            if let Some(res_assert) =
                assert_type_candidates(&target_ty, type_str_ty_candidates, expr)
            {
                res.push(res_assert);
            }
            (TypeKind::Boolean, res)
        }
        ExpressionKind::MemberExpression(obj_expr, member_expr) => {
            // check is namespace
            if let Some(_) = context.bindings.function_table.get(&member_expr.id) {
                return check_expression(&member_expr, context, flow);
            }

            let (obj_ty, mut res) = check_expression(&obj_expr, context, flow);
            if obj_ty == TypeKind::Any {
                return (obj_ty, res);
            }
            match &member_expr.kind {
                ExpressionKind::Variable(member_name) => {
                    // check is interface member
                    if let Some(member) = context.interfaces.get(&obj_ty).and_then(|interface| {
                        interface
                            .members
                            .get(&MemberKind::Member(member_name.clone()))
                    }) {
                        return (*member, res);
                    }

                    // check is map
                    if obj_ty != TypeKind::Map {
                        res.push(TypeCheckResult {
                            node: &**member_expr,
                            reason: "no map type don't have member".into(),
                        })
                    }
                    return (TypeKind::Any, res);
                }
                ExpressionKind::FunctionCallExpression(fn_name, fn_params_expr) => {
                    // check is interface function
                    if let Some(function_candidates) =
                        context.interfaces.get(&obj_ty).and_then(|interface| {
                            interface
                                .functions
                                .get(&FunctionKind::Function(fn_name.clone()))
                        })
                    {
                        let (params_ty, params_res) = fn_params_expr
                            .iter()
                            .map(|param_expr| check_expression(param_expr, context, flow))
                            .fold::<(Vec<TypeKind>, Vec<TypeCheckResult>), _>(
                                (vec![], vec![]),
                                |(mut acc_ty_list, acc_res_list), (param_ty, param_res)| {
                                    acc_ty_list.push(param_ty);
                                    (
                                        acc_ty_list,
                                        acc_res_list.into_iter().chain(param_res).collect(),
                                    )
                                },
                            );
                        let (return_ty, return_res) =
                            check_function_args(expr, function_candidates, params_ty);
                        return (
                            return_ty,
                            res.into_iter()
                                .chain(params_res)
                                .chain(return_res)
                                .collect(),
                        );
                    } else {
                        res.push(TypeCheckResult {
                            node: &**member_expr,
                            reason: format!("{} not found", fn_name).into(),
                        });
                        return (TypeKind::Any, res);
                    }
                }
                _ => {
                    res.push(TypeCheckResult {
                        node: &**member_expr,
                        reason: "map member must identifier".into(),
                    });
                    return (TypeKind::Any, res);
                }
            };
        }
        ExpressionKind::SubscriptExpression(obj_expr, subscript_expr) => {
            let (obj_ty, obj_res) = check_expression(&obj_expr, context, flow);
            let (subscript_ty, subscript_res) = check_expression(&subscript_expr, context, flow);
            let (return_ty, return_res) = check_interface_function_calling(
                expr,
                context,
                obj_ty,
                FunctionKind::Subscript,
                vec![subscript_ty],
            );
            (
                return_ty,
                obj_res
                    .into_iter()
                    .chain(subscript_res)
                    .chain(return_res)
                    .collect(),
            )
        }
        ExpressionKind::FunctionCallExpression(_, params_expr) => {
            let (params_ty, params_res) = params_expr
                .iter()
                .map(|param_expr| (param_expr, check_expression(param_expr, context, flow)))
                .fold::<(Vec<TypeKind>, Vec<TypeCheckResult>), _>(
                    (vec![], vec![]),
                    |(mut acc_ty_list, acc_res_list), (param_expr, (param_ty, param_res))| {
                        acc_ty_list.push(param_ty);
                        (
                            acc_ty_list,
                            acc_res_list.into_iter().chain(param_res).collect(),
                        )
                    },
                );

            match context
                .bindings
                .function_table
                .get(&expr.id)
                .and_then(|node| Some(node.1))
            {
                Some(FunctionNodeRef::Function(node)) => {
                    let (return_ty, return_res) =
                        check_function(expr, node, &params_ty, context, &flow);
                    (
                        return_ty,
                        params_res.into_iter().chain(return_res).collect(),
                    )
                }
                Some(FunctionNodeRef::GlobalFunction(function_ty_candidates)) => {
                    let (return_ty, return_res) =
                        check_function_args(expr, function_ty_candidates, params_ty);
                    (
                        return_ty,
                        params_res.into_iter().chain(return_res).collect(),
                    )
                }
                None => panic!(),
            }
        }
    }
}

fn check_rule<'a, 'b>(
    rule: &'a Rule,
    context: &'a TypeCheckContext<'a>,
    flow: &'b Flow,
) -> Vec<TypeCheckResult<'a>> {
    let (ty, mut result) = check_expression(&rule.condition, context, flow);
    if let Some(res) = assert_type(&ty, &TypeKind::Boolean, &rule.condition) {
        result.push(res)
    }
    result
}

fn check_rule_group<'a, 'b>(
    rule_group: &'a RuleGroup,
    context: &'a TypeCheckContext<'a>,
    flow: &'b Flow,
) -> Vec<TypeCheckResult<'a>> {
    rule_group
        .rules
        .iter()
        .map(|rule| check_rule(rule, context, flow))
        .flatten()
        .chain(
            rule_group
                .rule_groups
                .iter()
                .map(|rule_group| check_rule_group(rule_group, context, flow))
                .flatten(),
        )
        .collect()
}

pub fn check<'a>(ast: &'a Ast, context: &'a TypeCheckContext<'a>) -> Vec<TypeCheckResult<'a>> {
    let flow = Flow {
        context: HashMap::new(),
    };

    ast.tree
        .services
        .iter()
        .map(|service| {
            service
                .rule_groups
                .iter()
                .map(|rule_group| check_rule_group(rule_group, context, &flow))
                .flatten()
        })
        .flatten()
        .collect()
}
