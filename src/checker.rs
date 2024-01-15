use std::{collections::HashMap, iter::zip};

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::{
    ast::{
        Ast, BinaryLiteral, Expression, ExpressionKind, Function, Literal, Node, NodeID,
        PathLiteral, Rule, RuleGroup,
    },
    symbol::{Bindings, FunctionNodeRef, SymbolReferences, VariableNodeRef},
    ty::{FunctionInterface, FunctionKind, MapLiteral, MayLiteral, MemberKind, TypeKind},
};

#[derive(Clone, Debug, Error, Diagnostic, PartialEq, Eq)]
#[error("{reason}")]
#[diagnostic()]
pub struct TypeCheckResult {
    pub reason: String,
    #[label]
    pub at: SourceSpan,
}

impl TypeCheckResult {
    pub fn new(node: &dyn Node, reason: String) -> Self {
        TypeCheckResult {
            reason: reason,
            at: node.get_span().into(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct TypeCheckContext<'a> {
    pub bindings: &'a Bindings<'a>,
    pub symbol_references: &'a SymbolReferences<'a>,
}

#[derive(Clone, Debug)]
pub struct Flow<'a> {
    pub context: HashMap<&'a NodeID, TypeKind>,
}

fn check_can_be<'a, 'b>(
    from: &'b TypeKind,
    to: &'b TypeKind,
    expr: &'a Expression,
) -> (Option<bool>, Vec<TypeCheckResult>) {
    let passed: Option<bool> = from.can_be(to);
    match passed {
        None => (None, vec![]),
        Some(can) => {
            if can {
                (Some(true), vec![])
            } else {
                (
                    Some(false),
                    vec![TypeCheckResult::new(
                        expr,
                        format!("Expect {:?}, Get {:?}", to, from).into(),
                    )],
                )
            }
        }
    }
}

fn check_can_be_candidates<'a, 'b>(
    from: &'b TypeKind,
    to_candidates: Vec<TypeKind>,
    expr: &'a Expression,
) -> (Option<bool>, Vec<TypeCheckResult>) {
    let passed: Option<bool> = to_candidates
        .iter()
        .map(|to: &TypeKind| from.can_be(to))
        .collect::<Option<Vec<bool>>>()
        .map(|res| res.iter().all(|b| *b));
    match passed {
        None => (None, vec![]),
        Some(can) => {
            if can {
                (Some(true), vec![])
            } else {
                (
                    Some(false),
                    vec![TypeCheckResult::new(
                        expr,
                        format!("Expect {:?}, Get {:?}", to_candidates, from).into(),
                    )],
                )
            }
        }
    }
}

fn check_function_args<'a>(
    expr: &'a dyn Node,
    name: String,
    base_ty: Option<&TypeKind>,
    functions: &Vec<&FunctionInterface>,
    args: Vec<TypeKind>,
) -> (TypeKind, Vec<TypeCheckResult>) {
    if let Some((return_ty, return_result)) = functions.iter().find_map(
        |FunctionInterface((params, _), generate_return_type)| match zip(&args, params)
            .map(|(arg, param)| arg.can_be(param))
            .collect::<Option<Vec<bool>>>()
            .map(|res| res.iter().all(|b| *b))
        {
            Some(true) => Some(generate_return_type(expr, &args)),
            Some(false) => None,
            None => Some((TypeKind::Any, vec![])),
        },
    ) {
        (return_ty.clone(), return_result)
    } else {
        (
            TypeKind::Any,
            vec![TypeCheckResult::new(
                expr,
                format!(
                    "function or operator {}({}) type mismatch. expect {}, get {:?}",
                    name,
                    base_ty
                        .map(|t| format!("{:?}", t))
                        .unwrap_or("Global".to_owned()),
                    functions
                        .iter()
                        .map(|x| format!("{:?}", x.0))
                        .collect::<Vec<String>>()
                        .join(" or "),
                    args
                ),
            )],
        )
    }
}

fn check_interface_function_calling<'a>(
    node: &'a dyn Node,
    _context: &'a TypeCheckContext,
    interface_ty: TypeKind,
    function_kind: FunctionKind,
    args: Vec<TypeKind>,
) -> (TypeKind, Vec<TypeCheckResult>) {
    if interface_ty.is_any() {
        return (TypeKind::Any, vec![]);
    }
    if function_kind == FunctionKind::BinaryOp(BinaryLiteral::Eq)
        || function_kind == FunctionKind::BinaryOp(BinaryLiteral::NotEq)
    {
        if interface_ty.is_null() {
            if args[0].is_null() {
                return (TypeKind::Boolean(MayLiteral::Literal(true)), vec![]);
            } else {
                return (TypeKind::Boolean(MayLiteral::Literal(false)), vec![]);
            }
        }
    }
    let coercions = interface_ty.get_coercion_list();
    // check is interface function
    let interfaces = interface_ty.get_interface(&coercions);
    let functions: Vec<&FunctionInterface> = interfaces
        .iter()
        .flat_map(|interface| interface.functions.get(&function_kind))
        .flatten()
        .collect();
    if functions.len() == 0 {
        (
            TypeKind::Any,
            vec![TypeCheckResult::new(
                node,
                format!(
                    "function {} not found for the type `{:?}`",
                    function_kind, interface_ty
                ),
            )],
        )
    } else {
        check_function_args(
            node,
            function_kind.to_string(),
            Some(&interface_ty),
            &functions,
            args,
        )
    }
}

fn check_function<'a, 'b, 'c>(
    caller: &'a dyn Node,
    function: &'a Function,
    params: &'b Vec<TypeKind>,
    context: &'a TypeCheckContext<'a>,
    flow: &'c Flow,
) -> (TypeKind, Vec<TypeCheckResult>) {
    let mut res: Vec<TypeCheckResult> = vec![];
    if function.arguments.len() != params.len() {
        res.push(TypeCheckResult::new(
            caller,
            format!(
                "params length not matched. expect {} but get {}",
                function.arguments.len(),
                params.len()
            )
            .into(),
        ))
    }
    let mut flow = flow.clone();
    for (arg, param) in zip(&function.arguments, params) {
        flow.context.insert(&arg.id, param.clone());
    }
    let (return_ty, return_res) = check_expression(&function.return_expression, context, &flow);
    (return_ty, [res, return_res].concat())
}

fn check_expression<'a, 'b>(
    expr: &'a Expression,
    context: &'a TypeCheckContext<'a>,
    flow: &'b Flow,
) -> (TypeKind, Vec<TypeCheckResult>) {
    match &expr.kind {
        ExpressionKind::Literal(Literal::Bool(b)) => {
            (TypeKind::Boolean(MayLiteral::Literal(*b)), vec![])
        }
        ExpressionKind::Literal(Literal::Float(f)) => {
            (TypeKind::Float(MayLiteral::Literal(*f)), vec![])
        }
        ExpressionKind::Literal(Literal::Int(i)) => {
            (TypeKind::Integer(MayLiteral::Literal(*i)), vec![])
        }
        ExpressionKind::Literal(Literal::String(s)) => {
            (TypeKind::String(MayLiteral::Literal(s.clone())), vec![])
        }
        ExpressionKind::Literal(Literal::List(items)) => {
            let (item_ty, result) = items
                .iter()
                .map(|item| check_expression(item, context, flow))
                .reduce(|(acc_ty, acc_result), (item_ty, item_result)| {
                    (
                        TypeKind::max(&acc_ty, &item_ty),
                        [acc_result, item_result].concat(),
                    )
                })
                .unwrap_or((TypeKind::Any, vec![]));
            (TypeKind::List(Box::new(item_ty)), result)
        }
        ExpressionKind::Literal(Literal::Map(entries)) => {
            let (entries_type, entries_result) = entries
                .iter()
                .map(|(key, value)| (key, check_expression(value, context, flow)))
                .fold(
                    (HashMap::new(), Vec::<TypeCheckResult>::new()),
                    |(mut entries_type, entries_result), (key, (value_ty, value_result))| {
                        entries_type.insert(key.clone(), value_ty);
                        (entries_type, [entries_result, value_result].concat())
                    },
                );
            (
                TypeKind::Map(MayLiteral::Literal(MapLiteral {
                    literals: entries_type,
                    default: None,
                })),
                entries_result,
            )
        }
        ExpressionKind::Literal(Literal::Path(args)) => {
            let mut result: Vec<TypeCheckResult> = vec![];
            let ty = args.iter().fold(
                Result::Ok(MayLiteral::Literal("".to_owned())),
                |mut acc: Result<MayLiteral<String>, Vec<String>>, arg| match arg {
                    PathLiteral::PathExpressionSubstitution(arg_expr) => {
                        let (arg_type, arg_result) = check_expression(&arg_expr, context, flow);
                        let (_, check_result) = check_can_be(
                            &arg_type,
                            &TypeKind::String(MayLiteral::Unknown),
                            &arg_expr,
                        );
                        result.extend(arg_result);
                        result.extend(check_result);

                        if let TypeKind::String(MayLiteral::Literal(arg_str)) = arg_type {
                            match acc {
                                Ok(MayLiteral::Unknown) => Ok(MayLiteral::Unknown),
                                Ok(MayLiteral::Literal(str)) => {
                                    Ok(MayLiteral::Literal(str + &arg_str))
                                }
                                Err(templates) => Err(templates),
                            }
                        } else {
                            match acc {
                                Ok(_) => Ok(MayLiteral::Unknown),
                                Err(templates) => Err(templates),
                            }
                        }
                    }
                    PathLiteral::Path(arg_str) => match acc {
                        Ok(MayLiteral::Unknown) => Ok(MayLiteral::Unknown),
                        Ok(MayLiteral::Literal(str)) => Ok(MayLiteral::Literal(str + arg_str)),
                        Err(templates) => Err(templates),
                    },
                    PathLiteral::PathBinding(arg_str) => match &mut acc {
                        Ok(_) => Err(vec![arg_str.clone()]),
                        Err(templates) => {
                            templates.push(arg_str.clone());
                            acc
                        }
                    },
                },
            );
            (
                match ty {
                    Ok(may_literal) => TypeKind::Path(may_literal),
                    Err(templates) => TypeKind::PathTemplateUnBound(MayLiteral::Literal(templates)),
                },
                result,
            )
        }
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
                (flow.context.get(&arg.id).unwrap().clone(), vec![])
            }
            Some(VariableNodeRef::PathCapture(_)) => {
                (TypeKind::String(MayLiteral::Unknown), vec![])
            }
            Some(VariableNodeRef::PathCaptureGroup(_)) => {
                (TypeKind::String(MayLiteral::Unknown), vec![])
            }
            Some(VariableNodeRef::GlobalVariable(type_kind)) => (type_kind.clone(), vec![]),
            None => (TypeKind::Any, vec![]),
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
            (return_ty, [op_res, return_res].concat())
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
            (return_ty, [left_res, right_res, return_res].concat())
        }
        ExpressionKind::TernaryOperation(cond_expr, true_expr, false_expr) => {
            let (cond_ty, mut cond_res) = check_expression(&cond_expr, context, flow);
            let (_, res_assert) = check_can_be(
                &cond_ty,
                &TypeKind::Boolean(MayLiteral::Unknown),
                &cond_expr,
            );
            cond_res.extend(res_assert);
            let (true_ty, true_res) = check_expression(&true_expr, context, flow);
            let (false_ty, false_res) = check_expression(&false_expr, context, flow);
            let result_ty = TypeKind::max(&true_ty, &false_ty);
            (result_ty, [cond_res, true_res, false_res].concat())
        }
        ExpressionKind::TypeCheckOperation(target_expr, type_str) => {
            let type_str_ty_candidates = match &**type_str {
                "bool" => vec![TypeKind::Boolean(MayLiteral::Unknown)],
                "int" => vec![TypeKind::Integer(MayLiteral::Unknown)],
                "float" => vec![TypeKind::Float(MayLiteral::Unknown)],
                "number" => vec![
                    TypeKind::Integer(MayLiteral::Unknown),
                    TypeKind::Float(MayLiteral::Unknown),
                ],
                "string" => vec![TypeKind::String(MayLiteral::Unknown)],
                "list" => vec![TypeKind::List(Box::new(TypeKind::Any)).clone()],
                "map" => vec![TypeKind::Map(MayLiteral::Unknown).clone()],
                "timestamp" => vec![TypeKind::Timestamp],
                "duration" => vec![TypeKind::Duration],
                "path" => vec![TypeKind::Path(MayLiteral::Unknown)],
                "latlng" => vec![TypeKind::LatLng],
                _ => vec![TypeKind::Any],
            };
            let (target_ty, res_1) = check_expression(&target_expr, context, flow);
            let (bool_ty, res_2) =
                check_can_be_candidates(&target_ty, type_str_ty_candidates, expr);
            (TypeKind::make_bool_ty(bool_ty), [res_1, res_2].concat())
        }
        ExpressionKind::MemberExpression(obj_expr, member_expr) => {
            // check is namespace
            if let Some(_) = context.bindings.function_table.get(&member_expr.id) {
                return check_expression(&member_expr, context, flow);
            }

            let (obj_ty, mut res) = check_expression(&obj_expr, context, flow);
            if obj_ty.is_any() {
                return (obj_ty, res);
            }
            match &member_expr.kind {
                ExpressionKind::Variable(variable_name) => {
                    let coercions = obj_ty.get_coercion_list();
                    // check is interface function
                    let interfaces = obj_ty.get_interface(&coercions);
                    if let Some(member) = interfaces.iter().find_map(|interface| {
                        interface
                            .members
                            .iter()
                            .find_map(|(member_kind, member_ty)| match member_kind {
                                MemberKind::AnyMember => Some(TypeKind::Any),
                                MemberKind::Member(member_name) => {
                                    if member_name == variable_name {
                                        Some(member_ty.clone())
                                    } else {
                                        None
                                    }
                                }
                            })
                    }) {
                        return (member.clone(), res);
                    }

                    res.push(TypeCheckResult::new(
                        &**member_expr,
                        format!(
                            "member not found.

type: {:?}

expect: {:#?}

got: `.{}`",
                            obj_ty,
                            interfaces
                                .iter()
                                .map(|interface| &interface.members)
                                .collect::<Vec<&HashMap<MemberKind, TypeKind>>>(),
                            variable_name
                        ),
                    ));
                    return (TypeKind::Any, res);
                }
                ExpressionKind::FunctionCallExpression(fn_name, fn_params_expr) => {
                    let obj_coercions = obj_ty.get_coercion_list();
                    // check is interface function
                    let obj_interfaces = obj_ty.get_interface(&obj_coercions);
                    let function_candidates: Vec<&FunctionInterface> = obj_interfaces
                        .iter()
                        .flat_map(|interface| {
                            interface
                                .functions
                                .get(&FunctionKind::Function(fn_name.clone()))
                        })
                        .flatten()
                        .collect();
                    if function_candidates.len() == 0 {
                        return (
                            TypeKind::Any,
                            vec![TypeCheckResult::new(
                                expr,
                                format!(
                                    "function `{}()` not found for the type `{:?}`",
                                    fn_name, obj_ty
                                ),
                            )],
                        );
                    }
                    let (params_ty, params_res) = fn_params_expr
                        .iter()
                        .map(|param_expr| check_expression(param_expr, context, flow))
                        .fold::<(Vec<TypeKind>, Vec<TypeCheckResult>), _>(
                            (vec![], vec![]),
                            |(mut acc_ty_list, acc_res_list), (param_ty, param_res)| {
                                acc_ty_list.push(param_ty);
                                (acc_ty_list, [acc_res_list, param_res].concat())
                            },
                        );
                    let (return_ty, return_res) = check_function_args(
                        expr,
                        format!("`{}()`", fn_name),
                        Some(&obj_ty),
                        &function_candidates,
                        params_ty,
                    );
                    return (return_ty, [res, params_res, return_res].concat());
                }
                _ => {
                    res.push(TypeCheckResult::new(
                        &**member_expr,
                        "map member must identifier".into(),
                    ));
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
            (return_ty, [obj_res, subscript_res, return_res].concat())
        }
        ExpressionKind::FunctionCallExpression(fn_name, params_expr) => {
            let (params_ty, params_res) = params_expr
                .iter()
                .map(|param_expr| (param_expr, check_expression(param_expr, context, flow)))
                .fold::<(Vec<TypeKind>, Vec<TypeCheckResult>), _>(
                    (vec![], vec![]),
                    |(mut acc_ty_list, acc_res_list), (_param_expr, (param_ty, param_res))| {
                        acc_ty_list.push(param_ty);
                        (acc_ty_list, [acc_res_list, param_res].concat())
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
                    (return_ty, [params_res, return_res].concat())
                }
                Some(FunctionNodeRef::GlobalFunction(function_ty_candidates)) => {
                    let (return_ty, return_res) = check_function_args(
                        expr,
                        format!("`{}()`", fn_name),
                        None,
                        &function_ty_candidates.iter().collect(),
                        params_ty,
                    );
                    (return_ty, [params_res, return_res].concat())
                }
                None => (TypeKind::Any, vec![]),
            }
        }
    }
}

fn check_rule<'a, 'b>(
    rule: &'a Rule,
    context: &'a TypeCheckContext<'a>,
    flow: &'b Flow,
) -> Vec<TypeCheckResult> {
    let (ty, mut result) = check_expression(&rule.condition, context, flow);
    let (_, res) = check_can_be(
        &ty,
        &TypeKind::Boolean(MayLiteral::Unknown),
        &rule.condition,
    );
    result.extend(res);
    if let Some(true) = ty.can_be(&TypeKind::Boolean(MayLiteral::Literal(false))) {
        result.push(TypeCheckResult {
            reason: "always false".to_owned(),
            at: rule.condition.get_span().into(),
        })
    }
    result
}

fn check_rule_group<'a, 'b>(
    rule_group: &'a RuleGroup,
    context: &'a TypeCheckContext<'a>,
    flow: &'b Flow,
) -> Vec<TypeCheckResult> {
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

pub fn check<'a>(ast: &'a Ast, context: &'a TypeCheckContext<'a>) -> Vec<TypeCheckResult> {
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
