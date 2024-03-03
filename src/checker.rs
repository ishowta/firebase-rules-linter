use std::{collections::HashMap, hash::Hash, iter::zip};

use log::{debug, info};
use miette::{Diagnostic, Report, SourceSpan};
use thiserror::Error;

use crate::{
    ast::{
        Ast, BinaryLiteral, Expression, ExpressionKind, Function, Literal, Node, NodeID,
        PathLiteral, Rule, RuleGroup,
    },
    orany::OrAny,
    symbol::{Bindings, FunctionNodeRef, SymbolReferences, VariableNodeRef},
    ty::{
        Flow, FunctionInterface, FunctionKind, ListLiteral, MapLiteral, MayLiteral, MemberKind, Ty,
        TypeID, TypeKind,
    },
    Config,
};

#[derive(Clone, Debug, Error, Diagnostic, PartialEq, Eq, Hash)]
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
    pub source_code: &'a String,
    pub config: &'a Config,
}

pub type VariableTypeBindings<'a> = HashMap<&'a NodeID, Ty>;

fn check_can_be<'a, 'b>(
    from: &'b Ty,
    to: &'b Ty,
    expr: &'a Expression,
    flow: &'a Flow,
) -> (OrAny, Vec<TypeCheckResult>) {
    let passed: OrAny = from.can_be(to, flow);
    match passed {
        OrAny::Any => (OrAny::Any, vec![]),
        OrAny::Bool(can) => {
            if can {
                (OrAny::Bool(true), vec![])
            } else {
                (
                    OrAny::Bool(false),
                    vec![TypeCheckResult::new(
                        expr,
                        format!(
                            "Expect {:?}, Get {:?}",
                            to.expand_for_debug(flow),
                            from.expand_for_debug(flow)
                        )
                        .into(),
                    )],
                )
            }
        }
    }
}

fn check_can_be_candidates<'a, 'b>(
    from: &'b Ty,
    to_candidates: Vec<Ty>,
    expr: &'a Expression,
    flow: &'a Flow,
) -> (OrAny, Vec<TypeCheckResult>) {
    let passed: OrAny = OrAny::all(to_candidates.iter(), |to: &Ty| from.can_be(to, flow));
    match passed {
        OrAny::Any => (OrAny::Any, vec![]),
        OrAny::Bool(can) => {
            if can {
                (OrAny::Bool(true), vec![])
            } else {
                (
                    OrAny::Bool(false),
                    vec![TypeCheckResult::new(
                        expr,
                        format!(
                            "Expect {:?}, Get {:?}",
                            to_candidates
                                .iter()
                                .map(|ty| ty.expand_for_debug(flow))
                                .collect::<Vec<TypeKind>>(),
                            from.expand_for_debug(flow)
                        )
                        .into(),
                    )],
                )
            }
        }
    }
}

fn check_function_args<'a>(
    expr: &'a dyn Node,
    name: String,
    base_ty: Option<&Ty>,
    functions: &Vec<&FunctionInterface>,
    args: Vec<Ty>,
    flow: &mut Flow,
    function_kind: Option<FunctionKind>,
) -> (Ty, Vec<TypeCheckResult>) {
    if let Some((return_ty, return_result)) =
        functions
            .iter()
            .find_map(|FunctionInterface((params, _), generate_return_type)| {
                match OrAny::all(zip(&args, params), |(arg, param)| {
                    arg.kind(flow).can_be(param, flow)
                }) {
                    OrAny::Any | OrAny::Bool(true) => Some(generate_return_type(
                        expr,
                        &args.iter().map(|x| x.kind(flow)).collect(),
                        flow,
                    )),
                    OrAny::Bool(false) => None,
                }
            })
    {
        (return_ty.clone(), return_result)
    } else {
        (
            Ty::new(TypeKind::Any),
            vec![TypeCheckResult::new(
                expr,
                format!(
                    "function or operator {}({}) type mismatch. expect {}, get {:?}",
                    name,
                    base_ty
                        .map(|t| format!("{:?}", t.expand_for_debug(flow)))
                        .unwrap_or("Global".to_owned()),
                    functions
                        .iter()
                        .map(|x| format!("{:?}", x.0))
                        .collect::<Vec<String>>()
                        .join(" or "),
                    args.iter()
                        .map(|ty| ty.expand_for_debug(flow))
                        .collect::<Vec<TypeKind>>()
                ),
            )],
        )
    }
}

fn check_interface_function_calling<'a>(
    node: &'a dyn Node,
    _context: &'a TypeCheckContext,
    interface_ty: Ty,
    function_kind: FunctionKind,
    args: Vec<Ty>,
    flow: &mut Flow,
) -> (Ty, Vec<TypeCheckResult>) {
    if interface_ty.kind(flow).is_any() {
        if function_kind == FunctionKind::BinaryOp(BinaryLiteral::Eq) {
            return (Ty::new(TypeKind::Boolean(MayLiteral::Unknown)), vec![]);
        }
        if function_kind == FunctionKind::BinaryOp(BinaryLiteral::NotEq) {
            return (Ty::new(TypeKind::Boolean(MayLiteral::Unknown)), vec![]);
        }
        return (Ty::new(TypeKind::Any), vec![]);
    }
    if function_kind == FunctionKind::BinaryOp(BinaryLiteral::Eq)
        || function_kind == FunctionKind::BinaryOp(BinaryLiteral::NotEq)
    {
        if interface_ty.kind(flow).is_null() {
            if args[0].kind(flow).is_null() {
                return (
                    Ty::new(TypeKind::Boolean(MayLiteral::Literal(true))),
                    vec![],
                );
            } else {
                return (
                    Ty::new(TypeKind::Boolean(MayLiteral::Literal(false))),
                    vec![],
                );
            }
        }
    }
    let interface_ty = interface_ty.kind(flow).clone();
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
            Ty::new(TypeKind::Any),
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
            Some(&Ty::new(interface_ty.clone())),
            &functions,
            args,
            flow,
            Some(function_kind),
        )
    }
}

fn check_function<'a, 'b, 'c>(
    caller: &'a dyn Node,
    function: &'a Function,
    params: &'b Vec<Ty>,
    context: &'a TypeCheckContext<'a>,
    variable_type_bindings: &'c VariableTypeBindings,
    flow: &'c mut Flow,
    request_resource_data_ty_id: &TypeID,
) -> (Ty, Vec<TypeCheckResult>) {
    let mut res: Vec<TypeCheckResult> = vec![];
    let mut variable_type_bindings = variable_type_bindings.clone();

    // args
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
    for (arg, param) in zip(&function.arguments, params) {
        variable_type_bindings.insert(&arg.id, param.clone());
    }

    // let bindings
    for let_binding in &function.let_bindings {
        let (let_ty, let_result) = check_expression(
            &let_binding.expression,
            context,
            &variable_type_bindings,
            flow,
            request_resource_data_ty_id,
        );
        variable_type_bindings.insert(&let_binding.id, let_ty.clone());
        res.extend(let_result);
    }

    // return expression
    let (return_ty, return_res) = check_expression(
        &function.return_expression,
        context,
        &variable_type_bindings,
        flow,
        request_resource_data_ty_id,
    );
    res.extend(return_res);

    (return_ty, res)
}

fn check_expression<'a, 'b>(
    expr: &'a Expression,
    context: &'a TypeCheckContext<'a>,
    variable_type_bindings: &'b VariableTypeBindings,
    flow: &'b mut Flow,
    request_resource_data_ty_id: &TypeID,
) -> (Ty, Vec<TypeCheckResult>) {
    let (ty, err) = check_expression_inner(
        expr,
        context,
        variable_type_bindings,
        flow,
        request_resource_data_ty_id,
    );
    debug!(
        "{:?} {:?}",
        ty.expand_for_debug(flow),
        (Report::from(TypeCheckResult {
            reason: "Expression".to_owned(),
            at: expr.get_span().into()
        })
        .with_source_code(context.source_code.clone()))
    );
    (ty, err)
}

fn check_expression_inner<'a, 'b>(
    expr: &'a Expression,
    context: &'a TypeCheckContext<'a>,
    variable_type_bindings: &'b VariableTypeBindings,
    flow: &'b mut Flow,
    request_resource_data_ty_id: &TypeID,
) -> (Ty, Vec<TypeCheckResult>) {
    match &expr.kind {
        ExpressionKind::Literal(Literal::Bool(b)) => {
            (Ty::new(TypeKind::Boolean(MayLiteral::Literal(*b))), vec![])
        }
        ExpressionKind::Literal(Literal::Float(f)) => {
            (Ty::new(TypeKind::Float(MayLiteral::Literal(*f))), vec![])
        }
        ExpressionKind::Literal(Literal::Int(i)) => {
            (Ty::new(TypeKind::Integer(MayLiteral::Literal(*i))), vec![])
        }
        ExpressionKind::Literal(Literal::String(s)) => (
            Ty::new(TypeKind::String(MayLiteral::Literal(s.clone()))),
            vec![],
        ),
        ExpressionKind::Literal(Literal::List(items)) => {
            let mut result = vec![];
            (
                Ty::new(TypeKind::List(MayLiteral::Literal(ListLiteral::Tuple(
                    items
                        .iter()
                        .map(|item| {
                            let (item_ty, item_res) = check_expression(
                                item,
                                context,
                                variable_type_bindings,
                                flow,
                                request_resource_data_ty_id,
                            );
                            result.extend(item_res);
                            item_ty
                        })
                        .collect(),
                )))),
                result,
            )
        }
        ExpressionKind::Literal(Literal::Map(entries)) => {
            let (entries_type, entries_result) = entries
                .iter()
                .map(|(key, value)| {
                    (
                        key,
                        check_expression(
                            value,
                            context,
                            variable_type_bindings,
                            flow,
                            request_resource_data_ty_id,
                        ),
                    )
                })
                .fold(
                    (HashMap::new(), Vec::<TypeCheckResult>::new()),
                    |(mut entries_type, entries_result), (key, (value_ty, value_result))| {
                        entries_type.insert(key.clone(), value_ty);
                        (entries_type, [entries_result, value_result].concat())
                    },
                );
            (
                Ty::new(TypeKind::Map(MayLiteral::Literal(MapLiteral {
                    literals: entries_type,
                    default: None,
                }))),
                entries_result,
            )
        }
        ExpressionKind::Literal(Literal::Path(args)) => {
            let mut result: Vec<TypeCheckResult> = vec![];
            let ty = args.iter().fold(
                Result::Ok(MayLiteral::Literal("".to_owned())),
                |mut acc: Result<MayLiteral<String>, Vec<String>>, arg| match arg {
                    PathLiteral::PathExpressionSubstitution(arg_expr) => {
                        let (arg_type, arg_result) = check_expression(
                            &arg_expr,
                            context,
                            variable_type_bindings,
                            flow,
                            request_resource_data_ty_id,
                        );
                        let (_, check_result) = check_can_be(
                            &arg_type,
                            &Ty::new(TypeKind::String(MayLiteral::Unknown)),
                            &arg_expr,
                            flow,
                        );
                        result.extend(arg_result);
                        result.extend(check_result);

                        if let TypeKind::String(MayLiteral::Literal(arg_str)) = arg_type.kind(flow)
                        {
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
                    Ok(may_literal) => Ty::new(TypeKind::Path(may_literal)),
                    Err(templates) => Ty::new(TypeKind::PathTemplateUnBound(MayLiteral::Literal(
                        templates,
                    ))),
                },
                result,
            )
        }
        ExpressionKind::Literal(Literal::Null) => (Ty::new(TypeKind::Null), vec![]),
        ExpressionKind::Variable(_) => match context
            .bindings
            .variable_table
            .get(&expr.id)
            .and_then(|node| Some(node.1))
        {
            Some(VariableNodeRef::LetBinding(node)) => (
                (*variable_type_bindings.get(&node.id).unwrap()).clone(),
                vec![],
            ),
            Some(VariableNodeRef::FunctionArgument(arg)) => (
                (*variable_type_bindings.get(&arg.id).unwrap()).clone(),
                vec![],
            ),
            Some(VariableNodeRef::PathCapture(_)) => {
                (Ty::new(TypeKind::String(MayLiteral::Unknown)), vec![])
            }
            Some(VariableNodeRef::PathCaptureGroup(_)) => {
                (Ty::new(TypeKind::String(MayLiteral::Unknown)), vec![])
            }
            Some(VariableNodeRef::GlobalVariable(type_kind)) => (type_kind.clone(), vec![]),
            None => (Ty::new(TypeKind::Any), vec![]),
        },
        ExpressionKind::UnaryOperation(literal, op_expr) => {
            let (op_ty, op_res) = check_expression(
                &op_expr,
                context,
                variable_type_bindings,
                flow,
                request_resource_data_ty_id,
            );
            let (return_ty, return_res) = check_interface_function_calling(
                expr,
                context,
                op_ty,
                FunctionKind::UnaryOp(*literal),
                vec![],
                flow,
            );
            (return_ty, [op_res, return_res].concat())
        }
        ExpressionKind::BinaryOperation(literal, left_expr, right_expr) => {
            let (left_ty, left_res) = check_expression(
                &left_expr,
                context,
                variable_type_bindings,
                flow,
                request_resource_data_ty_id,
            );
            let (right_ty, right_res) = check_expression(
                &right_expr,
                context,
                variable_type_bindings,
                flow,
                request_resource_data_ty_id,
            );
            let (return_ty, return_res) = check_interface_function_calling(
                expr,
                context,
                left_ty,
                FunctionKind::BinaryOp(*literal),
                vec![right_ty],
                flow,
            );
            (return_ty, [left_res, right_res, return_res].concat())
        }
        ExpressionKind::TernaryOperation(cond_expr, true_expr, false_expr) => {
            let (cond_ty, mut cond_res) = check_expression(
                &cond_expr,
                context,
                variable_type_bindings,
                flow,
                request_resource_data_ty_id,
            );
            let (_, res_assert) = check_can_be(
                &cond_ty,
                &Ty::new(TypeKind::Boolean(MayLiteral::Unknown)),
                &cond_expr,
                flow,
            );
            cond_res.extend(res_assert);
            let (true_ty, true_res) = check_expression(
                &true_expr,
                context,
                variable_type_bindings,
                flow,
                request_resource_data_ty_id,
            );
            let (false_ty, false_res) = check_expression(
                &false_expr,
                context,
                variable_type_bindings,
                flow,
                request_resource_data_ty_id,
            );
            let result_ty = Ty::max(&true_ty, &false_ty, flow);
            (result_ty, [cond_res, true_res, false_res].concat())
        }
        ExpressionKind::TypeCheckOperation(target_expr, type_str) => {
            let type_str_ty_candidates = match &**type_str {
                "bool" => vec![Ty::new(TypeKind::Boolean(MayLiteral::Unknown))],
                "int" => vec![Ty::new(TypeKind::Integer(MayLiteral::Unknown))],
                "float" => vec![Ty::new(TypeKind::Float(MayLiteral::Unknown))],
                "number" => vec![
                    Ty::new(TypeKind::Integer(MayLiteral::Unknown)),
                    Ty::new(TypeKind::Float(MayLiteral::Unknown)),
                ],
                "string" => vec![Ty::new(TypeKind::String(MayLiteral::Unknown))],
                "list" => vec![Ty::new(TypeKind::List(MayLiteral::Unknown))],
                "map" => vec![Ty::new(TypeKind::Map(MayLiteral::Unknown))],
                "timestamp" => vec![Ty::new(TypeKind::Timestamp)],
                "duration" => vec![Ty::new(TypeKind::Duration)],
                "path" => vec![Ty::new(TypeKind::Path(MayLiteral::Unknown))],
                "latlng" => vec![Ty::new(TypeKind::LatLng)],
                _ => vec![Ty::new(TypeKind::Any)],
            };
            let (target_ty, res_1) = check_expression(
                &target_expr,
                context,
                variable_type_bindings,
                flow,
                request_resource_data_ty_id,
            );
            let (bool_ty, res_2) =
                check_can_be_candidates(&target_ty, type_str_ty_candidates, expr, flow);

            (
                Ty::new(TypeKind::make_bool_ty(bool_ty)),
                [res_1, res_2].concat(),
            )
        }
        ExpressionKind::MemberExpression(obj_expr, member_expr) => {
            // check is namespace
            if let Some(_) = context.bindings.function_table.get(&member_expr.id) {
                return check_expression(
                    &member_expr,
                    context,
                    variable_type_bindings,
                    flow,
                    request_resource_data_ty_id,
                );
            }

            let (obj_ty, mut res) = check_expression(
                &obj_expr,
                context,
                variable_type_bindings,
                flow,
                request_resource_data_ty_id,
            );
            if obj_ty.kind(flow).is_any() {
                return (Ty::new(TypeKind::Any), res);
            }
            match &member_expr.kind {
                ExpressionKind::Variable(variable_name) => {
                    let coercions = obj_ty.kind(flow).get_coercion_list();
                    // check is interface function
                    let member = {
                        let interfaces = obj_ty.kind(flow).get_interface(&coercions);
                        interfaces.iter().find_map(|interface| {
                            interface
                                .members
                                .iter()
                                .find_map(|(member_kind, member_ty)| match member_kind {
                                    MemberKind::AnyMember => Some(member_ty.clone()),
                                    MemberKind::Member(member_name) => {
                                        if member_name == variable_name {
                                            Some(member_ty.clone())
                                        } else {
                                            None
                                        }
                                    }
                                })
                        })
                    };

                    if let Some(member) = member {
                        if let TypeKind::Boolean(MayLiteral::Literal(bool_literal)) =
                            member.kind(flow)
                        {
                            return (
                                Ty::new(TypeKind::Boolean(MayLiteral::Literal(*bool_literal))),
                                res,
                            );
                        } else {
                            return (member.clone(), res);
                        }
                    }

                    res.push(TypeCheckResult::new(
                        &**member_expr,
                        format!(
                            "member not found.

type: {:?}

got: `.{}`",
                            obj_ty.expand_for_debug(flow),
                            // TODO
                            // interfaces
                            //     .iter()
                            //     .map(|interface| &interface.members)
                            //     .collect::<Vec<&HashMap<MemberKind, Ty>>>(),
                            variable_name,
                        ),
                    ));
                    return (Ty::new(TypeKind::Any), res);
                }
                ExpressionKind::FunctionCallExpression(fn_name, fn_params_expr) => {
                    let obj_ty = obj_ty.kind(flow).clone();
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
                            Ty::new(TypeKind::Any),
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
                        .map(|param_expr| {
                            check_expression(
                                param_expr,
                                context,
                                variable_type_bindings,
                                flow,
                                request_resource_data_ty_id,
                            )
                        })
                        .fold::<(Vec<Ty>, Vec<TypeCheckResult>), _>(
                            (vec![], vec![]),
                            |(mut acc_ty_list, acc_res_list), (param_ty, param_res)| {
                                acc_ty_list.push(param_ty);
                                (acc_ty_list, [acc_res_list, param_res].concat())
                            },
                        );
                    let (return_ty, return_res) = check_function_args(
                        expr,
                        format!("`{}()`", fn_name),
                        Some(&Ty::new(obj_ty.clone())),
                        &function_candidates,
                        params_ty,
                        flow,
                        None,
                    );
                    return (return_ty, [res, params_res, return_res].concat());
                }
                _ => {
                    res.push(TypeCheckResult::new(
                        &**member_expr,
                        "map member must identifier".into(),
                    ));
                    return (Ty::new(TypeKind::Any), res);
                }
            };
        }
        ExpressionKind::SubscriptExpression(obj_expr, subscript_expr) => {
            let (obj_ty, obj_res) = check_expression(
                &obj_expr,
                context,
                variable_type_bindings,
                flow,
                request_resource_data_ty_id,
            );
            let (subscript_ty, subscript_res) = check_expression(
                &subscript_expr,
                context,
                variable_type_bindings,
                flow,
                request_resource_data_ty_id,
            );
            let (return_ty, return_res) = check_interface_function_calling(
                expr,
                context,
                obj_ty,
                FunctionKind::Subscript,
                vec![subscript_ty],
                flow,
            );
            (return_ty, [obj_res, subscript_res, return_res].concat())
        }
        ExpressionKind::FunctionCallExpression(fn_name, params_expr) => {
            let (params_ty, params_res) = params_expr
                .iter()
                .map(|param_expr| {
                    (
                        param_expr,
                        check_expression(
                            param_expr,
                            context,
                            variable_type_bindings,
                            flow,
                            request_resource_data_ty_id,
                        ),
                    )
                })
                .fold::<(Vec<Ty>, Vec<TypeCheckResult>), _>(
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
                .and_then(|node| Some(&node.1))
            {
                Some(FunctionNodeRef::Function(node)) => {
                    let (return_ty, return_res) = check_function(
                        expr,
                        node,
                        &params_ty,
                        context,
                        variable_type_bindings,
                        flow,
                        request_resource_data_ty_id,
                    );
                    (return_ty, [params_res, return_res].concat())
                }
                Some(FunctionNodeRef::GlobalFunction(_, _, function_ty_candidates)) => {
                    let (return_ty, return_res) = check_function_args(
                        expr,
                        format!("`{}()`", fn_name),
                        None,
                        &function_ty_candidates.iter().collect(),
                        params_ty,
                        flow,
                        None,
                    );
                    (return_ty, [params_res, return_res].concat())
                }
                None => (Ty::new(TypeKind::Any), vec![]),
            }
        }
    }
}

fn check_rule<'a, 'b>(
    rule: &'a Rule,
    context: &'a TypeCheckContext<'a>,
    flow: &Flow,
    request_resource_data_ty_id: &TypeID,
) -> Vec<TypeCheckResult> {
    let variable_type_bindings = HashMap::new();

    let mut result = vec![];

    info!(
        "begin check rule {:?}",
        Report::from(TypeCheckResult {
            reason: "rule".to_owned(),
            at: rule.get_span().into()
        })
        .with_source_code(context.source_code.clone())
    );

    let mut flow = flow.clone();
    let (ty, iter_result) = check_expression(
        &rule.condition,
        context,
        &variable_type_bindings,
        &mut flow,
        request_resource_data_ty_id,
    );
    result.extend(iter_result);

    // check condition is boolean
    let (_, res) = check_can_be(
        &ty,
        &Ty::new(TypeKind::Boolean(MayLiteral::Unknown)),
        &rule.condition,
        &flow,
    );
    result.extend(res);

    // check condition is always ture/false
    if let Expression {
        id: _,
        span: _,
        kind: ExpressionKind::Literal(Literal::Bool(_)),
    } = rule.condition
    {
    } else {
        if let OrAny::Bool(true) = ty.can_be(
            &Ty::new(TypeKind::Boolean(MayLiteral::Literal(true))),
            &flow,
        ) {
            result.push(TypeCheckResult {
                reason: format!("always true"),
                at: rule.condition.get_span().into(),
            })
        }
        if let OrAny::Bool(true) = ty.can_be(
            &Ty::new(TypeKind::Boolean(MayLiteral::Literal(false))),
            &flow,
        ) {
            result.push(TypeCheckResult {
                reason: format!("always false"),
                at: rule.condition.get_span().into(),
            })
        }
    }

    result
}

fn check_rule_group<'a, 'b>(
    rule_group: &'a RuleGroup,
    context: &'a TypeCheckContext<'a>,
    flow: &Flow,
    request_resource_data_ty_id: &TypeID,
) -> Vec<TypeCheckResult> {
    rule_group
        .rules
        .iter()
        .map(|rule| check_rule(rule, context, flow, request_resource_data_ty_id))
        .flatten()
        .chain(
            rule_group
                .rule_groups
                .iter()
                .map(|rule_group| {
                    check_rule_group(rule_group, context, flow, request_resource_data_ty_id)
                })
                .flatten(),
        )
        .collect()
}

pub fn check<'a>(
    ast: &'a Ast,
    context: &'a TypeCheckContext<'a>,
    flow: &Flow,
    request_resource_data_ty_id: &TypeID,
) -> Vec<TypeCheckResult> {
    ast.tree
        .services
        .iter()
        .map(|service| {
            service
                .rule_groups
                .iter()
                .map(|rule_group| {
                    check_rule_group(rule_group, context, flow, request_resource_data_ty_id)
                })
                .flatten()
        })
        .flatten()
        .collect()
}
