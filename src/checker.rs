use std::{cell::RefCell, collections::HashMap, hash::Hash, iter::zip};

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::{
    ast::{
        Ast, BinaryLiteral, Expression, ExpressionKind, Function, Literal, Node, NodeID,
        PathLiteral, Rule, RuleGroup, UnaryLiteral,
    },
    orany::OrAny,
    symbol::{Bindings, FunctionNodeRef, SymbolReferences, VariableNodeRef},
    ty::{
        Flow, FunctionInterface, FunctionKind, ListLiteral, MapLiteral, MayLiteral, MemberKind, Ty,
        TypeID, TypeKind,
    },
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
}

pub type VariableTypeBindings<'a> = HashMap<&'a NodeID, Ty>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Branch {
    Side(bool),
    Examination(bool),
    Through,
}

fn check_can_be<'a, 'b>(
    from: &'b Ty,
    to: &'b Ty,
    expr: &'a Expression,
    flow: &'a Flow,
    polluted: &'a RefCell<bool>,
) -> (OrAny, Vec<TypeCheckResult>) {
    let passed: OrAny = from.can_be(to, flow, polluted);
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
    polluted: &'a RefCell<bool>,
) -> (OrAny, Vec<TypeCheckResult>) {
    let passed: OrAny = OrAny::all(to_candidates.iter(), |to: &Ty| {
        from.can_be(to, flow, polluted)
    });
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
    polluted: &RefCell<bool>,
) -> (Ty, Vec<TypeCheckResult>) {
    if let Some((return_ty, return_result)) =
        functions
            .iter()
            .find_map(|FunctionInterface((params, _), generate_return_type)| {
                match OrAny::all(zip(&args, params), |(arg, param)| {
                    arg.kind(flow, polluted).can_be(param, flow, polluted)
                }) {
                    OrAny::Bool(true) => Some(generate_return_type(
                        expr,
                        &args.iter().map(|x| x.kind(flow, polluted)).collect(),
                        flow,
                        polluted,
                    )),
                    OrAny::Bool(false) => None,
                    OrAny::Any => Some((Ty::new(TypeKind::Any), vec![])),
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
    flow_branch_reverse: bool,
    polluted: &RefCell<bool>,
    on_examination: &bool,
    on_poisoning: bool,
) -> (Ty, Vec<TypeCheckResult>) {
    if !on_examination && flow_branch_reverse == false {
        if let Ty::FlowType(flow_type_id, poison) = &interface_ty {
            if *poison {
                *polluted.borrow_mut() = true;
            }
            if function_kind == FunctionKind::BinaryOp(BinaryLiteral::In) {
                if let Some(flow_interface_ty) = flow.get(&flow_type_id) {
                    if let Ty::Type(_, TypeKind::String(MayLiteral::Literal(key))) = &args[0] {
                        if let TypeKind::Map(MayLiteral::Literal(map_literal)) =
                            flow_interface_ty.kind(flow, polluted)
                        {
                            let mut map_literal = map_literal.clone();
                            let new_ty_id = TypeID::new();
                            flow.insert(
                                new_ty_id.clone(),
                                Ty::Type(new_ty_id.clone(), TypeKind::Any),
                            );
                            map_literal
                                .literals
                                .insert(key.clone(), Ty::FlowType(new_ty_id.clone(), on_poisoning));
                            *flow.get_mut(&flow_type_id).unwrap().get_type_mut().unwrap() =
                                TypeKind::Map(MayLiteral::Literal(map_literal));
                        } else if let TypeKind::Map(MayLiteral::Unknown) =
                            flow_interface_ty.kind(flow, polluted)
                        {
                            let mut map_literal = MapLiteral {
                                literals: HashMap::new(),
                                default: None,
                            };
                            let new_ty_id = TypeID::new();
                            flow.insert(
                                new_ty_id.clone(),
                                Ty::Type(new_ty_id.clone(), TypeKind::Any),
                            );
                            map_literal
                                .literals
                                .insert(key.clone(), Ty::FlowType(new_ty_id.clone(), on_poisoning));
                            *flow.get_mut(&flow_type_id).unwrap().get_type_mut().unwrap() =
                                TypeKind::Map(MayLiteral::Literal(map_literal));
                        }
                    }
                }
            }
        }
    }
    if interface_ty.kind(flow, polluted).is_any() {
        return (Ty::new(TypeKind::Any), vec![]);
    }
    if function_kind == FunctionKind::BinaryOp(BinaryLiteral::Eq)
        || function_kind == FunctionKind::BinaryOp(BinaryLiteral::NotEq)
    {
        if interface_ty.kind(flow, polluted).is_null() {
            if args[0].kind(flow, polluted).is_null() {
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
    let interface_ty = interface_ty.kind(flow, polluted).clone();
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
            polluted,
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
    flow_branch: &'c mut Vec<Branch>,
    flow_branch_depth: &'b mut usize,
    flow_branch_reverse: bool,
    polluted: &'c RefCell<bool>,
    on_examination: &'b mut bool,
    on_poisoning: bool,
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
            flow_branch,
            flow_branch_depth,
            flow_branch_reverse,
            polluted,
            on_examination,
            on_poisoning,
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
        flow_branch,
        flow_branch_depth,
        flow_branch_reverse,
        polluted,
        on_examination,
        on_poisoning,
    );
    res.extend(return_res);

    (return_ty, res)
}

fn check_expression<'a, 'b>(
    expr: &'a Expression,
    context: &'a TypeCheckContext<'a>,
    variable_type_bindings: &'b VariableTypeBindings,
    flow: &'b mut Flow,
    flow_branch: &'b mut Vec<Branch>,
    flow_branch_depth: &'b mut usize,
    flow_branch_reverse: bool,
    polluted: &RefCell<bool>,
    on_examination: &'b mut bool,
    on_poisoning: bool,
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
                                flow_branch,
                                flow_branch_depth,
                                flow_branch_reverse,
                                polluted,
                                on_examination,
                                on_poisoning,
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
                            flow_branch,
                            flow_branch_depth,
                            flow_branch_reverse,
                            polluted,
                            on_examination,
                            on_poisoning,
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
                            flow_branch,
                            flow_branch_depth,
                            flow_branch_reverse,
                            polluted,
                            on_examination,
                            on_poisoning,
                        );
                        let (_, check_result) = check_can_be(
                            &arg_type,
                            &Ty::new(TypeKind::String(MayLiteral::Unknown)),
                            &arg_expr,
                            flow,
                            polluted,
                        );
                        result.extend(arg_result);
                        result.extend(check_result);

                        if let TypeKind::String(MayLiteral::Literal(arg_str)) =
                            arg_type.kind(flow, polluted)
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
                flow_branch,
                flow_branch_depth,
                if *literal == UnaryLiteral::Not {
                    !flow_branch_reverse
                } else {
                    flow_branch_reverse
                },
                polluted,
                on_examination,
                on_poisoning,
            );
            let (return_ty, return_res) = check_interface_function_calling(
                expr,
                context,
                op_ty,
                FunctionKind::UnaryOp(*literal),
                vec![],
                flow,
                flow_branch_reverse,
                polluted,
                &on_examination,
                on_poisoning,
            );
            (return_ty, [op_res, return_res].concat())
        }
        ExpressionKind::BinaryOperation(literal, left_expr, right_expr) => {
            if !*on_examination
                && ((*literal == BinaryLiteral::LogicalOr && !flow_branch_reverse)
                    || (*literal == BinaryLiteral::LogicalAnd && flow_branch_reverse))
            {
                let _flow_branch_depth = *flow_branch_depth;
                *flow_branch_depth += 1;
                match flow_branch.get(_flow_branch_depth) {
                    Some(Branch::Through) => {
                        // TODO: need merge?
                        let (left_ty, left_res) = check_expression(
                            &left_expr,
                            context,
                            variable_type_bindings,
                            flow,
                            flow_branch,
                            flow_branch_depth,
                            flow_branch_reverse,
                            polluted,
                            on_examination,
                            on_poisoning,
                        );
                        let (left_ty, left_res) = check_expression(
                            &left_expr,
                            context,
                            variable_type_bindings,
                            flow,
                            flow_branch,
                            flow_branch_depth,
                            !flow_branch_reverse,
                            polluted,
                            on_examination,
                            on_poisoning,
                        );
                        let (right_ty, right_res) = check_expression(
                            &right_expr,
                            context,
                            variable_type_bindings,
                            flow,
                            flow_branch,
                            flow_branch_depth,
                            flow_branch_reverse,
                            polluted,
                            on_examination,
                            on_poisoning,
                        );
                        let (return_ty, return_res) = check_interface_function_calling(
                            expr,
                            context,
                            left_ty,
                            FunctionKind::BinaryOp(if *literal == BinaryLiteral::LogicalOr {
                                BinaryLiteral::LogicalAnd
                            } else {
                                *literal
                            }),
                            vec![right_ty],
                            flow,
                            flow_branch_reverse,
                            polluted,
                            &on_examination,
                            on_poisoning,
                        );
                        (return_ty, [left_res, right_res, return_res].concat())
                    }
                    Some(Branch::Side(side)) => {
                        if !side {
                            let (left_ty, left_res) = check_expression(
                                &left_expr,
                                context,
                                variable_type_bindings,
                                flow,
                                flow_branch,
                                flow_branch_depth,
                                flow_branch_reverse,
                                polluted,
                                on_examination,
                                on_poisoning,
                            );
                            check_can_be(
                                &left_ty,
                                &Ty::new(TypeKind::Boolean(MayLiteral::Unknown)),
                                &left_expr,
                                flow,
                                polluted,
                            );
                            // TODO: care always true/false
                            (Ty::new(TypeKind::Boolean(MayLiteral::Unknown)), left_res)
                        } else {
                            let (left_ty, left_res) = check_expression(
                                &left_expr,
                                context,
                                variable_type_bindings,
                                flow,
                                flow_branch,
                                flow_branch_depth,
                                !flow_branch_reverse,
                                polluted,
                                on_examination,
                                on_poisoning,
                            );
                            let (right_ty, right_res) = check_expression(
                                &right_expr,
                                context,
                                variable_type_bindings,
                                flow,
                                flow_branch,
                                flow_branch_depth,
                                flow_branch_reverse,
                                polluted,
                                on_examination,
                                on_poisoning,
                            );
                            let (return_ty, return_res) = check_interface_function_calling(
                                expr,
                                context,
                                left_ty,
                                FunctionKind::BinaryOp(if *literal == BinaryLiteral::LogicalAnd {
                                    BinaryLiteral::LogicalOr
                                } else {
                                    *literal
                                }),
                                vec![right_ty],
                                flow,
                                flow_branch_reverse,
                                polluted,
                                &on_examination,
                                on_poisoning,
                            );
                            (return_ty, [left_res, right_res, return_res].concat())
                        }
                    }
                    Some(Branch::Examination(false)) => {
                        let _polluted = RefCell::new(false);
                        let (left_ty, left_res) = check_expression(
                            &left_expr,
                            context,
                            variable_type_bindings,
                            flow,
                            flow_branch,
                            flow_branch_depth,
                            flow_branch_reverse,
                            &_polluted,
                            on_examination,
                            true,
                        );
                        *on_examination = true;
                        check_can_be(
                            &left_ty,
                            &Ty::new(TypeKind::Boolean(MayLiteral::Unknown)),
                            &left_expr,
                            flow,
                            polluted,
                        );
                        // TODO: care always true/false
                        (Ty::new(TypeKind::Boolean(MayLiteral::Unknown)), left_res)
                    }
                    Some(Branch::Examination(true)) => {
                        let _polluted = RefCell::new(false);
                        let (left_ty, left_res) = check_expression(
                            &left_expr,
                            context,
                            variable_type_bindings,
                            flow,
                            flow_branch,
                            flow_branch_depth,
                            !flow_branch_reverse,
                            &_polluted,
                            on_examination,
                            true,
                        );
                        let (right_ty, right_res) = check_expression(
                            &right_expr,
                            context,
                            variable_type_bindings,
                            flow,
                            flow_branch,
                            flow_branch_depth,
                            flow_branch_reverse,
                            &_polluted,
                            on_examination,
                            true,
                        );
                        *on_examination = true;
                        let (return_ty, return_res) = check_interface_function_calling(
                            expr,
                            context,
                            left_ty,
                            FunctionKind::BinaryOp(if *literal == BinaryLiteral::LogicalOr {
                                BinaryLiteral::LogicalAnd
                            } else {
                                *literal
                            }),
                            vec![right_ty],
                            flow,
                            flow_branch_reverse,
                            polluted,
                            &on_examination,
                            on_poisoning,
                        );
                        (return_ty, [left_res, right_res, return_res].concat())
                    }
                    None => {
                        let _polluted = RefCell::new(false);
                        flow_branch.push(Branch::Examination(false));
                        let (left_ty, left_res) = check_expression(
                            &left_expr,
                            context,
                            variable_type_bindings,
                            flow,
                            flow_branch,
                            flow_branch_depth,
                            flow_branch_reverse,
                            &_polluted,
                            on_examination,
                            true,
                        );
                        *on_examination = true;
                        check_can_be(
                            &left_ty,
                            &Ty::new(TypeKind::Boolean(MayLiteral::Unknown)),
                            &left_expr,
                            flow,
                            polluted,
                        );
                        // TODO: care always true/false
                        (Ty::new(TypeKind::Boolean(MayLiteral::Unknown)), left_res)
                    }
                }
            } else {
                let (left_ty, left_res) = check_expression(
                    &left_expr,
                    context,
                    variable_type_bindings,
                    flow,
                    flow_branch,
                    flow_branch_depth,
                    flow_branch_reverse,
                    polluted,
                    on_examination,
                    on_poisoning,
                );
                let (right_ty, right_res) = check_expression(
                    &right_expr,
                    context,
                    variable_type_bindings,
                    flow,
                    flow_branch,
                    flow_branch_depth,
                    flow_branch_reverse,
                    polluted,
                    on_examination,
                    on_poisoning,
                );
                let (return_ty, return_res) = if *literal == BinaryLiteral::In {
                    check_interface_function_calling(
                        expr,
                        context,
                        right_ty,
                        FunctionKind::BinaryOp(*literal),
                        vec![left_ty],
                        flow,
                        flow_branch_reverse,
                        polluted,
                        &on_examination,
                        on_poisoning,
                    )
                } else {
                    check_interface_function_calling(
                        expr,
                        context,
                        left_ty,
                        FunctionKind::BinaryOp(if *literal == BinaryLiteral::LogicalOr {
                            BinaryLiteral::LogicalAnd
                        } else {
                            *literal
                        }),
                        vec![right_ty],
                        flow,
                        flow_branch_reverse,
                        polluted,
                        &on_examination,
                        on_poisoning,
                    )
                };
                (return_ty, [left_res, right_res, return_res].concat())
            }
        }
        ExpressionKind::TernaryOperation(cond_expr, true_expr, false_expr) => {
            let (cond_ty, mut cond_res) = check_expression(
                &cond_expr,
                context,
                variable_type_bindings,
                flow,
                flow_branch,
                flow_branch_depth,
                flow_branch_reverse,
                polluted,
                on_examination,
                on_poisoning,
            );
            let (_, res_assert) = check_can_be(
                &cond_ty,
                &Ty::new(TypeKind::Boolean(MayLiteral::Unknown)),
                &cond_expr,
                flow,
                polluted,
            );
            cond_res.extend(res_assert);
            let (true_ty, true_res) = check_expression(
                &true_expr,
                context,
                variable_type_bindings,
                flow,
                flow_branch,
                flow_branch_depth,
                flow_branch_reverse,
                polluted,
                on_examination,
                on_poisoning,
            );
            let (false_ty, false_res) = check_expression(
                &false_expr,
                context,
                variable_type_bindings,
                flow,
                flow_branch,
                flow_branch_depth,
                flow_branch_reverse,
                polluted,
                on_examination,
                on_poisoning,
            );
            let result_ty = Ty::max(&true_ty, &false_ty, flow, polluted);
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
                flow_branch,
                flow_branch_depth,
                flow_branch_reverse,
                polluted,
                on_examination,
                on_poisoning,
            );
            let (bool_ty, res_2) = if let TypeKind::Unknown = target_ty.kind(flow, polluted) {
                (OrAny::Any, vec![])
            } else {
                check_can_be_candidates(&target_ty, type_str_ty_candidates, expr, flow, polluted)
            };

            if !*on_examination && flow_branch_reverse == false {
                if let Ty::FlowType(flow_type_id, poison) = &target_ty {
                    if *poison {
                        *polluted.borrow_mut() = true;
                    }
                    let type_str_ty = match &**type_str {
                        "bool" => TypeKind::Boolean(MayLiteral::Unknown),
                        "int" => TypeKind::Integer(MayLiteral::Unknown),
                        "float" => TypeKind::Float(MayLiteral::Unknown),
                        "number" => TypeKind::Integer(MayLiteral::Unknown),
                        "string" => TypeKind::String(MayLiteral::Unknown),
                        "list" => TypeKind::List(MayLiteral::Unknown),
                        "map" => TypeKind::Map(MayLiteral::Literal(MapLiteral {
                            literals: HashMap::new(),
                            default: None,
                        })),
                        "timestamp" => TypeKind::Timestamp,
                        "duration" => TypeKind::Duration,
                        "path" => TypeKind::Path(MayLiteral::Unknown),
                        "latlng" => TypeKind::LatLng,
                        _ => TypeKind::Any,
                    };
                    match type_str_ty.can_be(target_ty.kind(flow, polluted), flow, polluted) {
                        OrAny::Bool(true) => {}
                        OrAny::Any | OrAny::Bool(false) => {
                            *flow.get_mut(&flow_type_id).unwrap().get_type_mut().unwrap() =
                                type_str_ty;
                        }
                    }
                }
            }

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
                    flow_branch,
                    flow_branch_depth,
                    flow_branch_reverse,
                    polluted,
                    on_examination,
                    on_poisoning,
                );
            }

            let (obj_ty, mut res) = check_expression(
                &obj_expr,
                context,
                variable_type_bindings,
                flow,
                flow_branch,
                flow_branch_depth,
                flow_branch_reverse,
                polluted,
                on_examination,
                on_poisoning,
            );
            if obj_ty.kind(flow, polluted).is_any() {
                return (Ty::new(TypeKind::Any), res);
            }
            match &member_expr.kind {
                ExpressionKind::Variable(variable_name) => {
                    if *on_examination {
                        if let Ty::FlowType(_, _) = obj_ty {
                            return (Ty::new(TypeKind::Any), vec![]);
                        }
                    }

                    let coercions = obj_ty.kind(flow, polluted).get_coercion_list();
                    // check is interface function
                    {
                        let interfaces = obj_ty.kind(flow, polluted).get_interface(&coercions);
                        if let Some(member) = interfaces.iter().find_map(|interface| {
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
                        }) {
                            return (member.clone(), res);
                        }
                    }

                    if let Ty::FlowType(flow_obj_ty_id, poison) = &obj_ty {
                        if flow_branch_reverse == false {
                            if *poison {
                                *polluted.borrow_mut() = true;
                            }
                            if let Some(flow_obj_ty) = flow.get(&flow_obj_ty_id) {
                                if let TypeKind::Map(MayLiteral::Literal(map_literal)) =
                                    flow_obj_ty.kind(flow, polluted)
                                {
                                    let mut map_literal = map_literal.clone();
                                    let new_ty_id = TypeID::new();
                                    flow.insert(
                                        new_ty_id.clone(),
                                        Ty::Type(new_ty_id.clone(), TypeKind::Any),
                                    );
                                    map_literal.literals.insert(
                                        variable_name.clone(),
                                        Ty::FlowType(new_ty_id.clone(), on_poisoning),
                                    );
                                    *flow
                                        .get_mut(&flow_obj_ty_id)
                                        .unwrap()
                                        .get_type_mut()
                                        .unwrap() = TypeKind::Map(MayLiteral::Literal(map_literal));

                                    return (Ty::FlowType(new_ty_id, on_poisoning), vec![]);
                                } else if let TypeKind::Map(MayLiteral::Unknown) =
                                    flow_obj_ty.kind(flow, polluted)
                                {
                                    let mut map_literal = MapLiteral {
                                        literals: HashMap::new(),
                                        default: None,
                                    };
                                    let new_ty_id = TypeID::new();
                                    flow.insert(
                                        new_ty_id.clone(),
                                        Ty::Type(new_ty_id.clone(), TypeKind::Any),
                                    );
                                    map_literal.literals.insert(
                                        variable_name.clone(),
                                        Ty::FlowType(new_ty_id.clone(), on_poisoning),
                                    );
                                    *flow
                                        .get_mut(&flow_obj_ty_id)
                                        .unwrap()
                                        .get_type_mut()
                                        .unwrap() = TypeKind::Map(MayLiteral::Literal(map_literal));

                                    return (Ty::FlowType(new_ty_id, on_poisoning), vec![]);
                                }
                            }
                        } else {
                            return (Ty::new(TypeKind::Any), res);
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
                    let obj_ty = obj_ty.kind(flow, polluted).clone();
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
                                flow_branch,
                                flow_branch_depth,
                                flow_branch_reverse,
                                polluted,
                                on_examination,
                                on_poisoning,
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
                        polluted,
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
                flow_branch,
                flow_branch_depth,
                flow_branch_reverse,
                polluted,
                on_examination,
                on_poisoning,
            );
            let (subscript_ty, subscript_res) = check_expression(
                &subscript_expr,
                context,
                variable_type_bindings,
                flow,
                flow_branch,
                flow_branch_depth,
                flow_branch_reverse,
                polluted,
                on_examination,
                on_poisoning,
            );
            let (return_ty, return_res) = check_interface_function_calling(
                expr,
                context,
                obj_ty,
                FunctionKind::Subscript,
                vec![subscript_ty],
                flow,
                flow_branch_reverse,
                polluted,
                &on_examination,
                on_poisoning,
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
                            flow_branch,
                            flow_branch_depth,
                            flow_branch_reverse,
                            polluted,
                            on_examination,
                            on_poisoning,
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
                .and_then(|node| Some(node.1))
            {
                Some(FunctionNodeRef::Function(node)) => {
                    let (return_ty, return_res) = check_function(
                        expr,
                        node,
                        &params_ty,
                        context,
                        variable_type_bindings,
                        flow,
                        flow_branch,
                        flow_branch_depth,
                        flow_branch_reverse,
                        polluted,
                        on_examination,
                        on_poisoning,
                    );
                    (return_ty, [params_res, return_res].concat())
                }
                Some(FunctionNodeRef::GlobalFunction(function_ty_candidates)) => {
                    let (return_ty, return_res) = check_function_args(
                        expr,
                        format!("`{}()`", fn_name),
                        None,
                        &function_ty_candidates.iter().collect(),
                        params_ty,
                        flow,
                        polluted,
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
    // TODO
    let mut flow_branch: Vec<Branch> = vec![];
    let mut branch_count = 0;

    let mut result = vec![];
    let mut _polluted = RefCell::new(false);

    println!("begin check rule {}", rule.span.0.start_point);

    loop {
        let mut flow = flow.clone();
        let mut flow_branch_depth = 0;
        let mut on_examination = false;
        let mut polluted = RefCell::new(false);
        let (ty, iter_result) = check_expression(
            &rule.condition,
            context,
            &variable_type_bindings,
            &mut flow,
            &mut flow_branch,
            &mut flow_branch_depth,
            false,
            &mut polluted,
            &mut on_examination,
            false,
        );
        result.extend(iter_result);

        // check condition is boolean
        let (_, res) = check_can_be(
            &ty,
            &Ty::new(TypeKind::Boolean(MayLiteral::Unknown)),
            &rule.condition,
            &flow,
            &mut _polluted,
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
                &mut _polluted,
            ) {
                result.push(TypeCheckResult {
                    reason: "always true".to_owned(),
                    at: rule.condition.get_span().into(),
                })
            }
            if let OrAny::Bool(true) = ty.can_be(
                &Ty::new(TypeKind::Boolean(MayLiteral::Literal(false))),
                &flow,
                &mut _polluted,
            ) {
                result.push(TypeCheckResult {
                    reason: "always false".to_owned(),
                    at: rule.condition.get_span().into(),
                })
            }
        }

        // println!(
        //     "{:?}",
        //     flow.get(request_resource_data_ty_id)
        //         .unwrap()
        //         .expand_for_debug(&flow)
        // );
        // println!("polluted: {}", polluted.borrow());
        // println!("before {:?}", flow_branch);

        let flow_branch_len = flow_branch.len();
        if let Some(examination_branch_pos) = flow_branch.iter().rev().position(|branch| {
            *branch == Branch::Examination(false) || *branch == Branch::Examination(true)
        }) {
            match flow_branch[flow_branch_len - 1 - examination_branch_pos] {
                Branch::Examination(false) => {
                    flow_branch.drain(flow_branch_len - 1 - examination_branch_pos + 1..);
                    if *polluted.borrow() == true {
                        *flow_branch.last_mut().unwrap() = Branch::Side(false)
                    } else {
                        *flow_branch.last_mut().unwrap() = Branch::Examination(true)
                    }
                }
                Branch::Examination(true) => {
                    flow_branch.drain(flow_branch_len - 1 - examination_branch_pos + 1..);
                    if *polluted.borrow() == true {
                        *flow_branch.last_mut().unwrap() = Branch::Side(false)
                    } else {
                        *flow_branch.last_mut().unwrap() = Branch::Through
                    }
                }
                _ => panic!(),
            }
        } else {
            let non_false_count = flow_branch
                .iter()
                .rev()
                .position(|branch| *branch == Branch::Side(false));
            match non_false_count {
                None => {
                    println!(
                        "{:#?}",
                        flow.get(request_resource_data_ty_id)
                            .unwrap()
                            .expand_for_debug(&flow)
                    );
                    break;
                }
                Some(count) => {
                    flow_branch.drain(flow_branch_len - 1 - count + 1..);
                    *flow_branch.last_mut().unwrap() = Branch::Side(true);
                }
            }
        }

        // println!("after {:?}", flow_branch);

        branch_count += 1;
    }

    println!("{:?}", branch_count);

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
