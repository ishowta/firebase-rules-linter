use base64::{engine::general_purpose, Engine as _};
use std::{collections::HashMap, iter::zip};

use crate::{
    ast::{BinaryLiteral, UnaryLiteral},
    checker::TypeCheckResult,
    orany::OrAny,
    ty::{
        FunctionInterface, FunctionKind, Interface, ListLiteral, MapLiteral, MayLiteral::*,
        MemberKind, Ty, TypeKind,
    },
};

impl TypeKind {
    pub fn get_interface<'a>(&'a self, coercions: &'a Vec<TypeKind>) -> Vec<Interface> {
        let mut result = vec![];
        result.push(self.get_exactly_interface());
        for coercion in coercions {
            result.push(coercion.get_exactly_interface())
        }
        result
    }

    pub fn get_exactly_interface<'a>(self: &'a TypeKind) -> Interface<'a> {
        let mut interface = Interface {
            functions: HashMap::new(),
            members: HashMap::new(),
        };

        match &self {
            TypeKind::Any => {
                interface.functions.extend([]);
                interface.members.extend([]);
            }
            TypeKind::Null => {
                interface.functions.extend([
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Eq),
                        vec![FunctionInterface(
                            (vec![TypeKind::Any], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match &params[..] {
                                [TypeKind::Null] => {
                                    (Ty::new(TypeKind::Boolean(Literal(true))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::NotEq),
                        vec![FunctionInterface(
                            (vec![TypeKind::Any], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match &params[..] {
                                [TypeKind::Null] => {
                                    (Ty::new(TypeKind::Boolean(Literal(false))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                ]);
                interface.members.extend([]);
            }
            TypeKind::Boolean(lit) => {
                interface.functions.extend([
                    (FunctionKind::BinaryOp(BinaryLiteral::LogicalAnd), {
                        vec![FunctionInterface(
                            (vec![TypeKind::Boolean(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (lit, &params[..]) {
                                (Unknown, [TypeKind::Boolean(Literal(false))])
                                | (Literal(false), [TypeKind::Boolean(Unknown)]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(false))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )]
                    }),
                    (FunctionKind::BinaryOp(BinaryLiteral::LogicalOr), {
                        vec![FunctionInterface(
                            (vec![TypeKind::Boolean(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (lit, &params[..]) {
                                (Unknown, [TypeKind::Boolean(Literal(true))])
                                | (Literal(true), [TypeKind::Boolean(Unknown)]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(true))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )]
                    }),
                    (FunctionKind::UnaryOp(UnaryLiteral::Not), {
                        vec![FunctionInterface(
                            (vec![], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, _, _, _| match lit {
                                Literal(false) => {
                                    (Ty::new(TypeKind::Boolean(Literal(true))), vec![])
                                }
                                Literal(true) => {
                                    (Ty::new(TypeKind::Boolean(Literal(false))), vec![])
                                }
                                Unknown => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )]
                    }),
                ]);
                interface.members.extend([]);
            }
            TypeKind::Bytes(lit) => {
                interface.functions.extend([
                    (
                        FunctionKind::Function("size".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| match lit {
                                Literal(left) => (
                                    Ty::new(TypeKind::Integer(Literal(left.len() as i64))),
                                    vec![],
                                ),
                                _ => (Ty::new(TypeKind::Integer(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("toBase64".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::String(Unknown)),
                            Box::new(move |_, _, _, _| match lit {
                                Literal(left) => (
                                    Ty::new(TypeKind::String(Literal(
                                        general_purpose::STANDARD.encode(&left),
                                    ))),
                                    vec![],
                                ),
                                _ => (Ty::new(TypeKind::String(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("toHexString".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::String(Unknown)),
                            Box::new(move |_, _, _, _| match lit {
                                Literal(left) => (
                                    Ty::new(TypeKind::String(Literal(format!("{:02X?}", left)))),
                                    vec![],
                                ),
                                _ => (Ty::new(TypeKind::String(Unknown)), vec![]),
                            }),
                        )],
                    ),
                ]);
                interface.members.extend([])
            }
            TypeKind::Duration => {
                interface.functions.extend([
                    (
                        FunctionKind::Function("nanos".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("seconds".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                ]);
                interface.members.extend([])
            }
            TypeKind::Float(ty) => {
                interface.functions.extend([
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Eq),
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Float(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left == right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::NotEq),
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Float(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left != right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Gt),
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Float(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left > right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Gte),
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Float(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left >= right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Lt),
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Float(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left < right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Lte),
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Float(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left <= right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Add),
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Float(Literal(right))]) => {
                                    (Ty::new(TypeKind::Float(Literal(left + right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Float(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Sub),
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Float(Literal(right))]) => {
                                    (Ty::new(TypeKind::Float(Literal(left - right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Float(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Div),
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Float(Literal(right))]) => {
                                    (Ty::new(TypeKind::Float(Literal(left / right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Float(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Mul),
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Float(Literal(right))]) => {
                                    (Ty::new(TypeKind::Float(Literal(left * right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Float(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Mod),
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Float(Literal(right))]) => {
                                    (Ty::new(TypeKind::Float(Literal(left % right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Float(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::UnaryOp(UnaryLiteral::Minus),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Float(Unknown)),
                            Box::new(move |_, _, _, _| match ty {
                                Literal(lit) => (Ty::new(TypeKind::Float(Literal(-lit))), vec![]),
                                _ => (Ty::new(TypeKind::Float(Unknown)), vec![]),
                            }),
                        )],
                    ),
                ]);
                interface.members.extend([])
            }
            TypeKind::Integer(ty) => {
                interface.functions.extend([
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Eq),
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Integer(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left == right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::NotEq),
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Integer(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left != right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Gt),
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Integer(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left > right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Gte),
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Integer(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left >= right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Lt),
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Integer(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left < right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Lte),
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Integer(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left <= right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Add),
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Integer(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Integer(Literal(right))]) => {
                                    (Ty::new(TypeKind::Integer(Literal(left + right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Integer(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Sub),
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Integer(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Integer(Literal(right))]) => {
                                    (Ty::new(TypeKind::Integer(Literal(left - right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Integer(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Div),
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Integer(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Integer(Literal(right))]) => {
                                    (Ty::new(TypeKind::Integer(Literal(left / right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Integer(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Mul),
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Integer(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Integer(Literal(right))]) => {
                                    (Ty::new(TypeKind::Integer(Literal(left * right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Integer(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Mod),
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Integer(Unknown)),
                            Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::Integer(Literal(right))]) => {
                                    (Ty::new(TypeKind::Integer(Literal(left % right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Integer(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::UnaryOp(UnaryLiteral::Minus),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| match ty {
                                Literal(lit) => (Ty::new(TypeKind::Integer(Literal(-lit))), vec![]),
                                _ => (Ty::new(TypeKind::Integer(Unknown)), vec![]),
                            }),
                        )],
                    ),
                ]);
                interface.members.extend([])
            }
            TypeKind::LatLng => {
                interface.functions.extend([
                    (
                        FunctionKind::Function("distance".to_owned()),
                        vec![FunctionInterface(
                            (vec![TypeKind::LatLng], TypeKind::Float(Unknown)),
                            Box::new(move |_, _, _, _| (Ty::new(TypeKind::Float(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("latitude".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Float(Unknown)),
                            Box::new(move |_, _, _, _| (Ty::new(TypeKind::Float(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("longitude".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Float(Unknown)),
                            Box::new(move |_, _, _, _| (Ty::new(TypeKind::Float(Unknown)), vec![])),
                        )],
                    ),
                ]);
                interface.members.extend([])
            }
            TypeKind::List(ty) => {
                interface.functions.extend([
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Eq),
                        vec![FunctionInterface(
                            (vec![TypeKind::List(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, flow, polluted| match (ty, &params[..]) {
                                (
                                    Literal(ListLiteral::Tuple(left)),
                                    [TypeKind::List(Literal(ListLiteral::Tuple(right)))],
                                ) if ((
                                   OrAny::all(zip(left, right), |(left, right)| left.can_be(right, flow, polluted)).and(
                                    || {
                                       OrAny::all(zip(left, right), |(left, right)| {
                                            left.can_be(right, flow, polluted)
                                        })
                                    },
                                ))).is_true() =>
                                {
                                    (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Subscript,
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Any),
                            Box::new(move |node, params, _,_| match (ty, &params[..]) {
                                (
                                Literal(ListLiteral::Tuple(tuple)),
                                                    [TypeKind::Integer(Literal(index))],
                                               ) => {
                                    if let Result::Ok(index_uint) = usize::try_from(*index) {
                                        if let Some(elem) = tuple.get(index_uint)
                                        {
                                            (elem.clone(), vec![])
                                        } else {
                                            (
                                                Ty::new(TypeKind::List(Unknown)),
                                                vec![
                                                    (TypeCheckResult {
                                                        reason: "index out of range".to_owned(),
                                                        at: node.get_span().into(),
                                                    }),
                                                ],
                                            )
                                        }
                                    } else {
                                        (
                                            Ty::new(TypeKind::List(Unknown)),
                                            vec![
                                                (TypeCheckResult {
                                                    reason: "index must be unsigned integer"
                                                        .to_owned(),
                                                    at: node.get_span().into(),
                                                }),
                                            ],
                                        )
                                    }
                                }
                                (Literal(ListLiteral::Single(x)), _) => (*x.clone(), vec![]),
                                _ => (Ty::new(TypeKind::Any), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::SubscriptRange,
                        vec![FunctionInterface(
                            (
                                vec![TypeKind::Integer(Unknown), TypeKind::Integer(Unknown)],
                                TypeKind::List(Unknown),
                            ),
                            Box::new(move |node, params, _,_| match (ty, &params[..]) {
                                (
                                    _,
                                    [TypeKind::Integer(Literal(index)), TypeKind::Integer(Unknown)],
                                )
                                | (
                                    _,
                                    [TypeKind::Integer(Unknown), TypeKind::Integer(Literal(index))],
                                ) if *index < 0 => (
                                    Ty::new(TypeKind::List(Unknown)),
                                    vec![
                                        (TypeCheckResult {
                                            reason: "range index must be unsigned integer"
                                                .to_owned(),
                                            at: node.get_span().into(),
                                        }),
                                    ],
                                ),
                                (
                                    _,
                                    [TypeKind::Integer(Literal(from)), TypeKind::Integer(Literal(to))],
                                ) if to <= from => (
                                    Ty::new(TypeKind::List(Unknown)),
                                    vec![
                                        (TypeCheckResult {
                                            reason: "invalid range".to_owned(),
                                            at: node.get_span().into(),
                                        }),
                                    ],
                                ),
                                (
                                    Literal(ListLiteral::Tuple(tuple)),
                                    [TypeKind::Integer(Literal(from)), TypeKind::Integer(Literal(to))],
                                ) => {
                                    if let Some(slice) = tuple
                                        .get(*from as usize..*to as usize)
                                    {
                                        (Ty::new(TypeKind::List(Literal(ListLiteral::Tuple(slice.iter().cloned().collect())))), vec![])
                                    } else {
                                        (
                                            Ty::new(TypeKind::List(Unknown)),
                                            vec![
                                                (TypeCheckResult {
                                                    reason: "index out of range".to_owned(),
                                                    at: node.get_span().into(),
                                                }),
                                            ],
                                        )
                                    }
                                }
                                (Literal(ListLiteral::Single(x)), _) => (Ty::new(TypeKind::List(Literal(ListLiteral::Single(Box::new(*x.clone()))))), vec![]),
                                _ => (Ty::new(TypeKind::List(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::In),
                        vec![FunctionInterface(
                            (vec![TypeKind::List(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("concat".to_owned()),
                        vec![FunctionInterface(
                            (vec![TypeKind::List(Unknown)], TypeKind::List(Unknown)),
                            Box::new(move |_, params, _,_| match &params[..] {
                                [TypeKind::List(_)] => (Ty::new(TypeKind::List(Unknown)), vec![]),
                                _ => (Ty::new(TypeKind::List(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("hasAll".to_owned()),
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::List(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::Set(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                            ),
                        ],
                    ),
                    (
                        FunctionKind::Function("hasAny".to_owned()),
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::List(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::Set(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                            ),
                        ],
                    ),
                    (
                        FunctionKind::Function("hasOnly".to_owned()),
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::List(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::Set(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                            ),
                        ],
                    ),
                    (
                        FunctionKind::Function("join".to_owned()),
                        vec![FunctionInterface(
                            (vec![TypeKind::String(Unknown)], TypeKind::String(Unknown)),
                            Box::new(move |_, _, _,_| (Ty::new(TypeKind::String(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("removeAll".to_owned()),
                        vec![FunctionInterface(
                            (vec![TypeKind::List(Unknown)], TypeKind::List(Unknown)),
                            Box::new(move |_, _, flow, polluted| match ty {
                                Unknown => (Ty::new(TypeKind::List(Unknown)), vec![]),
                                Literal(lit) => {
                                    let max = lit.max(flow, polluted);
                                    match max.kind(flow, polluted) {
                                        TypeKind::Any => (Ty::new(TypeKind::List(Unknown)), vec![]),
                                        _ => (
                                            Ty::new(TypeKind::List(Literal(ListLiteral::Single(Box::new(max))))),
                                            vec![],
                                        ),
                                    }
                                },
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("size".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _,_| (Ty::new(TypeKind::Integer(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("toSet".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Set(Unknown)),
                            Box::new(move |_, _, _,_| match ty {
                                Literal(ListLiteral::Single(x)) => {
                                    (Ty::new(TypeKind::Set(Literal(x.clone()))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Set(Unknown)), vec![]),
                            }),
                        )],
                    ),
                ]);
                interface.members.extend([])
            }
            TypeKind::Map(left) => {
                interface.functions.extend([
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Eq),
                        vec![FunctionInterface(
                            (vec![TypeKind::Map(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::NotEq),
                        vec![FunctionInterface(
                            (vec![TypeKind::Map(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Subscript,
                        vec![FunctionInterface(
                            (vec![TypeKind::String(Unknown)], TypeKind::Any),
                            Box::new(move |node, params, _,_| match (left, &params[..]) {
                                (Literal(left), [TypeKind::String(Literal(key))]) => {
                                    if let Some(value) = left.literals.get(key) {
                                        (value.clone(), vec![])
                                    } else {
                                        match &left.default {
                                            None => (
                                                Ty::new(TypeKind::Any),
                                                vec![
                                                    (TypeCheckResult {
                                                        reason: format!("field not exist. expect {:?}, got {:?}", left.literals.keys(), key),
                                                        at: node.get_span().into(),
                                                    }),
                                                ],
                                            ),
                                            Some(_) => (Ty::new(TypeKind::Any), vec![]),
                                        }
                                    }
                                }
                                _ => (Ty::new(TypeKind::Any), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::In),
                        vec![FunctionInterface(
                            (vec![TypeKind::String(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _,_| match (left, &params[..]) {
                                (Literal(left), [TypeKind::String(Literal(key))]) => {
                                    if let Some(_) = left.literals.get(key) {
                                        (Ty::new(TypeKind::Boolean(Literal(true))), vec![])
                                    } else {
                                        match &left.default {
                                            None => (Ty::new(TypeKind::Boolean(Literal(false))), vec![]),
                                            Some(_) => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                                        }
                                    }
                                }
                                _ => (Ty::new(TypeKind::Any), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("diff".to_owned()),
                        vec![FunctionInterface(
                            (
                                vec![TypeKind::Map(Unknown)],
                                TypeKind::MapDiff((Unknown, Unknown)),
                            ),
                            Box::new(move |_, params, _,_| match &params[..] {
                                [TypeKind::Map(right)] => {
                                    (Ty::new(TypeKind::MapDiff((left.clone(), right.clone()))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Any), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("get".to_owned()),
                        vec![
                            FunctionInterface(
                                (
                                    vec![TypeKind::String(Unknown), TypeKind::Any],
                                    TypeKind::Any,
                                ),
                                Box::new(move |_, params, _,_| match (left, &params[..]) {
                                    (
                                        Literal(left),
                                        [TypeKind::String(Literal(key)), default_value_ty],
                                    ) => {
                                        if let Some(value) = left.literals.get(key) {
                                            (value.clone(), vec![])
                                        } else {
                                            match &left.default {
                                                None => (Ty::new((**default_value_ty).clone()), vec![]),
                                                Some(_) => (Ty::new(TypeKind::Any), vec![]),
                                            }
                                        }
                                    }
                                    _ => (Ty::new(TypeKind::Any), vec![]),
                                }),
                            ),
                            FunctionInterface(
                                (
                                    vec![
                                        TypeKind::List(Unknown),
                                        TypeKind::Any,
                                    ],
                                    TypeKind::Any,
                                ),
                                Box::new(move |_, _, _,_| (Ty::new(TypeKind::Any), vec![])),
                            ),
                        ],
                    ),
                    (
                        FunctionKind::Function("keys".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::List(Unknown)),
                            Box::new(move |_, _, _,_| match left {
                                Literal(MapLiteral { literals, default: None }) => (Ty::new(TypeKind::List(Literal(ListLiteral::Tuple(
                                    literals.keys().map(|key| Ty::new(TypeKind::String(Literal(key.clone())))).collect()
                                )))), vec![]),
                                _ => (Ty::new(TypeKind::List(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("size".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _,_| match left {
                                Literal(MapLiteral {
                                    literals,
                                    default: None,
                                }) => (
                                    Ty::new(TypeKind::Integer(Literal(literals.len().try_into().unwrap()))),
                                    vec![],
                                ),
                                _ => (Ty::new(TypeKind::Integer(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("values".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::List(Unknown)),
                            Box::new(move |_, _, _,_| match left {
                                Literal(MapLiteral {
                                    literals,
                                    default: Some(default),
                                }) if literals.is_empty() => {
                                    (Ty::new(TypeKind::List(Literal(ListLiteral::Single(default.clone())))), vec![])
                                }
                                _ => (Ty::new(TypeKind::List(Unknown)), vec![]),
                            }),
                        )],
                    ),
                ]);
                match left {
                    Literal(left) => {
                        for (key, value) in left.literals.iter() {
                            interface
                                .members
                                .insert(MemberKind::Member(key.clone()), value.clone());
                        }
                        if left.default.is_some() {
                            interface
                                .members
                                .insert(MemberKind::AnyMember, Ty::new(TypeKind::Any));
                        }
                    }
                    Unknown => {
                        interface
                            .members
                            .insert(MemberKind::AnyMember, Ty::new(TypeKind::Any));
                    }
                }
            }
            TypeKind::MapDiff(_) => {
                interface.functions.extend([
                    (
                        FunctionKind::Function("addedKeys".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Set(Unknown)),
                            Box::new(move |_, _, _, _| (Ty::new(TypeKind::Set(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("affectedKeys".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Set(Unknown)),
                            Box::new(move |_, _, _, _| (Ty::new(TypeKind::Set(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("changedKeys".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Set(Unknown)),
                            Box::new(move |_, _, _, _| (Ty::new(TypeKind::Set(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("removedKeys".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Set(Unknown)),
                            Box::new(move |_, _, _, _| (Ty::new(TypeKind::Set(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("unchangedKeys".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Set(Unknown)),
                            Box::new(move |_, _, _, _| (Ty::new(TypeKind::Set(Unknown)), vec![])),
                        )],
                    ),
                ]);
                interface.members.extend([])
            }
            TypeKind::Path(ty) => {
                interface.functions.extend([
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Eq),
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::Path(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                    (Literal(left), [TypeKind::Path(Literal(right))]) => {
                                        (Ty::new(TypeKind::Boolean(Literal(left == right))), vec![])
                                    }
                                    _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                                }),
                            ),
                            FunctionInterface(
                                (
                                    vec![TypeKind::PathTemplateBound(Unknown)],
                                    TypeKind::Boolean(Unknown),
                                ),
                                Box::new(move |_, _, _, _| {
                                    (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                                }),
                            ),
                        ],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::NotEq),
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::Path(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, params, _, _| match (ty, &params[..]) {
                                    (Literal(left), [TypeKind::Path(Literal(right))]) => {
                                        (Ty::new(TypeKind::Boolean(Literal(left != right))), vec![])
                                    }
                                    _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![]),
                                }),
                            ),
                            FunctionInterface(
                                (
                                    vec![TypeKind::PathTemplateBound(Unknown)],
                                    TypeKind::Boolean(Unknown),
                                ),
                                Box::new(move |_, _, _, _| {
                                    (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                                }),
                            ),
                        ],
                    ),
                ]);
                interface.members.extend([])
            }
            TypeKind::PathTemplateUnBound(ty) => {
                interface.functions.extend([(
                    FunctionKind::Function("bind".to_owned()),
                    vec![FunctionInterface(
                        (
                            vec![TypeKind::Map(Unknown)],
                            TypeKind::PathTemplateBound(Unknown),
                        ),
                        Box::new(move |node, params, _, _| match (ty, &params[..]) {
                            (
                                Literal(templates),
                                [TypeKind::Map(Literal(MapLiteral {
                                    literals,
                                    default: None,
                                }))],
                            ) if templates
                                .iter()
                                .any(|template| !literals.contains_key(template)) =>
                            {
                                (
                                    Ty::new(TypeKind::PathTemplateBound(Unknown)),
                                    vec![
                                        (TypeCheckResult {
                                            reason: "key not found".to_owned(),
                                            at: node.get_span().into(),
                                        }),
                                    ],
                                )
                            }
                            _ => (Ty::new(TypeKind::PathTemplateBound(Unknown)), vec![]),
                        }),
                    )],
                )]);
                interface.members.extend([])
            }
            TypeKind::PathTemplateBound(left) => {
                interface.functions.extend([
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Eq),
                        vec![
                            FunctionInterface(
                                (
                                    vec![TypeKind::PathTemplateBound(Unknown)],
                                    TypeKind::Boolean(Unknown),
                                ),
                                Box::new(move |_, _, _, _| {
                                    (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                                }),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::Path(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _, _| {
                                    (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                                }),
                            ),
                        ],
                    ),
                    (
                        FunctionKind::Subscript,
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::String(Unknown)], TypeKind::Any),
                                Box::new(move |node, params, _, _| match (left, &params[..]) {
                                    (Literal(templates), [TypeKind::String(Literal(key))])
                                        if templates
                                            .iter()
                                            .find(|template_key| *template_key == key)
                                            .is_none() =>
                                    {
                                        (
                                            Ty::new(TypeKind::Any),
                                            vec![
                                                (TypeCheckResult {
                                                    reason: "field not exist".to_owned(),
                                                    at: node.get_span().into(),
                                                }),
                                            ],
                                        )
                                    }
                                    _ => (Ty::new(TypeKind::Any), vec![]),
                                }),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::Integer(Unknown)], TypeKind::String(Unknown)),
                                Box::new(move |node, params, _, _| match (left, &params[..]) {
                                    (Literal(templates), [TypeKind::Integer(Literal(index))]) => {
                                        if let Result::Ok(index_uint) = u64::try_from(*index) {
                                            if templates.len() > (index_uint as usize) {
                                                (Ty::new(TypeKind::String(Unknown)), vec![])
                                            } else {
                                                (
                                                    Ty::new(TypeKind::String(Unknown)),
                                                    vec![
                                                        (TypeCheckResult {
                                                            reason: "index out of range".to_owned(),
                                                            at: node.get_span().into(),
                                                        }),
                                                    ],
                                                )
                                            }
                                        } else {
                                            (
                                                Ty::new(TypeKind::String(Unknown)),
                                                vec![
                                                    (TypeCheckResult {
                                                        reason: "index must be unsigned integer"
                                                            .to_owned(),
                                                        at: node.get_span().into(),
                                                    }),
                                                ],
                                            )
                                        }
                                    }
                                    _ => (Ty::new(TypeKind::String(Unknown)), vec![]),
                                }),
                            ),
                        ],
                    ),
                ]);
                interface.members = match left {
                    Unknown => {
                        HashMap::from([(MemberKind::AnyMember, Ty::new(TypeKind::String(Unknown)))])
                    }
                    Literal(templates) => {
                        let mut result: HashMap<_, _> = templates
                            .iter()
                            .map(|key| {
                                (
                                    MemberKind::Member(key.clone()),
                                    Ty::new(TypeKind::String(Unknown)),
                                )
                            })
                            .collect();
                        result.insert(MemberKind::AnyMember, Ty::new(TypeKind::String(Unknown)));
                        result
                    }
                }
            }
            TypeKind::Set(lit) => {
                interface.functions.extend([
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Eq),
                        vec![FunctionInterface(
                            (vec![TypeKind::Set(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::In),
                        vec![FunctionInterface(
                            (vec![TypeKind::Set(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("difference".to_owned()),
                        vec![FunctionInterface(
                            (vec![TypeKind::Set(Unknown)], TypeKind::Set(Unknown)),
                            Box::new(move |_, params, flow, polluted| match &params[..] {
                                [TypeKind::Set(Literal(ty))] => (
                                    Ty::new(TypeKind::Set(Literal(Box::new(Ty::new(
                                        ty.kind(flow, polluted).erase_literal_constraint(),
                                    ))))),
                                    vec![],
                                ),
                                _ => (Ty::new(TypeKind::Set(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("hasAll".to_owned()),
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::List(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _, _| {
                                    (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                                }),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::Set(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _, _| {
                                    (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                                }),
                            ),
                        ],
                    ),
                    (
                        FunctionKind::Function("hasAny".to_owned()),
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::List(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _, _| {
                                    (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                                }),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::Set(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _, _| {
                                    (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                                }),
                            ),
                        ],
                    ),
                    (
                        FunctionKind::Function("hasOnly".to_owned()),
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::List(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _, _| {
                                    (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                                }),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::Set(Unknown)], TypeKind::Boolean(Unknown)),
                                Box::new(move |_, _, _, _| {
                                    (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                                }),
                            ),
                        ],
                    ),
                    (
                        FunctionKind::Function("intersection".to_owned()),
                        vec![FunctionInterface(
                            (vec![TypeKind::Set(Unknown)], TypeKind::Set(Unknown)),
                            Box::new(move |_, params, flow, polluted| match &params[..] {
                                [TypeKind::Set(Literal(ty))] => (
                                    Ty::new(TypeKind::Set(Literal(Box::new(Ty::new(
                                        ty.kind(flow, polluted).erase_literal_constraint(),
                                    ))))),
                                    vec![],
                                ),
                                _ => (Ty::new(TypeKind::Set(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("size".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("union".to_owned()),
                        vec![FunctionInterface(
                            (vec![TypeKind::Set(Unknown)], TypeKind::Set(Unknown)),
                            Box::new(move |_, params, flow, polluted| match &params[..] {
                                [TypeKind::Set(Literal(ty))] => (
                                    Ty::new(TypeKind::Set(Literal(Box::new(Ty::new(
                                        ty.kind(flow, polluted).erase_literal_constraint(),
                                    ))))),
                                    vec![],
                                ),
                                _ => (Ty::new(TypeKind::Set(Unknown)), vec![]),
                            }),
                        )],
                    ),
                ]);
                interface.members.extend([(MemberKind::AnyMember, {
                    match lit {
                        Unknown => Ty::new(TypeKind::Any),
                        Literal(ty) => *ty.clone(),
                    }
                })])
            }
            TypeKind::String(ty) => {
                interface.functions.extend([
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Eq),
                        vec![FunctionInterface(
                            (vec![TypeKind::String(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _,_| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::String(Literal(right))])
                                     =>
                                {
                                    (Ty::new(TypeKind::Boolean(Literal(left == right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::NotEq),
                        vec![FunctionInterface(
                            (vec![TypeKind::String(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _,_| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::String(Literal(right))])
                                     =>
                                {
                                    (Ty::new(TypeKind::Boolean(Literal(left != right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Gt),
                        vec![FunctionInterface(
                            (vec![TypeKind::String(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _,_| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::String(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left > right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Gte),
                        vec![FunctionInterface(
                            (vec![TypeKind::String(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _,_| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::String(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left >= right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Lt),
                        vec![FunctionInterface(
                            (vec![TypeKind::String(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _,_| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::String(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left < right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Lte),
                        vec![FunctionInterface(
                            (vec![TypeKind::String(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, params, _,_| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::String(Literal(right))]) => {
                                    (Ty::new(TypeKind::Boolean(Literal(left <= right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Boolean(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::BinaryOp(BinaryLiteral::Add),
                        vec![FunctionInterface(
                            (vec![TypeKind::String(Unknown)], TypeKind::String(Unknown)),
                            Box::new(move |_, params, _,_| match (ty, &params[..]) {
                                (Literal(left), [TypeKind::String(Literal(right))]) => {
                                    (Ty::new(TypeKind::String(Literal(left.clone() + right))), vec![])
                                }
                                _ => (Ty::new(TypeKind::String(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Subscript,
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::String(Unknown)),
                            Box::new(move |node, params, _,_| match &params[..] {
                                [TypeKind::Integer(Unknown)] => (Ty::new(TypeKind::String(Unknown)), vec![]),
                                [TypeKind::Integer(Literal(index))] => {
                                    if let Result::Ok(index_uint) = u64::try_from(*index) {
                                        if let Some(c) = ty
                                            .to_option()
                                            .map(|literal| literal.chars().nth(index_uint as usize))
                                            .flatten()
                                        {
                                            (Ty::new(TypeKind::String(Literal(c.to_string()))), vec![])
                                        } else {
                                            (
                                                Ty::new(TypeKind::String(Unknown)),
                                                vec![
                                                    (TypeCheckResult {
                                                        reason: "index out of range".to_owned(),
                                                        at: node.get_span().into(),
                                                    }),
                                                ],
                                            )
                                        }
                                    } else {
                                        (
                                            Ty::new(TypeKind::String(Unknown)),
                                            vec![
                                                (TypeCheckResult {
                                                    reason: "index must be unsigned integer"
                                                        .to_owned(),
                                                    at: node.get_span().into(),
                                                }),
                                            ],
                                        )
                                    }
                                }
                                _ => panic!(),
                            }),
                        )],
                    ),
                    (
                        FunctionKind::SubscriptRange,
                        vec![FunctionInterface(
                            (
                                vec![TypeKind::Integer(Unknown), TypeKind::Integer(Unknown)],
                                TypeKind::String(Unknown),
                            ),
                            Box::new(move |node, params, _,_| match (ty, &params[..]) {
                                (
                                    _,
                                    [TypeKind::Integer(Literal(index)), TypeKind::Integer(Unknown)],
                                )
                                | (
                                    _,
                                    [TypeKind::Integer(Unknown), TypeKind::Integer(Literal(index))],
                                ) if *index < 0 => (
                                    Ty::new(TypeKind::String(Unknown)),
                                    vec![
                                        (TypeCheckResult {
                                            reason: "range index must be unsigned integer"
                                                .to_owned(),
                                            at: node.get_span().into(),
                                        }),
                                    ],
                                ),
                                (
                                    _,
                                    [TypeKind::Integer(Literal(from)), TypeKind::Integer(Literal(to))],
                                ) if to <= from => (
                                    Ty::new(TypeKind::String(Unknown)),
                                    vec![
                                        (TypeCheckResult {
                                            reason: "invalid range".to_owned(),
                                            at: node.get_span().into(),
                                        }),
                                    ],
                                ),
                                (
                                    Literal(literal),
                                    [TypeKind::Integer(Literal(from)), TypeKind::Integer(Literal(to))],
                                ) => {
                                    if let Some(slice) = literal
                                        .chars()
                                        .collect::<Vec<_>>()
                                        .get(*from as usize..*to as usize)
                                    {
                                        (Ty::new(TypeKind::String(Literal(slice.iter().collect()))), vec![])
                                    } else {
                                        (
                                            Ty::new(TypeKind::String(Unknown)),
                                            vec![
                                                (TypeCheckResult {
                                                    reason: "index out of range".to_owned(),
                                                    at: node.get_span().into(),
                                                }),
                                            ],
                                        )
                                    }
                                }
                                _ => (Ty::new(TypeKind::String(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("lower".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::String(Unknown)),
                            Box::new(move |_, _, _,_| match ty {
                                Literal(left) => {
                                    (Ty::new(TypeKind::String(Literal(left.to_lowercase()))), vec![])
                                }
                                _ => (Ty::new(TypeKind::String(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("matches".to_owned()),
                        vec![FunctionInterface(
                            (vec![TypeKind::String(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("replace".to_owned()),
                        vec![FunctionInterface(
                            (vec![TypeKind::String(Unknown)], TypeKind::Boolean(Unknown)),
                            Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("size".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _,_| match ty {
                                Literal(left) => (
                                    Ty::new(TypeKind::Integer(Literal(left.len().try_into().unwrap()))),
                                    vec![],
                                ),
                                _ => (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("split".to_owned()),
                        vec![FunctionInterface(
                            (
                                vec![TypeKind::String(Unknown)],
                                TypeKind::List(Unknown),
                            ),
                            Box::new(move |_, _, _,_| {
                                (Ty::new(TypeKind::List(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("toUtf8".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::String(Unknown)),
                            Box::new(move |_, _, _,_| match ty {
                                Literal(left) => {
                                    (Ty::new(TypeKind::Bytes(Literal(left.bytes().collect()))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Bytes(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("trim".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::String(Unknown)),
                            Box::new(move |_, _, _,_| match ty {
                                Literal(left) => {
                                    (Ty::new(TypeKind::String(Literal(left.trim().to_owned()))), vec![])
                                }
                                _ => (Ty::new(TypeKind::String(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("upper".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::String(Unknown)),
                            Box::new(move |_, _, _,_| match ty {
                                Literal(left) => {
                                    (Ty::new(TypeKind::String(Literal(left.to_uppercase()))), vec![])
                                }
                                _ => (Ty::new(TypeKind::String(Unknown)), vec![])
                            }),
                        )],
                    ),
                ]);
                interface.members.extend([])
            }
            TypeKind::Timestamp => {
                interface.functions.extend([
                    (
                        FunctionKind::Function("date".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Timestamp),
                            Box::new(move |_, _, _, _| (Ty::new(TypeKind::Timestamp), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("day".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("dayOfWeek".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("dayOfYear".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("hours".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("minutes".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("month".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("nanos".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("seconds".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("time".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Duration),
                            Box::new(move |_, _, _, _| (Ty::new(TypeKind::Duration), vec![])),
                        )],
                    ),
                    (
                        FunctionKind::Function("toMillis".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                    (
                        FunctionKind::Function("year".to_owned()),
                        vec![FunctionInterface(
                            (vec![], TypeKind::Integer(Unknown)),
                            Box::new(move |_, _, _, _| {
                                (Ty::new(TypeKind::Integer(Unknown)), vec![])
                            }),
                        )],
                    ),
                ]);
                interface.members.extend([])
            }
        }

        if let TypeKind::Null = self {
        } else {
            interface
                .functions
                .entry(FunctionKind::BinaryOp(BinaryLiteral::Eq))
                .and_modify(|v| {
                    v.push(FunctionInterface(
                        (vec![TypeKind::Null], TypeKind::Boolean(Unknown)),
                        Box::new(move |_, _, _, _| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                    ))
                })
                .or_insert(vec![FunctionInterface(
                    (vec![TypeKind::Null], TypeKind::Boolean(Unknown)),
                    Box::new(move |_, _, _, _| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                )]);
            interface
                .functions
                .entry(FunctionKind::BinaryOp(BinaryLiteral::NotEq))
                .and_modify(|v| {
                    v.push(FunctionInterface(
                        (vec![TypeKind::Null], TypeKind::Boolean(Unknown)),
                        Box::new(move |_, _, _, _| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                    ))
                })
                .or_insert(vec![FunctionInterface(
                    (vec![TypeKind::Null], TypeKind::Boolean(Unknown)),
                    Box::new(move |_, _, _, _| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                )]);
        }

        interface
    }
}
