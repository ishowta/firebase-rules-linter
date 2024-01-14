use std::collections::HashMap;

use chrono::NaiveDate;

use crate::{
    checker::TypeCheckResult,
    ty::{FunctionInterface, MayLiteral::*, TypeKind},
};

pub fn get_globals() -> (
    HashMap<&'static str, TypeKind>,
    HashMap<&'static str, Vec<FunctionInterface<'static>>>,
    HashMap<&'static str, HashMap<&'static str, Vec<FunctionInterface<'static>>>>,
) {
    (
        HashMap::from([
            ("request", TypeKind::Request),
            ("resource", TypeKind::Resource),
        ]),
        HashMap::from([
            (
                "debug",
                vec![FunctionInterface(
                    (vec![TypeKind::Any], TypeKind::Any),
                    Box::new(move |_, params| match &params[..] {
                        [ty] => (ty.clone(), vec![]),
                        _ => (TypeKind::Any, vec![]),
                    }),
                )],
            ),
            (
                "exists",
                vec![FunctionInterface(
                    (vec![TypeKind::Path(Unknown)], TypeKind::Boolean(Unknown)),
                    Box::new(move |_, _| (TypeKind::Boolean(Unknown), vec![])),
                )],
            ),
            (
                "existsAfter",
                vec![FunctionInterface(
                    (vec![TypeKind::Path(Unknown)], TypeKind::Boolean(Unknown)),
                    Box::new(move |_, _| (TypeKind::Boolean(Unknown), vec![])),
                )],
            ),
            (
                "get",
                vec![FunctionInterface(
                    (vec![TypeKind::Path(Unknown)], TypeKind::Resource),
                    Box::new(move |_, _| (TypeKind::Resource, vec![])),
                )],
            ),
            (
                "getAfter",
                vec![FunctionInterface(
                    (vec![TypeKind::Path(Unknown)], TypeKind::Resource),
                    Box::new(move |_, _| (TypeKind::Resource, vec![])),
                )],
            ),
            (
                "float",
                vec![
                    FunctionInterface(
                        (vec![TypeKind::String(Unknown)], TypeKind::Float(Unknown)),
                        Box::new(move |_, _| (TypeKind::Float(Unknown), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Integer(Unknown)], TypeKind::Float(Unknown)),
                        Box::new(move |_, _| (TypeKind::Float(Unknown), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                        Box::new(move |_, _| (TypeKind::Float(Unknown), vec![])),
                    ),
                ],
            ),
            (
                "int",
                vec![
                    FunctionInterface(
                        (vec![TypeKind::String(Unknown)], TypeKind::Integer(Unknown)),
                        Box::new(move |_, _| (TypeKind::Integer(Unknown), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Integer(Unknown)], TypeKind::Integer(Unknown)),
                        Box::new(move |_, _| (TypeKind::Integer(Unknown), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Float(Unknown)], TypeKind::Integer(Unknown)),
                        Box::new(move |_, _| (TypeKind::Integer(Unknown), vec![])),
                    ),
                ],
            ),
            (
                "string",
                vec![
                    FunctionInterface(
                        (vec![TypeKind::Boolean(Unknown)], TypeKind::String(Unknown)),
                        Box::new(move |_, _| (TypeKind::String(Unknown), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Integer(Unknown)], TypeKind::String(Unknown)),
                        Box::new(move |_, _| (TypeKind::String(Unknown), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Float(Unknown)], TypeKind::String(Unknown)),
                        Box::new(move |_, _| (TypeKind::String(Unknown), vec![])),
                    ),
                    FunctionInterface(
                        (
                            vec![TypeKind::Null],
                            TypeKind::String(Literal("null".to_owned())),
                        ),
                        Box::new(move |_, _| {
                            (TypeKind::String(Literal("null".to_owned())), vec![])
                        }),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::String(Unknown)], TypeKind::String(Unknown)),
                        Box::new(move |_, _| (TypeKind::String(Unknown), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Path(Unknown)], TypeKind::String(Unknown)),
                        Box::new(move |_, params| match &params[..] {
                            [TypeKind::Path(Literal(str))] => {
                                (TypeKind::String(Literal(str.clone())), vec![])
                            }
                            _ => (TypeKind::String(Unknown), vec![]),
                        }),
                    ),
                    FunctionInterface(
                        (
                            vec![TypeKind::PathTemplateBound(Unknown)],
                            TypeKind::String(Unknown),
                        ),
                        Box::new(move |_, _| (TypeKind::String(Unknown), vec![])),
                    ),
                ],
            ),
            (
                "path",
                vec![FunctionInterface(
                    (vec![TypeKind::String(Unknown)], TypeKind::Path(Unknown)),
                    Box::new(move |_, params| match &params[..] {
                        [TypeKind::String(Literal(str))] => {
                            (TypeKind::Path(Literal(str.clone())), vec![])
                        }
                        _ => (TypeKind::Path(Unknown), vec![]),
                    }),
                )],
            ),
        ]),
        HashMap::from([
            (
                "duration",
                HashMap::from([
                    (
                        "abs",
                        vec![FunctionInterface(
                            (vec![TypeKind::Duration], TypeKind::Duration),
                            Box::new(move |_, _| (TypeKind::Duration, vec![])),
                        )],
                    ),
                    (
                        "time",
                        vec![FunctionInterface(
                            (
                                vec![
                                    TypeKind::Integer(Unknown),
                                    TypeKind::Integer(Unknown),
                                    TypeKind::Integer(Unknown),
                                    TypeKind::Integer(Unknown),
                                ],
                                TypeKind::Duration,
                            ),
                            Box::new(move |_, _| (TypeKind::Duration, vec![])),
                        )],
                    ),
                    (
                        "value",
                        vec![FunctionInterface(
                            (
                                vec![TypeKind::Integer(Unknown), TypeKind::String(Unknown)],
                                TypeKind::Duration,
                            ),
                            Box::new(move |_, params| match &params[..] {
                                [TypeKind::String(Literal(str))]
                                    if ["w", "d", "h", "m", "s", "ms", "ns"]
                                        .contains(&(str as &str)) =>
                                {
                                    (TypeKind::Duration, vec![])
                                }
                                _ => (TypeKind::Duration, vec![]),
                            }),
                        )],
                    ),
                ]),
            ),
            (
                "hashing",
                HashMap::from([
                    (
                        "crc32",
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::Bytes(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _| (TypeKind::Bytes(Unknown), vec![])),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::String(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _| (TypeKind::Bytes(Unknown), vec![])),
                            ),
                        ],
                    ),
                    (
                        "crc32c",
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::Bytes(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _| (TypeKind::Bytes(Unknown), vec![])),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::String(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _| (TypeKind::Bytes(Unknown), vec![])),
                            ),
                        ],
                    ),
                    (
                        "md5",
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::Bytes(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _| (TypeKind::Bytes(Unknown), vec![])),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::String(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _| (TypeKind::Bytes(Unknown), vec![])),
                            ),
                        ],
                    ),
                    (
                        "sha256",
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::Bytes(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _| (TypeKind::Bytes(Unknown), vec![])),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::String(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _| (TypeKind::Bytes(Unknown), vec![])),
                            ),
                        ],
                    ),
                ]),
            ),
            (
                "latlng",
                HashMap::from([(
                    "value",
                    vec![FunctionInterface(
                        (
                            vec![TypeKind::Float(Unknown), TypeKind::Float(Unknown)],
                            TypeKind::LatLng,
                        ),
                        Box::new(move |_, _| (TypeKind::LatLng, vec![])),
                    )],
                )]),
            ),
            (
                "math",
                HashMap::from([
                    (
                        "abs",
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::Integer(Unknown)], TypeKind::Integer(Unknown)),
                                Box::new(move |_, params| match &params[..] {
                                    [TypeKind::Integer(Literal(x))] => {
                                        (TypeKind::Integer(Literal(-x)), vec![])
                                    }
                                    _ => (TypeKind::Integer(Unknown), vec![]),
                                }),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                                Box::new(move |_, params| match &params[..] {
                                    [TypeKind::Float(Literal(x))] => {
                                        (TypeKind::Float(Literal(-x)), vec![])
                                    }
                                    _ => (TypeKind::Float(Unknown), vec![]),
                                }),
                            ),
                        ],
                    ),
                    (
                        "ceil",
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params| match &params[..] {
                                [TypeKind::Float(Literal(x))] => {
                                    (TypeKind::Float(Literal(f64::ceil(*x))), vec![])
                                }
                                _ => (TypeKind::Float(Unknown), vec![]),
                            }),
                        )],
                    ),
                    (
                        "floor",
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params| match &params[..] {
                                [TypeKind::Float(Literal(x))] => {
                                    (TypeKind::Float(Literal(f64::floor(*x))), vec![])
                                }
                                _ => (TypeKind::Float(Unknown), vec![]),
                            }),
                        )],
                    ),
                    (
                        "pow",
                        vec![FunctionInterface(
                            (
                                vec![TypeKind::Float(Unknown), TypeKind::Float(Unknown)],
                                TypeKind::Float(Unknown),
                            ),
                            Box::new(move |_, params| match &params[..] {
                                [TypeKind::Float(Literal(base)), TypeKind::Float(Literal(exp))] => {
                                    (TypeKind::Float(Literal(base.powf(*exp))), vec![])
                                }
                                _ => (TypeKind::Float(Unknown), vec![]),
                            }),
                        )],
                    ),
                    (
                        "round",
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params| match &params[..] {
                                [TypeKind::Float(Literal(x))] => {
                                    (TypeKind::Float(Literal(f64::round(*x))), vec![])
                                }
                                _ => (TypeKind::Float(Unknown), vec![]),
                            }),
                        )],
                    ),
                    (
                        "sqrt",
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params| match &params[..] {
                                [TypeKind::Float(Literal(x))] => {
                                    (TypeKind::Float(Literal(f64::sqrt(*x))), vec![])
                                }
                                _ => (TypeKind::Float(Unknown), vec![]),
                            }),
                        )],
                    ),
                ]),
            ),
            (
                "timestamp",
                HashMap::from([
                    (
                        "date",
                        vec![FunctionInterface(
                            (
                                vec![
                                    TypeKind::Integer(Unknown),
                                    TypeKind::Integer(Unknown),
                                    TypeKind::Integer(Unknown),
                                ],
                                TypeKind::Timestamp,
                            ),
                            Box::new(move |node, params| match &params[..] {
                                [TypeKind::Integer(Literal(year)), TypeKind::Integer(Literal(month)), TypeKind::Integer(Literal(day))] => {
                                    (
                                        TypeKind::Timestamp,
                                        if let (Ok(year), Ok(month), Ok(day)) = (
                                            i32::try_from(*year),
                                            u32::try_from(*month),
                                            u32::try_from(*day),
                                        ) {
                                            if NaiveDate::from_ymd_opt(year, month, day).is_some() {
                                                vec![]
                                            } else {
                                                vec![TypeCheckResult {
                                                    reason: "invalid date".to_owned(),
                                                    at: node.get_span().into(),
                                                }]
                                            }
                                        } else {
                                            vec![TypeCheckResult {
                                                reason: "invalid date".to_owned(),
                                                at: node.get_span().into(),
                                            }]
                                        },
                                    )
                                }
                                _ => (TypeKind::Timestamp, vec![]),
                            }),
                        )],
                    ),
                    (
                        "value",
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Timestamp),
                            Box::new(move |_, _| (TypeKind::Timestamp, vec![])),
                        )],
                    ),
                ]),
            ),
        ]),
    )
}
