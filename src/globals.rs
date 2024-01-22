use std::collections::HashMap;

use chrono::NaiveDate;

use crate::{
    checker::TypeCheckResult,
    ty::{Flow, FunctionInterface, ListLiteral, MapLiteral, MayLiteral::*, Ty, TypeID, TypeKind},
};

pub fn get_globals() -> (
    Flow,
    (
        HashMap<&'static str, Ty>,
        HashMap<&'static str, Vec<FunctionInterface<'static>>>,
        HashMap<&'static str, HashMap<&'static str, Vec<FunctionInterface<'static>>>>,
    ),
    TypeID
) {
    let mut flow: Flow = HashMap::new();

    let resource_data_ty_id = TypeID::new();
    let resource_data_ty = Ty::Type(resource_data_ty_id.clone(), TypeKind::Map(Literal(MapLiteral { literals: HashMap::new(), default: None })));
    let resource_ty_id = TypeID::new();
    let resource_ty = Ty::Type(
        resource_ty_id.clone(),
        TypeKind::Map(Literal(MapLiteral {
            default: None,
            literals: HashMap::from([
                ("data".to_owned(), Ty::FlowType(resource_data_ty_id.clone(), false)),
                ("id".to_owned(), Ty::new(TypeKind::String(Unknown))),
                ("__name__".to_owned(), Ty::new(TypeKind::Path(Unknown))),
            ]),
        })),
    );
    let request_resource_data_ty_id = TypeID::new();
    let request_resource_data_ty = Ty::Type(resource_data_ty_id.clone(), TypeKind::Map(Literal(MapLiteral { literals: HashMap::new(), default: None })));
    let request_resource_ty_id = TypeID::new();
    let request_resource_ty = Ty::Type(
        request_resource_ty_id.clone(),
        TypeKind::Map(Literal(MapLiteral {
            default: None,
            literals: HashMap::from([
                ("data".to_owned(), Ty::FlowType(request_resource_data_ty_id.clone(), false)),
                ("id".to_owned(), Ty::new(TypeKind::String(Unknown))),
                ("__name__".to_owned(), Ty::new(TypeKind::Path(Unknown))),
            ]),
        })),
    );
    let request_ty_id = TypeID::new();
    let request_ty = Ty::Type(request_ty_id.clone(), TypeKind::Map(Literal(MapLiteral {
        default: None,
        literals: HashMap::from([
            (
                "auth".to_owned(),
                Ty::new(TypeKind::Map(Literal(MapLiteral {
                    default: None,
                    literals: HashMap::from([
                        ("uid".to_owned(), Ty::new(TypeKind::String(Unknown))),
                        (
                            "token".to_owned(),
                            Ty::new(TypeKind::Map(Literal(MapLiteral {
                                default: None,
                                literals: HashMap::from([
                                    ("email".to_owned(), Ty::new(TypeKind::String(Unknown))),
                                    (
                                        "email_verified".to_owned(),
                                        Ty::new(TypeKind::Boolean(Unknown)),
                                    ),
                                    (
                                        "phone_number".to_owned(),
                                        Ty::new(TypeKind::String(Unknown)),
                                    ),
                                    ("name".to_owned(), Ty::new(TypeKind::String(Unknown))),
                                    ("sub".to_owned(), Ty::new(TypeKind::String(Unknown))),
                                    (
                                        "firebase".to_owned(),
                                        Ty::new(TypeKind::Map(Literal(MapLiteral {
                                            default: None,
                                            literals: HashMap::from([
                                                (
                                                    "identities".to_owned(),
                                                    Ty::new(TypeKind::Map(Literal(MapLiteral {
                                                        default: None,
                                                        literals: HashMap::from([
                                                            (
                                                                "email".to_owned(),
                                                                Ty::new(TypeKind::List(Literal(
                                                                    ListLiteral::Single(Box::new(
                                                                        Ty::new(TypeKind::String(Unknown)),
                                                                    )),
                                                                ))),
                                                            ),
                                                            (
                                                                "phone".to_owned(),
                                                                Ty::new(TypeKind::List(Literal(
                                                                    ListLiteral::Single(Box::new(
                                                                        Ty::new(TypeKind::String(Unknown)),
                                                                    )),
                                                                ))),
                                                            ),
                                                            (
                                                                "google.com".to_owned(),
                                                                Ty::new(TypeKind::List(Literal(
                                                                    ListLiteral::Single(Box::new(
                                                                        Ty::new(TypeKind::String(Unknown)),
                                                                    )),
                                                                ))),
                                                            ),
                                                            (
                                                                "facebook.com".to_owned(),
                                                                Ty::new(TypeKind::List(Literal(
                                                                    ListLiteral::Single(Box::new(
                                                                        Ty::new(TypeKind::String(Unknown)),
                                                                    )),
                                                                ))),
                                                            ),
                                                            (
                                                                "github.com".to_owned(),
                                                                Ty::new(TypeKind::List(Literal(
                                                                    ListLiteral::Single(Box::new(
                                                                        Ty::new(TypeKind::String(Unknown)),
                                                                    )),
                                                                ))),
                                                            ),
                                                            (
                                                                "twitter.com".to_owned(),
                                                                Ty::new(TypeKind::List(Literal(
                                                                    ListLiteral::Single(Box::new(
                                                                        Ty::new(TypeKind::String(Unknown)),
                                                                    )),
                                                                ))),
                                                            ),
                                                        ]),
                                                    }))),
                                                ),
                                                (
                                                    "sign_in_provider".to_owned(),
                                                    Ty::new(TypeKind::String(Unknown)),
                                                ),
                                                (
                                                    "tenant".to_owned(),
                                                    Ty::new(TypeKind::String(Unknown)),
                                                ),
                                            ]),
                                        }))),
                                    ),
                                ]),
                            }))),
                        ),
                    ]),
                }))),
            ),
            ("method".to_owned(), Ty::new(TypeKind::String(Unknown))),
            ("path".to_owned(), Ty::new(TypeKind::Path(Unknown))),
            (
                "query".to_owned(),
                Ty::new(TypeKind::Map(Literal(MapLiteral {
                    default: None,
                    literals: HashMap::from([
                        ("limit".to_owned(), Ty::new(TypeKind::Integer(Unknown))),
                        ("offset".to_owned(), Ty::new(TypeKind::Any)),
                        ("orderBy".to_owned(), Ty::new(TypeKind::String(Unknown))),
                    ]),
                }))),
            ),
            ("resource".to_owned(), Ty::FlowType(request_resource_ty_id.clone(),false)),
            ("time".to_owned(), Ty::new(TypeKind::Timestamp)),
        ]),
    })));
    flow.insert(resource_data_ty_id.clone(), resource_data_ty);
    flow.insert(resource_ty_id.clone(), resource_ty);
    flow.insert(request_resource_data_ty_id.clone(), request_resource_data_ty);
    flow.insert(request_resource_ty_id.clone(), request_resource_ty);
    flow.insert(request_ty_id.clone(), request_ty);

    let unknown_resource_ty = TypeKind::Map(Literal(MapLiteral {
        default: None,
        literals: HashMap::from([
            ("data".to_owned(), Ty::new(TypeKind::Map(Unknown))),
            ("id".to_owned(), Ty::new(TypeKind::String(Unknown))),
            ("__name__".to_owned(), Ty::new(TypeKind::Path(Unknown))),
        ]),
    }));
    let result = (
        HashMap::from([
            ("request", Ty::FlowType(request_ty_id.clone(), false)),
            ("resource", Ty::FlowType(resource_ty_id.clone(), false)),
        ]),
        HashMap::from([
            (
                "debug",
                vec![FunctionInterface(
                    (vec![TypeKind::Any], TypeKind::Any),
                    Box::new(move |_, params, _,_| match &params[..] {
                        // TODO
                        [ty] => (Ty::new((**ty).clone()), vec![]),
                        _ => (Ty::new(TypeKind::Any), vec![]),
                    }),
                )],
            ),
            (
                "exists",
                vec![FunctionInterface(
                    (vec![TypeKind::Path(Unknown)], TypeKind::Boolean(Unknown)),
                    Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                )],
            ),
            (
                "existsAfter",
                vec![FunctionInterface(
                    (vec![TypeKind::Path(Unknown)], TypeKind::Boolean(Unknown)),
                    Box::new(move |_, _, _,_| (Ty::new(TypeKind::Boolean(Unknown)), vec![])),
                )],
            ),
            (
                "get",
                vec![FunctionInterface(
                    (vec![TypeKind::Path(Unknown)], unknown_resource_ty.clone()),
                    {
                        let unknown_resource_ty = unknown_resource_ty.clone();
                        Box::new(move |_, _, _,_| (Ty::new(unknown_resource_ty.clone()), vec![]))
                    },
                )],
            ),
            (
                "getAfter",
                vec![FunctionInterface(
                    (vec![TypeKind::Path(Unknown)], unknown_resource_ty.clone()),
                    {
                        let unknown_resource_ty = unknown_resource_ty.clone();
                        Box::new(move |_, _, _,_| (Ty::new(unknown_resource_ty.clone()), vec![]))
                    },
                )],
            ),
            (
                "float",
                vec![
                    FunctionInterface(
                        (vec![TypeKind::String(Unknown)], TypeKind::Float(Unknown)),
                        Box::new(move |_, _, _,_| (Ty::new(TypeKind::Float(Unknown)), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Integer(Unknown)], TypeKind::Float(Unknown)),
                        Box::new(move |_, _, _,_| (Ty::new(TypeKind::Float(Unknown)), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                        Box::new(move |_, _, _,_| (Ty::new(TypeKind::Float(Unknown)), vec![])),
                    ),
                ],
            ),
            (
                "int",
                vec![
                    FunctionInterface(
                        (vec![TypeKind::String(Unknown)], TypeKind::Integer(Unknown)),
                        Box::new(move |_, _, _,_| (Ty::new(TypeKind::Integer(Unknown)), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Integer(Unknown)], TypeKind::Integer(Unknown)),
                        Box::new(move |_, _, _,_| (Ty::new(TypeKind::Integer(Unknown)), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Float(Unknown)], TypeKind::Integer(Unknown)),
                        Box::new(move |_, _, _,_| (Ty::new(TypeKind::Integer(Unknown)), vec![])),
                    ),
                ],
            ),
            (
                "string",
                vec![
                    FunctionInterface(
                        (vec![TypeKind::Boolean(Unknown)], TypeKind::String(Unknown)),
                        Box::new(move |_, _, _,_| (Ty::new(TypeKind::String(Unknown)), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Integer(Unknown)], TypeKind::String(Unknown)),
                        Box::new(move |_, _, _,_| (Ty::new(TypeKind::String(Unknown)), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Float(Unknown)], TypeKind::String(Unknown)),
                        Box::new(move |_, _, _,_| (Ty::new(TypeKind::String(Unknown)), vec![])),
                    ),
                    FunctionInterface(
                        (
                            vec![TypeKind::Null],
                            TypeKind::String(Literal("null".to_owned())),
                        ),
                        Box::new(move |_, _, _,_| {
                            (
                                Ty::new(TypeKind::String(Literal("null".to_owned()))),
                                vec![],
                            )
                        }),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::String(Unknown)], TypeKind::String(Unknown)),
                        Box::new(move |_, _, _,_| (Ty::new(TypeKind::String(Unknown)), vec![])),
                    ),
                    FunctionInterface(
                        (vec![TypeKind::Path(Unknown)], TypeKind::String(Unknown)),
                        Box::new(move |_, params, _,_| match &params[..] {
                            [TypeKind::Path(Literal(str))] => {
                                (Ty::new(TypeKind::String(Literal(str.clone()))), vec![])
                            }
                            _ => (Ty::new(TypeKind::String(Unknown)), vec![]),
                        }),
                    ),
                    FunctionInterface(
                        (
                            vec![TypeKind::PathTemplateBound(Unknown)],
                            TypeKind::String(Unknown),
                        ),
                        Box::new(move |_, _, _,_| (Ty::new(TypeKind::String(Unknown)), vec![])),
                    ),
                ],
            ),
            (
                "path",
                vec![FunctionInterface(
                    (vec![TypeKind::String(Unknown)], TypeKind::Path(Unknown)),
                    Box::new(move |_, params, _,_| match &params[..] {
                        [TypeKind::String(Literal(str))] => {
                            (Ty::new(TypeKind::Path(Literal(str.clone()))), vec![])
                        }
                        _ => (Ty::new(TypeKind::Path(Unknown)), vec![]),
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
                            Box::new(move |_, _, _,_| (Ty::new(TypeKind::Duration), vec![])),
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
                            Box::new(move |_, _, _,_| (Ty::new(TypeKind::Duration), vec![])),
                        )],
                    ),
                    (
                        "value",
                        vec![FunctionInterface(
                            (
                                vec![TypeKind::Integer(Unknown), TypeKind::String(Unknown)],
                                TypeKind::Duration,
                            ),
                            Box::new(move |_, params, _,_| match &params[..] {
                                [TypeKind::String(Literal(str))]
                                    if ["w", "d", "h", "m", "s", "ms", "ns"]
                                        .contains(&(str as &str)) =>
                                {
                                    (Ty::new(TypeKind::Duration), vec![])
                                }
                                _ => (Ty::new(TypeKind::Duration), vec![]),
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
                                Box::new(move |_, _, _,_| {
                                    (Ty::new(TypeKind::Bytes(Unknown)), vec![])
                                }),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::String(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _, _,_| {
                                    (Ty::new(TypeKind::Bytes(Unknown)), vec![])
                                }),
                            ),
                        ],
                    ),
                    (
                        "crc32c",
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::Bytes(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _, _,_| {
                                    (Ty::new(TypeKind::Bytes(Unknown)), vec![])
                                }),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::String(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _, _,_| {
                                    (Ty::new(TypeKind::Bytes(Unknown)), vec![])
                                }),
                            ),
                        ],
                    ),
                    (
                        "md5",
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::Bytes(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _, _,_| {
                                    (Ty::new(TypeKind::Bytes(Unknown)), vec![])
                                }),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::String(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _, _,_| {
                                    (Ty::new(TypeKind::Bytes(Unknown)), vec![])
                                }),
                            ),
                        ],
                    ),
                    (
                        "sha256",
                        vec![
                            FunctionInterface(
                                (vec![TypeKind::Bytes(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _, _,_| {
                                    (Ty::new(TypeKind::Bytes(Unknown)), vec![])
                                }),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::String(Unknown)], TypeKind::Bytes(Unknown)),
                                Box::new(move |_, _, _,_| {
                                    (Ty::new(TypeKind::Bytes(Unknown)), vec![])
                                }),
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
                        Box::new(move |_, _, _,_| (Ty::new(TypeKind::LatLng), vec![])),
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
                                Box::new(move |_, params, _,_| match &params[..] {
                                    [TypeKind::Integer(Literal(x))] => {
                                        (Ty::new(TypeKind::Integer(Literal(-x))), vec![])
                                    }
                                    _ => (Ty::new(TypeKind::Integer(Unknown)), vec![]),
                                }),
                            ),
                            FunctionInterface(
                                (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                                Box::new(move |_, params, _,_| match &params[..] {
                                    [TypeKind::Float(Literal(x))] => {
                                        (Ty::new(TypeKind::Float(Literal(-x))), vec![])
                                    }
                                    _ => (Ty::new(TypeKind::Float(Unknown)), vec![]),
                                }),
                            ),
                        ],
                    ),
                    (
                        "ceil",
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params, _,_| match &params[..] {
                                [TypeKind::Float(Literal(x))] => {
                                    (Ty::new(TypeKind::Float(Literal(f64::ceil(*x)))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Float(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        "floor",
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params, _,_| match &params[..] {
                                [TypeKind::Float(Literal(x))] => {
                                    (Ty::new(TypeKind::Float(Literal(f64::floor(*x)))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Float(Unknown)), vec![]),
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
                            Box::new(move |_, params, _,_| match &params[..] {
                                [TypeKind::Float(Literal(base)), TypeKind::Float(Literal(exp))] => {
                                    (Ty::new(TypeKind::Float(Literal(base.powf(*exp)))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Float(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        "round",
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params, _,_| match &params[..] {
                                [TypeKind::Float(Literal(x))] => {
                                    (Ty::new(TypeKind::Float(Literal(f64::round(*x)))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Float(Unknown)), vec![]),
                            }),
                        )],
                    ),
                    (
                        "sqrt",
                        vec![FunctionInterface(
                            (vec![TypeKind::Float(Unknown)], TypeKind::Float(Unknown)),
                            Box::new(move |_, params, _,_| match &params[..] {
                                [TypeKind::Float(Literal(x))] => {
                                    (Ty::new(TypeKind::Float(Literal(f64::sqrt(*x)))), vec![])
                                }
                                _ => (Ty::new(TypeKind::Float(Unknown)), vec![]),
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
                            Box::new(move |node, params, _, _| match &params[..] {
                                [TypeKind::Integer(Literal(year)), TypeKind::Integer(Literal(month)), TypeKind::Integer(Literal(day))] => {
                                    (
                                        Ty::new(TypeKind::Timestamp),
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
                                _ => (Ty::new(TypeKind::Timestamp), vec![]),
                            }),
                        )],
                    ),
                    (
                        "value",
                        vec![FunctionInterface(
                            (vec![TypeKind::Integer(Unknown)], TypeKind::Timestamp),
                            Box::new(move |_, _, _,_| (Ty::new(TypeKind::Timestamp), vec![])),
                        )],
                    ),
                ]),
            ),
        ]),
    );
    (flow, result, request_resource_data_ty_id)
}
