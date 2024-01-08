use std::collections::HashMap;

use crate::{
    ast::{BinaryLiteral, UnaryLiteral},
    ty::{FunctionKind, Interface, MemberKind, TypeKind},
};

pub struct Interfaces {
    get_exactly_interfaces: Box<dyn Fn(TypeKind) -> Interface>,
}

impl<'a> std::fmt::Debug for Interfaces {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Interfaces")
            .field("get_interfaces", &"<Fn>")
            .finish()
    }
}

impl Interfaces {
    pub fn get_interface(&self, ty: &TypeKind) -> Vec<Interface> {
        std::iter::once(ty)
            .chain(ty.get_coercion_list().iter())
            .map(|ty| (self.get_exactly_interfaces)(ty.clone()))
            .collect()
    }
}

pub fn get_interfaces() -> Interfaces {
    let any_interface = Interface {
        functions: HashMap::from([]),
        members: HashMap::from([]),
    };

    let null_interface = Interface {
        functions: HashMap::from([]),
        members: HashMap::from([]),
    };

    let boolean_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::BinaryOp(BinaryLiteral::LogicalAnd),
                vec![(vec![TypeKind::Boolean], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::LogicalOr),
                vec![(vec![TypeKind::Boolean], TypeKind::Boolean)],
            ),
            (
                FunctionKind::UnaryOp(UnaryLiteral::Not),
                vec![(vec![], TypeKind::Boolean)],
            ),
        ]),
        members: HashMap::from([]),
    };

    let float_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::BinaryOp(BinaryLiteral::Eq),
                vec![(vec![TypeKind::Float], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::NotEq),
                vec![(vec![TypeKind::Float], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Gt),
                vec![(vec![TypeKind::Float], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Gte),
                vec![(vec![TypeKind::Float], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Lt),
                vec![(vec![TypeKind::Float], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Lte),
                vec![(vec![TypeKind::Float], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Add),
                vec![(vec![TypeKind::Float], TypeKind::Float)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Sub),
                vec![(vec![TypeKind::Float], TypeKind::Float)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Div),
                vec![(vec![TypeKind::Float], TypeKind::Float)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Mul),
                vec![(vec![TypeKind::Float], TypeKind::Float)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Mul),
                vec![(vec![TypeKind::Float], TypeKind::Float)],
            ),
            (
                FunctionKind::UnaryOp(UnaryLiteral::Minus),
                vec![(vec![], TypeKind::Float)],
            ),
        ]),
        members: HashMap::from([]),
    };

    let integer_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::BinaryOp(BinaryLiteral::Eq),
                vec![(vec![TypeKind::Integer], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::NotEq),
                vec![(vec![TypeKind::Integer], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Gt),
                vec![(vec![TypeKind::Integer], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Gte),
                vec![(vec![TypeKind::Integer], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Lt),
                vec![(vec![TypeKind::Integer], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Lte),
                vec![(vec![TypeKind::Integer], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Add),
                vec![(vec![TypeKind::Integer], TypeKind::Integer)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Sub),
                vec![(vec![TypeKind::Integer], TypeKind::Integer)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Div),
                vec![(vec![TypeKind::Integer], TypeKind::Integer)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Mul),
                vec![(vec![TypeKind::Integer], TypeKind::Integer)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Mul),
                vec![(vec![TypeKind::Integer], TypeKind::Integer)],
            ),
            (
                FunctionKind::UnaryOp(UnaryLiteral::Minus),
                vec![(vec![], TypeKind::Integer)],
            ),
        ]),
        members: HashMap::from([]),
    };

    let string_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::BinaryOp(BinaryLiteral::Eq),
                vec![(vec![TypeKind::String], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::NotEq),
                vec![(vec![TypeKind::String], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Gt),
                vec![(vec![TypeKind::String], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Gte),
                vec![(vec![TypeKind::String], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Lt),
                vec![(vec![TypeKind::String], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Lte),
                vec![(vec![TypeKind::String], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::Add),
                vec![(vec![TypeKind::String], TypeKind::String)],
            ),
            (
                FunctionKind::Subscript,
                vec![(vec![TypeKind::Integer], TypeKind::String)],
            ),
            (
                FunctionKind::SubscriptRange,
                vec![(vec![TypeKind::Integer, TypeKind::Integer], TypeKind::String)],
            ),
            (
                FunctionKind::Function("lower".to_owned()),
                vec![(vec![], TypeKind::String)],
            ),
            (
                FunctionKind::Function("matches".to_owned()),
                vec![(vec![TypeKind::String], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("replace".to_owned()),
                vec![(vec![TypeKind::String, TypeKind::String], TypeKind::String)],
            ),
            (
                FunctionKind::Function("size".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("split".to_owned()),
                vec![(
                    vec![TypeKind::String],
                    TypeKind::List(Box::new(TypeKind::String)),
                )],
            ),
            (
                FunctionKind::Function("toUtf8".to_owned()),
                vec![(vec![], TypeKind::Bytes)],
            ),
            (
                FunctionKind::Function("trim".to_owned()),
                vec![(vec![], TypeKind::String)],
            ),
            (
                FunctionKind::Function("upper".to_owned()),
                vec![(vec![], TypeKind::String)],
            ),
        ]),
        members: HashMap::from([]),
    };

    let list_interface = |ty: &TypeKind| Interface {
        functions: HashMap::from([
            (
                FunctionKind::BinaryOp(BinaryLiteral::Eq),
                vec![(
                    vec![TypeKind::List(Box::new(ty.clone()))],
                    TypeKind::Boolean,
                )],
            ),
            (
                FunctionKind::Subscript,
                vec![(vec![TypeKind::Integer], TypeKind::Any)],
            ),
            (
                FunctionKind::SubscriptRange,
                vec![(
                    vec![TypeKind::Integer, TypeKind::Integer],
                    TypeKind::List(Box::new(ty.clone())),
                )],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::In),
                vec![(vec![ty.clone()], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("concat".to_owned()),
                vec![
                    (
                        vec![TypeKind::List(Box::new(ty.clone()))],
                        TypeKind::List(Box::new(ty.clone())),
                    ),
                    (
                        vec![TypeKind::List(Box::new(TypeKind::Any))],
                        TypeKind::List(Box::new(TypeKind::Any)),
                    ),
                ],
            ),
            (
                FunctionKind::Function("hasAll".to_owned()),
                vec![(
                    vec![TypeKind::List(Box::new(ty.clone()))],
                    TypeKind::Boolean,
                )],
            ),
            (
                FunctionKind::Function("hasAny".to_owned()),
                vec![(
                    vec![TypeKind::List(Box::new(ty.clone()))],
                    TypeKind::Boolean,
                )],
            ),
            (
                FunctionKind::Function("hasOnly".to_owned()),
                vec![(
                    vec![TypeKind::List(Box::new(ty.clone()))],
                    TypeKind::Boolean,
                )],
            ),
            (
                FunctionKind::Function("join".to_owned()),
                vec![(vec![TypeKind::String], TypeKind::String)],
            ),
            (
                FunctionKind::Function("removeAll".to_owned()),
                vec![(
                    vec![TypeKind::List(Box::new(ty.clone()))],
                    TypeKind::List(Box::new(ty.clone())),
                )],
            ),
            (
                FunctionKind::Function("size".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("toSet".to_owned()),
                vec![(vec![], TypeKind::Set(Box::new(ty.clone())))],
            ),
        ]),
        members: HashMap::from([]),
    };

    let map_interface = |ty: &TypeKind| Interface {
        functions: HashMap::from([
            (
                FunctionKind::BinaryOp(BinaryLiteral::Eq),
                vec![(vec![TypeKind::Map(Box::new(ty.clone()))], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Subscript,
                vec![(vec![TypeKind::Integer], TypeKind::Map(Box::new(ty.clone())))],
            ),
            (
                FunctionKind::SubscriptRange,
                vec![(
                    vec![TypeKind::Integer, TypeKind::Integer],
                    TypeKind::Map(Box::new(ty.clone())),
                )],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::In),
                vec![(vec![TypeKind::String], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("diff".to_owned()),
                vec![(vec![TypeKind::Map(Box::new(ty.clone()))], TypeKind::MapDiff)],
            ),
            (
                FunctionKind::Function("get".to_owned()),
                vec![
                    (vec![TypeKind::String], TypeKind::Any),
                    (vec![TypeKind::List(Box::new(ty.clone()))], TypeKind::Any),
                ],
            ),
            (
                FunctionKind::Function("keys".to_owned()),
                vec![(vec![], TypeKind::List(Box::new(TypeKind::String)))],
            ),
            (
                FunctionKind::Function("size".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("values".to_owned()),
                vec![(vec![], TypeKind::List(Box::new(ty.clone())))],
            ),
        ]),
        members: HashMap::from([(
            MemberKind::AnyMember,
            TypeKind::Map(Box::new(TypeKind::Any)),
        )]),
    };

    let mapdiff_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::Function("addedKeys".to_owned()),
                vec![(vec![], TypeKind::Set(Box::new(TypeKind::String)))],
            ),
            (
                FunctionKind::Function("affectedKeys".to_owned()),
                vec![(vec![], TypeKind::Set(Box::new(TypeKind::String)))],
            ),
            (
                FunctionKind::Function("changedKeys".to_owned()),
                vec![(vec![], TypeKind::Set(Box::new(TypeKind::String)))],
            ),
            (
                FunctionKind::Function("removedKeys".to_owned()),
                vec![(vec![], TypeKind::Set(Box::new(TypeKind::String)))],
            ),
            (
                FunctionKind::Function("unchangedKeys".to_owned()),
                vec![(vec![], TypeKind::Set(Box::new(TypeKind::String)))],
            ),
        ]),
        members: HashMap::from([]),
    };

    let path_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::BinaryOp(BinaryLiteral::Eq),
                vec![(vec![TypeKind::Path], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Subscript,
                vec![(vec![TypeKind::String, TypeKind::Integer], TypeKind::String)],
            ),
            (
                FunctionKind::Function("bind".to_owned()),
                vec![(
                    vec![TypeKind::Map(Box::new(TypeKind::String))],
                    TypeKind::Path,
                )],
            ),
        ]),
        members: HashMap::from([(MemberKind::AnyMember, TypeKind::String)]),
    };

    let set_interface = |ty: &TypeKind| Interface {
        functions: HashMap::from([
            (
                FunctionKind::BinaryOp(BinaryLiteral::Eq),
                vec![(vec![TypeKind::Set(Box::new(ty.clone()))], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::In),
                vec![(vec![ty.clone()], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("difference".to_owned()),
                vec![(
                    vec![TypeKind::Set(Box::new(ty.clone()))],
                    TypeKind::Set(Box::new(ty.clone())),
                )],
            ),
            (
                FunctionKind::Function("hasAll".to_owned()),
                vec![(vec![], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("hasAny".to_owned()),
                vec![(vec![], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("hasOnly".to_owned()),
                vec![(vec![], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("intersection".to_owned()),
                vec![(
                    vec![TypeKind::Set(Box::new(ty.clone()))],
                    TypeKind::Set(Box::new(ty.clone())),
                )],
            ),
            (
                FunctionKind::Function("size".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("union".to_owned()),
                vec![
                    (
                        vec![TypeKind::Set(Box::new(ty.clone()))],
                        TypeKind::Set(Box::new(ty.clone())),
                    ),
                    (
                        vec![TypeKind::Set(Box::new(TypeKind::Any))],
                        TypeKind::Set(Box::new(TypeKind::Any)),
                    ),
                ],
            ),
        ]),
        members: HashMap::from([(MemberKind::AnyMember, TypeKind::String)]),
    };

    let bytes_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::Function("size".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("toBase64".to_owned()),
                vec![(vec![], TypeKind::String)],
            ),
            (
                FunctionKind::Function("toHexString".to_owned()),
                vec![(vec![], TypeKind::String)],
            ),
        ]),
        members: HashMap::from([]),
    };

    let duration_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::Function("nanos".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("seconds".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
        ]),
        members: HashMap::from([]),
    };

    let latlng_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::Function("distance".to_owned()),
                vec![(vec![TypeKind::LatLng], TypeKind::Float)],
            ),
            (
                FunctionKind::Function("latitude".to_owned()),
                vec![(vec![], TypeKind::Float)],
            ),
            (
                FunctionKind::Function("longitude".to_owned()),
                vec![(vec![], TypeKind::Float)],
            ),
        ]),
        members: HashMap::from([]),
    };

    let timestamp_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::Function("date".to_owned()),
                vec![(vec![], TypeKind::Timestamp)],
            ),
            (
                FunctionKind::Function("day".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("dayOfWeek".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("dayOfYear".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("hours".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("minutes".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("month".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("nanos".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("seconds".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("time".to_owned()),
                vec![(vec![], TypeKind::Duration)],
            ),
            (
                FunctionKind::Function("toMillis".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("year".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
        ]),
        members: HashMap::from([]),
    };

    let resource_interface = Interface {
        functions: HashMap::from([(
            FunctionKind::Subscript,
            vec![(vec![TypeKind::String], TypeKind::Path)],
        )]),
        members: HashMap::from([
            (
                MemberKind::Member("data".to_owned()),
                TypeKind::Map(Box::new(TypeKind::Any)),
            ),
            (MemberKind::Member("id".to_owned()), TypeKind::String),
        ]),
    };

    let request_interface = Interface {
        functions: HashMap::from([(
            FunctionKind::Subscript,
            vec![(vec![TypeKind::String], TypeKind::Path)],
        )]),
        members: HashMap::from([
            (
                MemberKind::Member("auth".to_owned()),
                TypeKind::Map(Box::new(TypeKind::Any)),
            ),
            (MemberKind::Member("method".to_owned()), TypeKind::String),
            (MemberKind::Member("path".to_owned()), TypeKind::Path),
            (
                MemberKind::Member("query".to_owned()),
                TypeKind::Map(Box::new(TypeKind::Any)),
            ),
            (
                MemberKind::Member("resource".to_owned()),
                TypeKind::Resource,
            ),
            (MemberKind::Member("time".to_owned()), TypeKind::Timestamp),
        ]),
    };

    Interfaces {
        get_exactly_interfaces: Box::new(move |ty: TypeKind| match ty {
            TypeKind::Any => any_interface.clone(),
            TypeKind::Null => null_interface.clone(),
            TypeKind::Boolean => boolean_interface.clone(),
            TypeKind::Bytes => bytes_interface.clone(),
            TypeKind::Duration => duration_interface.clone(),
            TypeKind::Float => float_interface.clone(),
            TypeKind::Integer => integer_interface.clone(),
            TypeKind::LatLng => latlng_interface.clone(),
            TypeKind::List(t) => list_interface(&t),
            TypeKind::Map(t) => map_interface(&t),
            TypeKind::MapDiff => mapdiff_interface.clone(),
            TypeKind::Path => path_interface.clone(),
            TypeKind::Set(t) => set_interface(&t),
            TypeKind::String => string_interface.clone(),
            TypeKind::Timestamp => timestamp_interface.clone(),
            TypeKind::Request => request_interface.clone(),
            TypeKind::Resource => resource_interface.clone(),
        }),
    }
}
