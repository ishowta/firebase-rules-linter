use std::collections::HashMap;

use crate::{
    ast::{BinaryLiteral, UnaryLiteral},
    ty::{FunctionKind, Interface, MemberKind, TypeKind},
};

#[derive(Debug, Clone)]
pub struct Interfaces {
    interfaces: HashMap<TypeKind, Interface>,
}

impl Interfaces {
    pub fn get_interface<'a>(&'a self, ty: &'a TypeKind) -> Vec<&Interface> {
        std::iter::once(ty)
            .chain(ty.get_coercion_list().iter())
            .flat_map(|ty| self.interfaces.get(&ty))
            .collect()
    }
}

pub fn get_interfaces<'a>() -> Interfaces {
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
                vec![(vec![TypeKind::String], TypeKind::List)],
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

    let list_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::BinaryOp(BinaryLiteral::Eq),
                vec![(vec![TypeKind::List], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Subscript,
                vec![(vec![TypeKind::Integer], TypeKind::Any)],
            ),
            (
                FunctionKind::SubscriptRange,
                vec![(vec![TypeKind::Integer, TypeKind::Integer], TypeKind::List)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::In),
                vec![(vec![TypeKind::Any], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("concat".to_owned()),
                vec![(vec![TypeKind::List], TypeKind::List)],
            ),
            (
                FunctionKind::Function("hasAll".to_owned()),
                vec![(vec![TypeKind::List], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("hasAny".to_owned()),
                vec![(vec![TypeKind::List], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("hasOnly".to_owned()),
                vec![(vec![TypeKind::List], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("join".to_owned()),
                vec![(vec![TypeKind::String], TypeKind::String)],
            ),
            (
                FunctionKind::Function("removeAll".to_owned()),
                vec![(vec![TypeKind::List], TypeKind::List)],
            ),
            (
                FunctionKind::Function("size".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("toSet".to_owned()),
                vec![(vec![], TypeKind::Set)],
            ),
        ]),
        members: HashMap::from([]),
    };

    let map_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::BinaryOp(BinaryLiteral::Eq),
                vec![(vec![TypeKind::Map], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Subscript,
                vec![(vec![TypeKind::Integer], TypeKind::Map)],
            ),
            (
                FunctionKind::SubscriptRange,
                vec![(vec![TypeKind::Integer, TypeKind::Integer], TypeKind::Map)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::In),
                vec![(vec![TypeKind::String], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("diff".to_owned()),
                vec![(vec![TypeKind::Map], TypeKind::MapDiff)],
            ),
            (
                FunctionKind::Function("get".to_owned()),
                vec![
                    (vec![TypeKind::String], TypeKind::Any),
                    (vec![TypeKind::List], TypeKind::Any),
                ],
            ),
            (
                FunctionKind::Function("keys".to_owned()),
                vec![(vec![], TypeKind::List)],
            ),
            (
                FunctionKind::Function("size".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("values".to_owned()),
                vec![(vec![], TypeKind::List)],
            ),
        ]),
        members: HashMap::from([(MemberKind::AnyMember, TypeKind::Map)]),
    };

    let mapdiff_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::Function("addedKeys".to_owned()),
                vec![(vec![], TypeKind::Set)],
            ),
            (
                FunctionKind::Function("affectedKeys".to_owned()),
                vec![(vec![], TypeKind::Set)],
            ),
            (
                FunctionKind::Function("changedKeys".to_owned()),
                vec![(vec![], TypeKind::Set)],
            ),
            (
                FunctionKind::Function("removedKeys".to_owned()),
                vec![(vec![], TypeKind::Set)],
            ),
            (
                FunctionKind::Function("unchangedKeys".to_owned()),
                vec![(vec![], TypeKind::Set)],
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
                vec![(vec![TypeKind::Map], TypeKind::Path)],
            ),
        ]),
        members: HashMap::from([(MemberKind::AnyMember, TypeKind::String)]),
    };

    let set_interface = Interface {
        functions: HashMap::from([
            (
                FunctionKind::BinaryOp(BinaryLiteral::Eq),
                vec![(vec![TypeKind::Set], TypeKind::Boolean)],
            ),
            (
                FunctionKind::BinaryOp(BinaryLiteral::In),
                vec![(vec![TypeKind::Any], TypeKind::Boolean)],
            ),
            (
                FunctionKind::Function("difference".to_owned()),
                vec![(vec![TypeKind::Set], TypeKind::Set)],
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
                vec![(vec![TypeKind::Set], TypeKind::Set)],
            ),
            (
                FunctionKind::Function("size".to_owned()),
                vec![(vec![], TypeKind::Integer)],
            ),
            (
                FunctionKind::Function("union".to_owned()),
                vec![(vec![TypeKind::Set], TypeKind::Set)],
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
            (MemberKind::Member("data".to_owned()), TypeKind::Map),
            (MemberKind::Member("id".to_owned()), TypeKind::String),
        ]),
    };

    let request_interface = Interface {
        functions: HashMap::from([(
            FunctionKind::Subscript,
            vec![(vec![TypeKind::String], TypeKind::Path)],
        )]),
        members: HashMap::from([
            (MemberKind::Member("auth".to_owned()), TypeKind::Map),
            (MemberKind::Member("method".to_owned()), TypeKind::String),
            (MemberKind::Member("path".to_owned()), TypeKind::Path),
            (MemberKind::Member("query".to_owned()), TypeKind::Map),
            (
                MemberKind::Member("resource".to_owned()),
                TypeKind::Resource,
            ),
            (MemberKind::Member("time".to_owned()), TypeKind::Timestamp),
        ]),
    };

    Interfaces {
        interfaces: HashMap::from([
            (TypeKind::Any, any_interface),
            (TypeKind::Null, null_interface),
            (TypeKind::Boolean, boolean_interface),
            (TypeKind::Bytes, bytes_interface),
            (TypeKind::Duration, duration_interface),
            (TypeKind::Float, float_interface),
            (TypeKind::Integer, integer_interface),
            (TypeKind::LatLng, latlng_interface),
            (TypeKind::List, list_interface),
            (TypeKind::Map, map_interface),
            (TypeKind::MapDiff, mapdiff_interface),
            (TypeKind::Path, path_interface),
            (TypeKind::Set, set_interface),
            (TypeKind::String, string_interface),
            (TypeKind::Timestamp, timestamp_interface),
            (TypeKind::Request, request_interface),
            (TypeKind::Resource, resource_interface),
        ]),
    }
}
