use std::collections::HashMap;

use crate::ast::{BinaryLiteral, UnaryLiteral};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeKind {
    Any,
    Null,
    Boolean,
    Bytes,
    Duration,
    Float,
    Integer,
    LatLng,
    List,
    Map,
    MapDiff,
    Path,
    Set,
    String,
    Timestamp,
    Request,
    Resource,
}

impl TypeKind {
    pub fn get_coercion_list(&self) -> Vec<TypeKind> {
        match *self {
            TypeKind::Integer => vec![TypeKind::Float],
            _ => vec![],
        }
    }

    pub fn is_type_coercion_to(&self, target: &Self) -> bool {
        self.get_coercion_list()
            .iter()
            .any(|candidate| candidate == target)
    }

    pub fn equal_to(&self, dst: &Self) -> bool {
        *self == *dst
            || self.is_type_coercion_to(dst)
            || *self == TypeKind::Any
            || *dst == TypeKind::Any
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionKind {
    Function(String),
    UnaryOp(UnaryLiteral),
    BinaryOp(BinaryLiteral),
    Subscript,
    SubscriptRange,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MemberKind {
    Member(String),
    AnyMember,
}

pub type FunctionInterface = (Vec<TypeKind>, TypeKind);

#[derive(Clone, Debug)]
pub struct Interface {
    pub functions: HashMap<FunctionKind, Vec<FunctionInterface>>,
    pub members: HashMap<MemberKind, TypeKind>,
}
