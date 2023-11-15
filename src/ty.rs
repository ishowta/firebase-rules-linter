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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionKind {
    Function(String),
    UnaryOp(UnaryLiteral),
    BinaryOp(BinaryLiteral),
    TernaryOp,
    InOp,
    Subscript,
    SubscriptRange,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MemberKind {
    Member(String),
    AnyMember,
}

pub type Function = (Vec<TypeKind>, TypeKind);

pub struct Interface {
    pub functions: HashMap<FunctionKind, Vec<Function>>,
    pub members: HashMap<MemberKind, TypeKind>,
}
