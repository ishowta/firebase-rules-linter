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
