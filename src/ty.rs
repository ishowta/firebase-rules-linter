use std::{
    collections::HashMap,
    fmt::{write, Display},
};

use miette::NamedSource;

use crate::ast::{BinaryLiteral, UnaryLiteral};

#[derive(Debug, Clone)]
pub enum TypeKind {
    Any,
    Null,
    Boolean,
    Bytes,
    Duration,
    Float,
    Integer,
    LatLng,
    List(Box<TypeKind>),
    Map(Box<TypeKind>),
    MapDiff,
    Path,
    Set(Box<TypeKind>),
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

    pub fn equal_exactly(&self, dst: &Self) -> bool {
        match (self, dst) {
            (TypeKind::Any, _) => true,
            (_, TypeKind::Any) => true,
            (TypeKind::Null, TypeKind::Null) => true,
            (TypeKind::Boolean, TypeKind::Boolean) => true,
            (TypeKind::Bytes, TypeKind::Bytes) => true,
            (TypeKind::Duration, TypeKind::Duration) => true,
            (TypeKind::Float, TypeKind::Float) => true,
            (TypeKind::Integer, TypeKind::Integer) => true,
            (TypeKind::LatLng, TypeKind::LatLng) => true,
            (TypeKind::List(a), TypeKind::List(b)) => a.equal_exactly(b),
            (TypeKind::Map(a), TypeKind::Map(b)) => a.equal_exactly(b),
            (TypeKind::MapDiff, TypeKind::MapDiff) => true,
            (TypeKind::Path, TypeKind::Path) => true,
            (TypeKind::Set(a), TypeKind::Set(b)) => a.equal_exactly(b),
            (TypeKind::String, TypeKind::String) => true,
            (TypeKind::Timestamp, TypeKind::Timestamp) => true,
            (TypeKind::Request, TypeKind::Request) => true,
            (TypeKind::Resource, TypeKind::Resource) => true,
            _ => false,
        }
    }

    pub fn is_type_coercion_to(&self, target: &Self) -> bool {
        self.get_coercion_list()
            .iter()
            .any(|candidate| candidate.equal_exactly(target))
    }

    pub fn is_any(&self) -> bool {
        if let TypeKind::Any = self {
            true
        } else {
            false
        }
    }

    pub fn is_null(&self) -> bool {
        if let TypeKind::Null = self {
            true
        } else {
            false
        }
    }

    pub fn equal_to(&self, dst: &Self) -> bool {
        (match (self, dst) {
            (TypeKind::Any, _) => true,
            (_, TypeKind::Any) => true,
            (TypeKind::Null, TypeKind::Null) => true,
            (TypeKind::Boolean, TypeKind::Boolean) => true,
            (TypeKind::Bytes, TypeKind::Bytes) => true,
            (TypeKind::Duration, TypeKind::Duration) => true,
            (TypeKind::Float, TypeKind::Float) => true,
            (TypeKind::Integer, TypeKind::Integer) => true,
            (TypeKind::LatLng, TypeKind::LatLng) => true,
            (TypeKind::List(a), TypeKind::List(b)) => a.equal_to(b),
            (TypeKind::Map(a), TypeKind::Map(b)) => a.equal_to(b),
            (TypeKind::MapDiff, TypeKind::MapDiff) => true,
            (TypeKind::Path, TypeKind::Path) => true,
            (TypeKind::Set(a), TypeKind::Set(b)) => a.equal_to(b),
            (TypeKind::String, TypeKind::String) => true,
            (TypeKind::Timestamp, TypeKind::Timestamp) => true,
            (TypeKind::Request, TypeKind::Request) => true,
            (TypeKind::Resource, TypeKind::Resource) => true,
            _ => false,
        } || self.is_type_coercion_to(dst))
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

impl Display for FunctionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FunctionKind::Function(name) => write!(f, "{}()", name),
            FunctionKind::UnaryOp(op) => write!(f, "`{}`", op),
            FunctionKind::BinaryOp(op) => write!(f, "`{}`", op),
            FunctionKind::Subscript => write!(f, "`[]`"),
            FunctionKind::SubscriptRange => write!(f, "`[:]`"),
        }
    }
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
