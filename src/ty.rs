use std::{collections::HashMap, fmt::Display, hash::Hash};

use crate::{
    ast::{BinaryLiteral, Node, UnaryLiteral},
    checker::TypeCheckResult,
};

#[derive(Debug, Clone)]
pub enum TypeKind {
    Any,
    Null,
    Boolean(MayLiteral<bool>),
    Bytes(MayLiteral<Vec<u8>>),
    Duration,
    Float(MayLiteral<f64>),
    Integer(MayLiteral<i64>),
    LatLng,
    List(Box<TypeKind>),
    Map(MayLiteral<MapLiteral>),
    MapDiff((MayLiteral<MapLiteral>, MayLiteral<MapLiteral>)),
    Path(MayLiteral<String>),
    PathTemplateUnBound(MayLiteral<Vec<String>>),
    PathTemplateBound(MayLiteral<Vec<String>>),
    Set(Box<TypeKind>),
    String(MayLiteral<String>),
    Timestamp,
    Request,
    Resource,
}

#[derive(Debug, Clone)]
pub struct MapLiteral {
    pub literals: HashMap<String, TypeKind>,
    pub default: Option<Box<TypeKind>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MayLiteral<T> {
    Unknown,
    Literal(T),
}

impl<T: PartialEq> MayLiteral<T> {
    fn can_be(&self, other: &Self) -> bool {
        match (self, other) {
            (MayLiteral::Unknown, MayLiteral::Unknown) => true,
            (MayLiteral::Unknown, MayLiteral::Literal(_)) => false,
            (MayLiteral::Literal(_), MayLiteral::Unknown) => true,
            (MayLiteral::Literal(left), MayLiteral::Literal(right)) => left == right,
        }
    }
}

impl<T: Copy> Copy for MayLiteral<T> {}

impl<T> MayLiteral<T> {
    fn can_be_by<F>(&self, other: &Self, f: F) -> Option<bool>
    where
        F: FnOnce(&T, &T) -> Option<bool>,
    {
        match (self, other) {
            (MayLiteral::Unknown, MayLiteral::Unknown) => Some(true),
            (MayLiteral::Unknown, MayLiteral::Literal(_)) => Some(false),
            (MayLiteral::Literal(_), MayLiteral::Unknown) => Some(true),
            (MayLiteral::Literal(left), MayLiteral::Literal(right)) => f(left, right),
        }
    }

    pub fn map<U, F>(self, f: F) -> MayLiteral<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            MayLiteral::Literal(x) => MayLiteral::Literal(f(x)),
            MayLiteral::Unknown => MayLiteral::Unknown,
        }
    }

    pub fn to_option(&self) -> Option<&T> {
        match self {
            MayLiteral::Literal(x) => Some(x),
            MayLiteral::Unknown => None,
        }
    }
}

impl TypeKind {
    pub fn get_coercion_list(&self) -> Vec<TypeKind> {
        match self {
            TypeKind::Integer(may_literal) => {
                vec![TypeKind::Float(may_literal.map(|i| i as f64))]
            }
            _ => vec![],
        }
    }

    pub fn is_type_coercion_to(&self, target: &Self) -> Option<bool> {
        let coercion_result: Option<Vec<bool>> = self
            .get_coercion_list()
            .iter()
            .map(|candidate| candidate.can_be(target))
            .collect();
        coercion_result.map(|result| result.iter().find(|b| **b).is_some())
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

    pub fn make_bool_ty(from: Option<bool>) -> TypeKind {
        match from {
            None => TypeKind::Boolean(MayLiteral::Unknown),
            Some(true) => TypeKind::Boolean(MayLiteral::Literal(true)),
            Some(false) => TypeKind::Boolean(MayLiteral::Literal(false)),
        }
    }

    /// subtyping
    ///
    /// return None if Any
    pub fn can_be(&self, other: &Self) -> Option<bool> {
        (match (self, other) {
            (TypeKind::Any, _) => None,
            (_, TypeKind::Any) => None,
            (TypeKind::Null, TypeKind::Null) => Some(true),
            (TypeKind::Boolean(left), TypeKind::Boolean(right)) => Some(left.can_be(right)),
            (TypeKind::Bytes(left), TypeKind::Bytes(right)) => Some(left.can_be(right)),
            (TypeKind::Duration, TypeKind::Duration) => Some(true),
            (TypeKind::Float(left), TypeKind::Float(right)) => Some(left.can_be(right)),
            (TypeKind::Integer(left), TypeKind::Integer(right)) => Some(left.can_be(right)),
            (TypeKind::LatLng, TypeKind::LatLng) => Some(true),
            (TypeKind::List(left), TypeKind::List(right)) => left.can_be(right),
            (TypeKind::Map(left), TypeKind::Map(right)) => left.can_be_by(right, |left, right| {
                right
                    .literals
                    .iter()
                    .map(|(right_key, right_value)| {
                        if let Some(left_value) = left.literals.get(right_key) {
                            left_value.can_be(right_value)
                        } else {
                            Some(false)
                        }
                    })
                    .collect::<Option<Vec<bool>>>()
                    .map(|res| res.iter().all(|b| *b))
                    .and_then(|prev| {
                        if prev == false {
                            Some(false)
                        } else {
                            match &right.default {
                                None => Some(true),
                                Some(right_default_ty) => (if let Some(left_default_ty) =
                                    &left.default
                                {
                                    left_default_ty.can_be(&right_default_ty)
                                } else {
                                    Some(false)
                                })
                                .and_then(|prev| {
                                    if prev == false {
                                        Some(false)
                                    } else {
                                        left.literals
                                            .iter()
                                            .filter(|(key, _)| !right.literals.contains_key(*key))
                                            .map(|(_, value)| value.can_be(&right_default_ty))
                                            .collect::<Option<Vec<bool>>>()
                                            .map(|res| res.iter().all(|b| *b))
                                    }
                                }),
                            }
                        }
                    })
            }),
            (TypeKind::MapDiff(left), TypeKind::MapDiff(right)) => left
                .0
                .can_be_by(&right.0, |left, right| {
                    TypeKind::Map(MayLiteral::Literal(left.clone()))
                        .can_be(&TypeKind::Map(MayLiteral::Literal(right.clone())))
                })
                .and_then(|prev| {
                    if prev == false {
                        Some(false)
                    } else {
                        left.1.can_be_by(&right.1, |left, right| {
                            TypeKind::Map(MayLiteral::Literal(left.clone()))
                                .can_be(&TypeKind::Map(MayLiteral::Literal(right.clone())))
                        })
                    }
                }),
            (TypeKind::Path(left), TypeKind::Path(right)) => Some(left.can_be(right)),
            (TypeKind::PathTemplateUnBound(left), TypeKind::PathTemplateUnBound(right)) => {
                Some(left.can_be(right))
            }
            (TypeKind::PathTemplateBound(left), TypeKind::PathTemplateBound(right)) => {
                Some(left.can_be(right))
            }
            (TypeKind::Set(left), TypeKind::Set(right)) => left.can_be(right),
            (TypeKind::String(left), TypeKind::String(right)) => Some(left.can_be(right)),
            (TypeKind::Timestamp, TypeKind::Timestamp) => Some(true),
            (TypeKind::Request, TypeKind::Request) => Some(true),
            (TypeKind::Resource, TypeKind::Resource) => Some(true),
            _ => Some(false),
        })
        .and_then(|prev| {
            if prev == true {
                Some(true)
            } else {
                self.is_type_coercion_to(other)
            }
        })
    }

    pub fn min(left: &Self, right: &Self) -> Self {
        left.can_be(right)
            .and_then(|result| {
                if result {
                    Some(left.clone())
                } else {
                    right
                        .can_be(left)
                        .and_then(|result| if result { Some(right.clone()) } else { None })
                }
            })
            .unwrap_or(TypeKind::Any)
    }

    pub fn max(left: &Self, right: &Self) -> Self {
        left.can_be(right)
            .and_then(|result| {
                if result {
                    Some(right.clone())
                } else {
                    right
                        .can_be(left)
                        .and_then(|result| if result { Some(left.clone()) } else { None })
                }
            })
            .unwrap_or(TypeKind::Any)
    }

    pub fn erase_literal_constraint(&self) -> TypeKind {
        match self {
            TypeKind::Any => TypeKind::Any,
            TypeKind::Null => TypeKind::Null,
            TypeKind::Boolean(_) => TypeKind::Boolean(MayLiteral::Unknown),
            TypeKind::Bytes(_) => TypeKind::Bytes(MayLiteral::Unknown),
            TypeKind::Duration => TypeKind::Duration,
            TypeKind::Float(_) => TypeKind::Float(MayLiteral::Unknown),
            TypeKind::Integer(_) => TypeKind::Integer(MayLiteral::Unknown),
            TypeKind::LatLng => TypeKind::LatLng,
            TypeKind::List(ty) => TypeKind::List(Box::new(ty.erase_literal_constraint())),
            TypeKind::Map(_) => TypeKind::Map(MayLiteral::Unknown),
            TypeKind::MapDiff(_) => TypeKind::MapDiff((MayLiteral::Unknown, MayLiteral::Unknown)),
            TypeKind::Path(_) => TypeKind::Path(MayLiteral::Unknown),
            TypeKind::PathTemplateUnBound(_) => TypeKind::PathTemplateUnBound(MayLiteral::Unknown),
            TypeKind::PathTemplateBound(_) => TypeKind::PathTemplateBound(MayLiteral::Unknown),
            TypeKind::Set(ty) => TypeKind::Set(Box::new(ty.erase_literal_constraint())),
            TypeKind::String(_) => TypeKind::String(MayLiteral::Unknown),
            TypeKind::Timestamp => TypeKind::Timestamp,
            TypeKind::Request => TypeKind::Request,
            TypeKind::Resource => TypeKind::Resource,
        }
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
            FunctionKind::Function(name) => write!(f, "`{}()`", name),
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

pub struct FunctionInterface<'a>(
    pub (Vec<TypeKind>, TypeKind),
    pub Box<dyn Fn(&dyn Node, &Vec<TypeKind>) -> (TypeKind, Vec<TypeCheckResult>) + 'a>,
);

impl<'a> std::fmt::Debug for FunctionInterface<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("FunctionInterface")
            .field(&self.0)
            .field(&"[impl]".to_owned())
            .finish()
    }
}

#[derive(Debug)]
pub struct Interface<'a> {
    pub functions: HashMap<FunctionKind, Vec<FunctionInterface<'a>>>,
    pub members: HashMap<MemberKind, TypeKind>,
}
