use nanoid::nanoid;
use std::{collections::HashMap, fmt::Display, hash::Hash, iter::zip};

use crate::{
    ast::{BinaryLiteral, Node, UnaryLiteral},
    checker::TypeCheckResult,
    orany::OrAny,
};

pub type Flow = HashMap<TypeID, Ty>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeID(pub String);

impl TypeID {
    pub fn new() -> TypeID {
        TypeID(nanoid!())
    }
}

#[derive(Debug, Clone)]
pub enum Ty {
    Type(TypeID, TypeKind),
    FlowType(TypeID),
}

impl Ty {
    pub fn new(kind: TypeKind) -> Ty {
        Ty::Type(TypeID::new(), kind)
    }

    pub fn kind<'a>(&'a self, flow: &'a Flow) -> &TypeKind {
        match self {
            Ty::Type(_, kind) => kind,
            Ty::FlowType(id) => flow.get(id).unwrap().kind(flow),
        }
    }

    pub fn get_type_mut<'a>(&'a mut self) -> Option<&'a mut TypeKind> {
        match self {
            Ty::Type(_, kind) => Some(kind),
            Ty::FlowType(_) => None,
        }
    }

    pub fn can_be(&self, other: &Self, flow: &Flow) -> OrAny {
        self.kind(flow).can_be(&other.kind(flow), flow)
    }

    #[allow(dead_code)]
    pub fn min(left: &Self, right: &Self, flow: &Flow) -> Self {
        left.can_be(right, flow)
            .and_then(|result| {
                if result {
                    Some(left.clone())
                } else {
                    right.can_be(left, flow).and_then(|result| {
                        if result {
                            Some(right.clone())
                        } else {
                            None
                        }
                    })
                }
            })
            .unwrap_or(Ty::new(TypeKind::Any))
    }

    pub fn max(left: &Self, right: &Self, flow: &Flow) -> Self {
        left.can_be(right, flow)
            .and_then(|result| {
                if result {
                    Some(right.clone())
                } else {
                    right.can_be(left, flow).and_then(|result| {
                        if result {
                            Some(left.clone())
                        } else {
                            None
                        }
                    })
                }
            })
            .unwrap_or(Ty::new(TypeKind::Any))
    }
}

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
    List(MayLiteral<ListLiteral>),
    Map(MayLiteral<MapLiteral>),
    MapDiff((MayLiteral<MapLiteral>, MayLiteral<MapLiteral>)),
    Path(MayLiteral<String>),
    PathTemplateUnBound(MayLiteral<Vec<String>>),
    PathTemplateBound(MayLiteral<Vec<String>>),
    Set(MayLiteral<Box<Ty>>),
    String(MayLiteral<String>),
    Timestamp,
}

#[derive(Debug, Clone)]
pub enum ListLiteral {
    Single(Box<Ty>),
    Tuple(Vec<Ty>),
}

impl ListLiteral {
    pub fn max(&self, flow: &Flow) -> Ty {
        match self {
            ListLiteral::Single(ty) => *ty.clone(),
            ListLiteral::Tuple(tuple) => tuple
                .clone()
                .into_iter()
                .reduce(|left, right| Ty::max(&left, &right, flow))
                .unwrap_or(Ty::new(TypeKind::Any))
                .clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct MapLiteral {
    pub literals: HashMap<String, Ty>,
    pub default: Option<Box<Ty>>,
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
    fn can_be_by<F>(&self, other: &Self, f: F) -> OrAny
    where
        F: FnOnce(&T, &T) -> OrAny,
    {
        match (self, other) {
            (MayLiteral::Unknown, MayLiteral::Unknown) => OrAny::Bool(true),
            (MayLiteral::Unknown, MayLiteral::Literal(_)) => OrAny::Bool(false),
            (MayLiteral::Literal(_), MayLiteral::Unknown) => OrAny::Bool(true),
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

    pub fn is_type_coercion_to(&self, target: &Self, flow: &Flow) -> OrAny {
        OrAny::any(self.get_coercion_list().iter(), |candidate| {
            candidate.can_be(target, flow)
        })
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

    pub fn make_bool_ty(from: OrAny) -> TypeKind {
        match from {
            OrAny::Any => TypeKind::Boolean(MayLiteral::Unknown),
            OrAny::Bool(true) => TypeKind::Boolean(MayLiteral::Literal(true)),
            OrAny::Bool(false) => TypeKind::Boolean(MayLiteral::Literal(false)),
        }
    }

    /// subtyping
    ///
    /// return None if Any
    pub fn can_be(&self, other: &Self, flow: &Flow) -> OrAny {
        (match (self, other) {
            (TypeKind::Any, _) => OrAny::Any,
            (_, TypeKind::Any) => OrAny::Any,
            (TypeKind::Null, TypeKind::Null) => OrAny::Bool(true),
            (TypeKind::Boolean(left), TypeKind::Boolean(right)) => OrAny::Bool(left.can_be(right)),
            (TypeKind::Bytes(left), TypeKind::Bytes(right)) => OrAny::Bool(left.can_be(right)),
            (TypeKind::Duration, TypeKind::Duration) => OrAny::Bool(true),
            (TypeKind::Float(left), TypeKind::Float(right)) => OrAny::Bool(left.can_be(right)),
            (TypeKind::Integer(left), TypeKind::Integer(right)) => OrAny::Bool(left.can_be(right)),
            (TypeKind::LatLng, TypeKind::LatLng) => OrAny::Bool(true),
            (TypeKind::List(left), TypeKind::List(right)) => {
                left.can_be_by(right, |left, right| match (left, right) {
                    (ListLiteral::Single(left), ListLiteral::Single(right)) => {
                        left.can_be(right, flow)
                    }
                    (ListLiteral::Single(_), ListLiteral::Tuple(_)) => OrAny::Bool(false),
                    (ListLiteral::Tuple(left), ListLiteral::Single(right)) => {
                        OrAny::all(left.iter(), |item| item.can_be(right, flow))
                    }
                    (ListLiteral::Tuple(left), ListLiteral::Tuple(right)) => {
                        if left.len() == right.len() {
                            OrAny::all(zip(left, right), |(left, right)| left.can_be(right, flow))
                        } else {
                            OrAny::Bool(false)
                        }
                    }
                })
            }
            (TypeKind::Map(left), TypeKind::Map(right)) => left.can_be_by(right, |left, right| {
                OrAny::all(right.literals.iter(), |(right_key, right_value)| {
                    if let Some(left_value) = left.literals.get(right_key) {
                        left_value.can_be(right_value, flow)
                    } else {
                        OrAny::Bool(false)
                    }
                })
                .and(|| match &right.default {
                    None => OrAny::Bool(true),
                    Some(right_default_ty) => (if let Some(left_default_ty) = &left.default {
                        left_default_ty.can_be(&right_default_ty, flow)
                    } else {
                        OrAny::Bool(false)
                    })
                    .and(|| {
                        OrAny::all(
                            left.literals
                                .iter()
                                .filter(|(key, _)| !right.literals.contains_key(*key)),
                            |(_, value)| value.can_be(&right_default_ty, flow),
                        )
                    }),
                })
            }),
            (TypeKind::MapDiff(left), TypeKind::MapDiff(right)) => left
                .0
                .can_be_by(&right.0, |left, right| {
                    TypeKind::Map(MayLiteral::Literal(left.clone()))
                        .can_be(&TypeKind::Map(MayLiteral::Literal(right.clone())), flow)
                })
                .and(|| {
                    left.1.can_be_by(&right.1, |left, right| {
                        TypeKind::Map(MayLiteral::Literal(left.clone()))
                            .can_be(&TypeKind::Map(MayLiteral::Literal(right.clone())), flow)
                    })
                }),
            (TypeKind::Path(left), TypeKind::Path(right)) => OrAny::Bool(left.can_be(right)),
            (TypeKind::PathTemplateUnBound(left), TypeKind::PathTemplateUnBound(right)) => {
                OrAny::Bool(left.can_be(right))
            }
            (TypeKind::PathTemplateBound(left), TypeKind::PathTemplateBound(right)) => {
                OrAny::Bool(left.can_be(right))
            }
            (TypeKind::Set(left), TypeKind::Set(right)) => {
                left.can_be_by(right, |left, right| left.can_be(right, flow))
            }
            (TypeKind::String(left), TypeKind::String(right)) => OrAny::Bool(left.can_be(right)),
            (TypeKind::Timestamp, TypeKind::Timestamp) => OrAny::Bool(true),
            _ => OrAny::Bool(false),
        })
        .or(|| self.is_type_coercion_to(other, flow))
    }

    #[allow(dead_code)]
    pub fn min(left: &Self, right: &Self, flow: &Flow) -> Self {
        left.can_be(right, flow)
            .and_then(|result| {
                if result {
                    Some(left.clone())
                } else {
                    right.can_be(left, flow).and_then(|result| {
                        if result {
                            Some(right.clone())
                        } else {
                            None
                        }
                    })
                }
            })
            .unwrap_or(TypeKind::Any)
    }

    pub fn max(left: &Self, right: &Self, flow: &Flow) -> Self {
        left.can_be(right, flow)
            .and_then(|result| {
                if result {
                    Some(right.clone())
                } else {
                    right.can_be(left, flow).and_then(|result| {
                        if result {
                            Some(left.clone())
                        } else {
                            None
                        }
                    })
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
            TypeKind::List(_) => TypeKind::List(MayLiteral::Unknown),
            TypeKind::Map(_) => TypeKind::Map(MayLiteral::Unknown),
            TypeKind::MapDiff(_) => TypeKind::MapDiff((MayLiteral::Unknown, MayLiteral::Unknown)),
            TypeKind::Path(_) => TypeKind::Path(MayLiteral::Unknown),
            TypeKind::PathTemplateUnBound(_) => TypeKind::PathTemplateUnBound(MayLiteral::Unknown),
            TypeKind::PathTemplateBound(_) => TypeKind::PathTemplateBound(MayLiteral::Unknown),
            TypeKind::Set(_) => TypeKind::Set(MayLiteral::Unknown),
            TypeKind::String(_) => TypeKind::String(MayLiteral::Unknown),
            TypeKind::Timestamp => TypeKind::Timestamp,
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
    pub Box<dyn Fn(&dyn Node, &Vec<&TypeKind>, &Flow) -> (Ty, Vec<TypeCheckResult>) + 'a>,
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
    pub members: HashMap<MemberKind, Ty>,
}
