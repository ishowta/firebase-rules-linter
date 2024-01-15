pub enum OrAny {
    Any,
    Bool(bool),
}

impl OrAny {
    pub fn all<T>(iter: impl Iterator<Item = T>, f: impl Fn(T) -> OrAny) -> OrAny {
        OrAny::from(
            iter.map(|x| Option::<bool>::from(f(x)))
                .collect::<Option<Vec<bool>>>()
                .map(|res| res.iter().all(|b| *b)),
        )
    }

    pub fn any<T>(iter: impl Iterator<Item = T>, f: impl Fn(T) -> OrAny) -> OrAny {
        OrAny::from(
            iter.map(|x| Option::<bool>::from(f(x)))
                .collect::<Option<Vec<bool>>>()
                .map(|res| res.iter().any(|b| *b)),
        )
    }

    pub fn fmap(self: &Self, f: impl FnOnce(bool) -> OrAny) -> OrAny {
        match self {
            OrAny::Any => OrAny::Any,
            OrAny::Bool(b) => f(*b),
        }
    }

    pub fn map(self: &Self, f: impl FnOnce(bool) -> bool) -> OrAny {
        match self {
            OrAny::Any => OrAny::Any,
            OrAny::Bool(b) => OrAny::Bool(f(*b)),
        }
    }

    pub fn unwrap_or(self: &Self, or: bool) -> bool {
        match self {
            OrAny::Any => or,
            OrAny::Bool(b) => *b,
        }
    }

    pub fn and(self: &Self, next: impl FnOnce() -> OrAny) -> OrAny {
        self.fmap(|b| {
            if b == true {
                next()
            } else {
                OrAny::Bool(false)
            }
        })
    }

    pub fn or(self: &Self, next: impl FnOnce() -> OrAny) -> OrAny {
        self.fmap(|b| {
            if b == false {
                next()
            } else {
                OrAny::Bool(true)
            }
        })
    }

    pub fn is_true(self: &Self) -> bool {
        self.unwrap_or(false)
    }

    pub fn is_false(self: &Self) -> bool {
        self.map(|x| !x).unwrap_or(false)
    }

    pub fn is_any(self: &Self) -> bool {
        match self {
            OrAny::Any => true,
            OrAny::Bool(_) => false,
        }
    }

    pub fn is_bool(self: &Self) -> bool {
        match self {
            OrAny::Any => false,
            OrAny::Bool(_) => true,
        }
    }

    pub fn and_then<T>(self: &Self, f: impl FnOnce(bool) -> Option<T>) -> Option<T> {
        match self {
            OrAny::Any => None,
            OrAny::Bool(b) => f(*b),
        }
    }
}

impl From<OrAny> for Option<bool> {
    fn from(value: OrAny) -> Self {
        match value {
            OrAny::Any => None,
            OrAny::Bool(b) => Some(b),
        }
    }
}

impl From<Option<bool>> for OrAny {
    fn from(value: Option<bool>) -> Self {
        match value {
            None => OrAny::Any,
            Some(b) => OrAny::Bool(b),
        }
    }
}
