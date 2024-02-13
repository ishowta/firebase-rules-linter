use nanoid::{alphabet, nanoid};

use crate::ast::Node;

pub trait Ast {
    fn as_smtlib2(&self) -> String;
}

impl Ast for String {
    fn as_smtlib2(&self) -> String {
        format!("\"{}\"", self)
    }
}

impl Ast for &str {
    fn as_smtlib2(&self) -> String {
        format!("\"{}\"", self)
    }
}

impl Ast for usize {
    fn as_smtlib2(&self) -> String {
        format!("{}", self)
    }
}

impl Ast for i64 {
    fn as_smtlib2(&self) -> String {
        format!("{}", self)
    }
}

impl Ast for i32 {
    fn as_smtlib2(&self) -> String {
        format!("{}", self)
    }
}

impl Ast for bool {
    fn as_smtlib2(&self) -> String {
        format!("{}", self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Symbol {
    pub smtlib2: String,
}

impl Symbol {
    pub fn new(node: &dyn Node) -> Symbol {
        Symbol {
            smtlib2: format!("{}-{}", node.get_id().0, nanoid!(6, &alphabet::SAFE[12..])),
        }
    }
}

impl Ast for Symbol {
    fn as_smtlib2(self: &Self) -> String {
        self.smtlib2.clone()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Sort {
    Bool,
    Int,
    String,
    List(Box<Sort>),
    Entry(Box<Sort>),
    Refl,
    Map,
}

impl Ast for Sort {
    fn as_smtlib2(self: &Self) -> String {
        match self {
            Sort::Bool => "Bool".to_owned(),
            Sort::Int => "Int".to_owned(),
            Sort::String => "String".to_owned(),
            Sort::List(sort) => format!("(List {})", sort.as_smtlib2()),
            Sort::Entry(sort) => format!("(Entry String {})", sort.as_smtlib2()),
            Sort::Refl => "Refl".to_owned(),
            Sort::Map => Sort::List(Box::new(Sort::Entry(Box::new(Sort::Refl)))).as_smtlib2(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Declaration {
    pub smtlib2: String,
}

impl Declaration {
    pub fn new(symbol: &Symbol, sort: &Sort) -> Declaration {
        if *sort == Sort::Map {
            Declaration {
                smtlib2: format!(
                    "(declare-const {} {})
(assert (map-is-uniq {}))",
                    symbol.as_smtlib2(),
                    sort.as_smtlib2(),
                    symbol.as_smtlib2(),
                ),
            }
        } else {
            Declaration {
                smtlib2: format!(
                    "(declare-const {} {})",
                    symbol.as_smtlib2(),
                    sort.as_smtlib2()
                ),
            }
        }
    }
}

impl Ast for Declaration {
    fn as_smtlib2(self: &Self) -> String {
        self.smtlib2.clone()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Literal {
    pub smtlib2: String,
}

impl From<String> for Literal {
    fn from(value: String) -> Self {
        Literal {
            smtlib2: format!("\"{}\"", value),
        }
    }
}

impl From<usize> for Literal {
    fn from(value: usize) -> Self {
        Literal {
            smtlib2: value.to_string(),
        }
    }
}

impl Ast for Literal {
    fn as_smtlib2(self: &Self) -> String {
        self.smtlib2.clone()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Constraint {
    pub smtlib2: String,
}

macro_rules! build_n_args_constraint_constructor {
    ($name:tt, $($args:ident), *) => {
        pub fn $name(func_name: &str, $($args: &impl Ast), *) -> Constraint {
            let mut smtlib2 = "(".to_string();
            smtlib2.push_str(func_name);

            $(
                smtlib2.push_str(" ");
                smtlib2.push_str($args.as_smtlib2().as_str());
            )*

            smtlib2.push_str(")");

            if smtlib2.len() > 80 {
                smtlib2 = "(".to_string();
                smtlib2.push_str(func_name);
                smtlib2.push_str("\n");

                $(
                    smtlib2.push_str(
                        $args.as_smtlib2()
                            .split("\n")
                            .fold("".to_owned(), |mut acc, line| {
                                acc.push_str("    ");
                                acc.push_str(line);
                                acc.push_str("\n");
                                acc
                            })
                            .as_str(),
                    );
                )*

                smtlib2.push_str(")");
            }

            Constraint { smtlib2: smtlib2 }
        }
    };
}

impl Constraint {
    pub fn mono(name: &str) -> Constraint {
        Constraint {
            smtlib2: name.to_string(),
        }
    }

    pub fn new<T>(func_name: &str, args: Vec<&T>) -> Constraint
    where
        T: Ast,
    {
        let mut smtlib2 = args.iter().fold(
            {
                let mut res = "(".to_owned();
                res.push_str(func_name);
                res
            },
            |mut acc, arg| {
                acc.push_str(" ");
                acc.push_str(arg.as_smtlib2().as_str());
                acc
            },
        );
        smtlib2.push_str(")");

        if smtlib2.len() > 80 {
            smtlib2 = args.iter().fold(
                {
                    let mut res = "(".to_owned();
                    res.push_str(func_name);
                    res.push_str("\n");
                    res
                },
                |mut acc, arg| {
                    acc.push_str(
                        arg.as_smtlib2()
                            .split("\n")
                            .fold("".to_owned(), |mut acc, line| {
                                acc.push_str("    ");
                                acc.push_str(line);
                                acc.push_str("\n");
                                acc
                            })
                            .as_str(),
                    );
                    acc
                },
            );
            smtlib2.push_str(")");
        }

        Constraint { smtlib2: smtlib2 }
    }

    build_n_args_constraint_constructor!(new1, arg1);
    build_n_args_constraint_constructor!(new2, arg1, arg2);
    build_n_args_constraint_constructor!(new3, arg1, arg2, arg3);
    build_n_args_constraint_constructor!(new4, arg1, arg2, arg3, arg4);
    build_n_args_constraint_constructor!(new5, arg1, arg2, arg3, arg4, arg5);
}

impl From<Literal> for Constraint {
    fn from(value: Literal) -> Self {
        Constraint {
            smtlib2: value.as_smtlib2(),
        }
    }
}

impl Ast for Constraint {
    fn as_smtlib2(self: &Self) -> String {
        self.smtlib2.clone()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Assert {
    smtlib2: String,
}

impl Assert {
    pub fn new(constraint: &Constraint) -> Assert {
        Assert {
            smtlib2: format!("(assert {})", constraint.as_smtlib2()),
        }
    }
}

impl Ast for Assert {
    fn as_smtlib2(self: &Self) -> String {
        self.smtlib2.clone()
    }
}
