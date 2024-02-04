use std::{cell::RefCell, collections::HashMap, io::Write, process::Command};

use log::{debug, info};
use miette::{Diagnostic, SourceSpan};
use nanoid::{alphabet, nanoid};
use tempfile::NamedTempFile;
use thiserror::Error;

use crate::{
    ast::{BinaryLiteral, Expression, ExpressionKind, Node, NodeID, Rule, RuleGroup},
    symbol::{Bindings, SymbolReferences, VariableNodeRef},
    ty::FunctionKind,
};

trait Ast {
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

impl Ast for f64 {
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
struct Symbol {
    smtlib2: String,
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
enum Sort {
    Bool,
    Int,
    Float64,
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
            Sort::Float64 => "Float64".to_owned(),
            Sort::List(sort) => format!("(List {})", sort.as_smtlib2()),
            Sort::Entry(sort) => format!("(Entry String {})", sort.as_smtlib2()),
            Sort::Refl => "Refl".to_owned(),
            Sort::Map => Sort::List(Box::new(Sort::Entry(Box::new(Sort::Refl)))).as_smtlib2(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Declaration {
    smtlib2: String,
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
struct Literal {
    smtlib2: String,
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
struct Constraint {
    smtlib2: String,
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
}

impl From<Literal> for Constraint {
    fn from(value: Literal) -> Self {
        Constraint {
            smtlib2: value.as_smtlib2(),
        }
    }
}

macro_rules! constraint {
    ($func_name:expr, $($args:expr),*) => {{
        let mut smtlib2 = "(".to_string();
        smtlib2.push_str($func_name);
        $(
            smtlib2.push_str(" ");
            smtlib2.push_str($args.as_smtlib2().as_str());
        )*
        smtlib2.push_str(")");

        if smtlib2.len() > 80 {
            smtlib2 = "(".to_string();
            smtlib2.push_str($func_name);
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
    }}
}

impl Ast for Constraint {
    fn as_smtlib2(self: &Self) -> String {
        self.smtlib2.clone()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Assert {
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

#[derive(Clone, Debug, Error, Diagnostic, PartialEq, Eq, Hash)]
#[error("{reason}")]
#[diagnostic()]
pub struct AnalysysError {
    pub reason: String,
    #[label]
    pub at: SourceSpan,
}

impl AnalysysError {
    pub fn new(reason: String, node: &dyn Node) -> AnalysysError {
        AnalysysError {
            reason: reason,
            at: node.get_span().into(),
        }
    }
}

#[derive(Clone, Debug)]
struct Res {
    value: Symbol,
    constraints: Vec<Constraint>,
}

#[derive(Clone, Debug)]
pub struct AnalysysGlobalContext<'a> {
    pub bindings: &'a Bindings<'a>,
    pub symbol_references: &'a SymbolReferences<'a>,
    pub source_code: &'a String,
}

#[derive(Clone, Debug)]
struct AnalysysContext<'a, 'ctx> {
    pub bindings: &'a Bindings<'a>,
    pub symbol_references: &'a SymbolReferences<'a>,
    pub source_code: &'a String,
    pub declarations: &'ctx RefCell<Vec<Declaration>>,
    pub variable_bindings: &'ctx HashMap<&'a NodeID, &'ctx Symbol>,
}

fn destruct_bool(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Constraint) {
    let dest_value = Symbol::new(expr);
    declarations.push(Declaration::new(&dest_value, &Sort::Bool));
    (
        dest_value.clone(),
        constraint!("=", refl_sym, constraint!("bool", dest_value)),
    )
}

fn destruct_bytes(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Symbol, Constraint) {
    let dest_value = Symbol::new(expr);
    let dest_bytes_sym = Symbol::new(expr);
    declarations.push(Declaration::new(&dest_value, &Sort::String));
    declarations.push(Declaration::new(&dest_bytes_sym, &Sort::Int));
    (
        dest_value.clone(),
        dest_bytes_sym.clone(),
        constraint!(
            "=",
            refl_sym,
            constraint!("bytes", dest_value, dest_bytes_sym)
        ),
    )
}

fn destruct_float(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Constraint) {
    let dest_value = Symbol::new(expr);
    declarations.push(Declaration::new(&dest_value, &Sort::Float64));
    (
        dest_value.clone(),
        constraint!("=", refl_sym, constraint!("float", dest_value)),
    )
}

fn destruct_int(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Constraint) {
    let dest_value = Symbol::new(expr);
    declarations.push(Declaration::new(&dest_value, &Sort::Int));
    (
        dest_value.clone(),
        constraint!("=", refl_sym, constraint!("int", dest_value)),
    )
}

fn destruct_list(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Symbol, Constraint) {
    let dest_value = Symbol::new(expr);
    let dest_bytes_sym = Symbol::new(expr);
    declarations.push(Declaration::new(
        &dest_value,
        &Sort::List(Box::new(Sort::Refl)),
    ));
    declarations.push(Declaration::new(&dest_bytes_sym, &Sort::Int));
    (
        dest_value.clone(),
        dest_bytes_sym.clone(),
        constraint!(
            "=",
            refl_sym,
            constraint!("list", dest_value, dest_bytes_sym)
        ),
    )
}

fn destruct_map(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Constraint) {
    let dest_value = Symbol::new(expr);
    declarations.push(Declaration::new(&dest_value, &Sort::Map));
    (
        dest_value.clone(),
        constraint!("=", refl_sym, constraint!("map", dest_value)),
    )
}

fn destruct_mapdiff(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Symbol, Symbol, Constraint) {
    let dest_lvalue = Symbol::new(expr);
    let dest_rvalue = Symbol::new(expr);
    let dest_bytes_sym = Symbol::new(expr);
    declarations.push(Declaration::new(&dest_lvalue, &Sort::Map));
    declarations.push(Declaration::new(&dest_rvalue, &Sort::Map));
    declarations.push(Declaration::new(&dest_bytes_sym, &Sort::Int));
    (
        dest_lvalue.clone(),
        dest_rvalue.clone(),
        dest_bytes_sym.clone(),
        constraint!(
            "=",
            refl_sym,
            constraint!("mapdiff", dest_lvalue, dest_rvalue, dest_bytes_sym)
        ),
    )
}

fn destruct_set(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Symbol, Constraint) {
    let dest_value = Symbol::new(expr);
    let dest_bytes_sym = Symbol::new(expr);
    declarations.push(Declaration::new(
        &dest_value,
        &Sort::List(Box::new(Sort::Refl)),
    ));
    declarations.push(Declaration::new(&dest_bytes_sym, &Sort::Int));
    (
        dest_value.clone(),
        dest_bytes_sym.clone(),
        constraint!(
            "=",
            refl_sym,
            constraint!("set", dest_value, dest_bytes_sym)
        ),
    )
}

fn destruct_string(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Symbol, Constraint) {
    let dest_value = Symbol::new(expr);
    let dest_bytes_sym = Symbol::new(expr);
    declarations.push(Declaration::new(&dest_value, &Sort::String));
    declarations.push(Declaration::new(&dest_bytes_sym, &Sort::Int));
    (
        dest_value.clone(),
        dest_bytes_sym.clone(),
        constraint!(
            "=",
            refl_sym,
            constraint!("str", dest_value, dest_bytes_sym)
        ),
    )
}

fn check_function_calling(
    cur_expr: &dyn Node,
    ctx: &AnalysysContext,
    func: &FunctionKind,
    args: &Vec<&Res>,
    cur_value: &Symbol,
    declarations: &mut Vec<Declaration>,
) -> Vec<Constraint> {
    let args_constraints: Vec<Vec<Constraint>> =
        args.iter().map(|res| res.constraints.clone()).collect();
    match func {
        FunctionKind::Function(fn_name) => match fn_name.as_str() {
            "keys" => {
                let [map_val] = args[..] else { panic!() };
                let (map_inner, map_constraint) =
                    destruct_map(&map_val.value, cur_expr, declarations);
                let (cur_inner_value, _, cur_inner_constraint) =
                    destruct_list(&cur_value, cur_expr, declarations);
                args_constraints
                    .into_iter()
                    .flatten()
                    .chain([
                        map_constraint,
                        cur_inner_constraint,
                        constraint!("=", cur_inner_value, constraint!("list-keys", map_inner)),
                    ])
                    .collect()
            }
            "hasOnly" => {
                let [target_val, keys_val] = args[..] else {
                    panic!()
                };
                let (target_inner_val, _, target_constraint) =
                    destruct_list(&target_val.value, cur_expr, declarations);
                let (keys_inner_val, _, keys_constraint) =
                    destruct_list(&keys_val.value, cur_expr, declarations);
                let (cur_inner_val, cur_constraint) =
                    destruct_bool(&cur_value, cur_expr, declarations);
                args_constraints
                    .into_iter()
                    .flatten()
                    .chain([
                        target_constraint,
                        keys_constraint,
                        cur_constraint,
                        constraint!(
                            "=",
                            cur_inner_val,
                            constraint!("refl-list-in-refl-list", target_inner_val, keys_inner_val) // constraint!(
                                                                                                    //     "forall ((elem Refl))",
                                                                                                    //     constraint!(
                                                                                                    //         "implies",
                                                                                                    //         constraint!(
                                                                                                    //             "refl-list-exists",
                                                                                                    //             target_inner_val,
                                                                                                    //             Constraint::mono("elem")
                                                                                                    //         ),
                                                                                                    //         constraint!(
                                                                                                    //             "refl-list-exists",
                                                                                                    //             keys_inner_val,
                                                                                                    //             Constraint::mono("elem")
                                                                                                    //         )
                                                                                                    //     )
                                                                                                    // )
                        ),
                    ])
                    .collect()
            }
            _ => todo!(),
        },
        FunctionKind::UnaryOp(_) => todo!(),
        FunctionKind::BinaryOp(binary_op) => match binary_op {
            BinaryLiteral::And => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };
                let (left_val, left_constraint) =
                    destruct_bool(&left_res.value, cur_expr, declarations);
                let (right_val, right_constraint) =
                    destruct_bool(&right_res.value, cur_expr, declarations);

                args_constraints
                    .into_iter()
                    .flatten()
                    .chain([constraint!(
                        "=",
                        cur_value,
                        constraint!(
                            "bool",
                            constraint!(
                                "and",
                                constraint!("and", left_val, left_constraint),
                                constraint!("and", right_val, right_constraint)
                            )
                        )
                    )])
                    .collect()
            }
            BinaryLiteral::Or => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };
                let (left_val, left_constraint) =
                    destruct_bool(&left_res.value, cur_expr, declarations);
                let (right_val, right_constraint) =
                    destruct_bool(&right_res.value, cur_expr, declarations);

                vec![constraint!(
                    "=",
                    cur_value,
                    constraint!(
                        "bool",
                        constraint!(
                            "or",
                            constraint!(
                                "and",
                                left_val,
                                left_constraint,
                                Constraint::new("and", args_constraints[0].iter().collect())
                            ),
                            constraint!(
                                "and",
                                right_val,
                                right_constraint,
                                Constraint::new("and", args_constraints[1].iter().collect())
                            )
                        )
                    )
                )]
            }
            BinaryLiteral::Add => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };

                let (left_int_val, left_int_constraint) =
                    destruct_int(&left_res.value, cur_expr, declarations);
                let (left_float_val, left_float_constraint) =
                    destruct_float(&left_res.value, cur_expr, declarations);
                let (left_str_val, left_str_bytes, left_str_constraint) =
                    destruct_string(&left_res.value, cur_expr, declarations);

                let (right_int_val, right_int_constraint) =
                    destruct_int(&right_res.value, cur_expr, declarations);
                let (right_float_val, right_float_constraint) =
                    destruct_float(&right_res.value, cur_expr, declarations);
                let (right_str_val, right_str_bytes, right_str_constraint) =
                    destruct_string(&right_res.value, cur_expr, declarations);

                args_constraints
                    .into_iter()
                    .flatten()
                    .chain([constraint!(
                        "or",
                        constraint!(
                            "and",
                            left_int_constraint,
                            right_int_constraint,
                            constraint!(
                                "=",
                                cur_value,
                                constraint!("int", constraint!("+", left_int_val, right_int_val))
                            )
                        ),
                        constraint!(
                            "and",
                            left_float_constraint,
                            right_float_constraint,
                            constraint!(
                                "=",
                                cur_value,
                                constraint!(
                                    "float",
                                    constraint!(
                                        "fp.add roundNearestTiesToEven",
                                        left_float_val,
                                        right_float_val
                                    )
                                )
                            )
                        ),
                        constraint!(
                            "and",
                            left_str_constraint,
                            right_str_constraint,
                            constraint!(
                                "=",
                                cur_value,
                                constraint!(
                                    "str",
                                    constraint!("str.++", left_str_val, right_str_val),
                                    constraint!("+", left_str_bytes, right_str_bytes)
                                )
                            )
                        )
                    )])
                    .collect()
            }
            BinaryLiteral::Sub => todo!(),
            BinaryLiteral::Mul => todo!(),
            BinaryLiteral::Div => todo!(),
            BinaryLiteral::Mod => todo!(),
            BinaryLiteral::Gt => todo!(),
            BinaryLiteral::Gte => todo!(),
            BinaryLiteral::Lt => todo!(),
            BinaryLiteral::Lte => todo!(),
            BinaryLiteral::Eq => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };
                let mut constraints = vec![constraint!(
                    "=",
                    cur_value,
                    constraint!("bool", constraint!("=", &left_res.value, &right_res.value))
                )];
                constraints.extend(left_res.constraints.iter().cloned());
                constraints.extend(right_res.constraints.iter().cloned());
                constraints.extend(args_constraints.into_iter().flatten());
                constraints
            }
            BinaryLiteral::NotEq => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };
                let mut constraints = vec![constraint!(
                    "=",
                    cur_value,
                    constraint!(
                        "bool",
                        constraint!("not", constraint!("=", &left_res.value, &right_res.value))
                    )
                )];
                constraints.extend(left_res.constraints.iter().cloned());
                constraints.extend(right_res.constraints.iter().cloned());
                constraints.extend(args_constraints.into_iter().flatten());
                constraints
            }
            BinaryLiteral::In => todo!(),
        },
        FunctionKind::Subscript => todo!(),
        FunctionKind::SubscriptRange => todo!(),
    }
}

fn check_expression(ctx: &AnalysysContext, cur_expr: &Expression) -> Res {
    let cur_value = Symbol::new(cur_expr);
    ctx.declarations
        .borrow_mut()
        .push(Declaration::new(&cur_value, &Sort::Refl));

    let constraints = match &cur_expr.kind {
        ExpressionKind::Literal(lit) => match lit {
            crate::ast::Literal::Null => {
                vec![constraint!("=", cur_value, Constraint::mono("null"))]
            }
            crate::ast::Literal::Bool(lit) => {
                vec![constraint!("=", cur_value, constraint!("bool", lit))]
            }
            crate::ast::Literal::Int(lit) => {
                vec![constraint!("=", cur_value, constraint!("int", lit))]
            }
            crate::ast::Literal::Float(lit) => {
                let lit_as_bits: String = lit
                    .to_be_bytes()
                    .iter()
                    .map(|b| format!("{:08b}", b))
                    .collect::<Vec<String>>()
                    .join("");
                vec![constraint!(
                    "=",
                    cur_value,
                    constraint!(
                        "float",
                        Constraint::mono(
                            format!(
                                "(fp #b{} #b{} #b{})",
                                lit_as_bits[0..1].to_owned(),
                                lit_as_bits[1..12].to_owned(),
                                lit_as_bits[12..].to_owned()
                            )
                            .as_str()
                        )
                    )
                )]
            }
            crate::ast::Literal::String(lit) => vec![constraint!(
                "=",
                cur_value,
                constraint!("str", lit, Literal::from(lit.len()))
            )],
            crate::ast::Literal::List(lit) => {
                let elems_res: Vec<_> = lit
                    .iter()
                    .map(|elem_lit| check_expression(ctx, elem_lit))
                    .collect();

                vec![
                    constraint!(
                        "=",
                        cur_value,
                        constraint!(
                            "list",
                            elems_res.iter().fold(
                                constraint!("as nil", Sort::List(Box::new(Sort::Refl))),
                                |acc, elem| { constraint!("insert", elem.value, acc) },
                            ),
                            elems_res.iter().fold(
                                Constraint::from(Literal::from(0)),
                                |acc, elem| constraint!(
                                    "+",
                                    constraint!("refl-sum", elem.value),
                                    acc
                                )
                            )
                        )
                    ),
                    Constraint::new(
                        "and",
                        elems_res.iter().flat_map(|res| &res.constraints).collect(),
                    ),
                ]
            }
            crate::ast::Literal::Map(lit) => {
                let elems_res: Vec<_> = lit
                    .iter()
                    .map(|(key, value_expr)| (key, check_expression(ctx, value_expr)))
                    .collect();

                vec![
                    constraint!(
                        "=",
                        cur_value,
                        constraint!(
                            "map",
                            elems_res.iter().fold(
                                constraint!("as nil", Sort::Map),
                                |acc, (key, value)| {
                                    constraint!(
                                        "insert",
                                        constraint!("entry", key, value.value),
                                        acc
                                    )
                                }
                            ),
                            elems_res.iter().fold(
                                Constraint::from(Literal::from(0)),
                                |acc, (_, value)| constraint!(
                                    "+",
                                    2,
                                    constraint!("refl-sum", value.value),
                                    acc
                                )
                            )
                        )
                    ),
                    Constraint::new(
                        "and",
                        elems_res
                            .iter()
                            .flat_map(|(_, res)| &res.constraints)
                            .collect(),
                    ),
                ]
            }
            crate::ast::Literal::Path(_) => vec![constraint!("=", cur_value, "path")],
        },
        ExpressionKind::Variable(_) => match ctx
            .bindings
            .variable_table
            .get(&cur_expr.id)
            .and_then(|node| Some(node.1))
        {
            None => vec![],
            Some(variable_node_ref) => match variable_node_ref {
                VariableNodeRef::LetBinding(node) => {
                    let value = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![constraint!("=", cur_value, value)]
                }
                VariableNodeRef::FunctionArgument(node) => {
                    let value = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![constraint!("=", cur_value, value)]
                }
                VariableNodeRef::PathCapture(node) => {
                    let value = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![constraint!("=", cur_value, value)]
                }
                VariableNodeRef::PathCaptureGroup(node) => {
                    let value = ctx.variable_bindings.get(&node.id).unwrap();
                    vec![constraint!("=", cur_value, value)]
                }
                VariableNodeRef::GlobalVariable(_) => {
                    // TODO
                    vec![constraint!(
                        "=",
                        cur_value,
                        Symbol {
                            smtlib2: "request_resource_data".to_string()
                        }
                    )]
                }
            },
        },
        ExpressionKind::TypeCheckOperation(target_expr, type_name) => {
            let target_res = check_expression(ctx, &target_expr);
            match type_name.as_str() {
                "bool" => {
                    let inner_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_sym, &Sort::Bool));
                    vec![constraint!(
                        "=",
                        target_res.value,
                        constraint!("bool", inner_sym)
                    )]
                }
                "int" => {
                    let inner_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_sym, &Sort::Int));
                    vec![constraint!(
                        "=",
                        target_res.value,
                        constraint!("int", inner_sym)
                    )]
                }
                "float" => {
                    let inner_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_sym, &Sort::Float64));
                    vec![constraint!(
                        "=",
                        target_res.value,
                        constraint!("float", inner_sym)
                    )]
                }
                "number" => {
                    let inner_int_sym = Symbol::new(target_expr as &Expression);
                    let inner_float_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_int_sym, &Sort::Int));
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_float_sym, &Sort::Float64));
                    vec![constraint!(
                        "or",
                        constraint!("=", target_res.value, constraint!("int", inner_int_sym)),
                        constraint!("=", target_res.value, constraint!("float", inner_float_sym))
                    )]
                }
                "string" => {
                    let inner_value = Symbol::new(target_expr as &Expression);
                    let inner_bytes_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_value, &Sort::String));
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_bytes_sym, &Sort::Int));
                    vec![constraint!(
                        "=",
                        target_res.value,
                        constraint!("str", inner_value, inner_bytes_sym)
                    )]
                }
                "list" => {
                    let inner_value = Symbol::new(target_expr as &Expression);
                    let inner_bytes_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations.borrow_mut().push(Declaration::new(
                        &inner_value,
                        &Sort::List(Box::new(Sort::Refl)),
                    ));
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_bytes_sym, &Sort::Int));
                    vec![constraint!(
                        "=",
                        target_res.value,
                        constraint!("list", inner_value, inner_bytes_sym)
                    )]
                }
                "map" => {
                    let inner_sym = Symbol::new(target_expr as &Expression);
                    ctx.declarations
                        .borrow_mut()
                        .push(Declaration::new(&inner_sym, &Sort::Map));
                    vec![constraint!(
                        "=",
                        target_res.value,
                        constraint!("map", inner_sym, constraint!("list-sum", inner_sym))
                    )]
                }
                "timestamp" => {
                    vec![constraint!(
                        "=",
                        target_res.value,
                        Constraint::mono("timestamp")
                    )]
                }
                "duration" => {
                    vec![constraint!(
                        "=",
                        target_res.value,
                        Constraint::mono("duration")
                    )]
                }
                "path" => {
                    vec![constraint!("=", target_res.value, Constraint::mono("path"))]
                }
                "latlng" => {
                    vec![constraint!(
                        "=",
                        target_res.value,
                        Constraint::mono("latlng")
                    )]
                }
                _ => vec![],
            }
        }
        ExpressionKind::UnaryOperation(op_lit, op_param_expr) => {
            let op_param_res = check_expression(ctx, &op_param_expr);
            check_function_calling(
                cur_expr,
                ctx,
                &FunctionKind::UnaryOp(*op_lit),
                &vec![&op_param_res],
                &cur_value,
                ctx.declarations.borrow_mut().as_mut(),
            )
        }
        ExpressionKind::BinaryOperation(op_lit, op_param1_expr, op_param2_expr) => {
            let op_param1_res = check_expression(ctx, &op_param1_expr);
            let op_param2_res = check_expression(ctx, &op_param2_expr);
            check_function_calling(
                cur_expr,
                ctx,
                &FunctionKind::BinaryOp(*op_lit),
                &vec![&op_param1_res, &op_param2_res],
                &cur_value,
                ctx.declarations.borrow_mut().as_mut(),
            )
        }
        ExpressionKind::SubscriptExpression(obj_expr, param_expr) => {
            let obj_res = check_expression(ctx, &obj_expr);
            let param_res = check_expression(ctx, &param_expr);
            check_function_calling(
                cur_expr,
                ctx,
                &FunctionKind::Subscript,
                &vec![&obj_res, &param_res],
                &cur_value,
                ctx.declarations.borrow_mut().as_mut(),
            )
        }
        ExpressionKind::FunctionCallExpression(fn_name, params_expr) => {
            let params_res: Vec<_> = params_expr
                .iter()
                .map(|expr| check_expression(ctx, expr))
                .collect();
            check_function_calling(
                cur_expr,
                ctx,
                &FunctionKind::Function(fn_name.clone()),
                &params_res.iter().map(|x| x).collect(),
                &cur_value,
                ctx.declarations.borrow_mut().as_mut(),
            )
        }
        ExpressionKind::TernaryOperation(cond_expr, left_expr, right_expr) => {
            let cond_res = check_expression(ctx, &cond_expr);
            let left_res = check_expression(ctx, &left_expr);
            let right_res = check_expression(ctx, &right_expr);
            vec![constraint!(
                "=",
                cur_value,
                constraint!(
                    "ite",
                    constraint!(
                        "and",
                        constraint!("=", cond_res.value, constraint!("bool", true)),
                        Constraint::new("and", cond_res.constraints.iter().collect())
                    ),
                    constraint!(
                        "and",
                        left_res.value,
                        Constraint::new("and", left_res.constraints.iter().collect())
                    ),
                    constraint!(
                        "and",
                        right_res.value,
                        Constraint::new("and", right_res.constraints.iter().collect())
                    )
                )
            )]
        }
        ExpressionKind::MemberExpression(obj_expr, member_expr) => match &member_expr.kind {
            ExpressionKind::Variable(variable_name) => {
                let obj_res = check_expression(ctx, &obj_expr);
                let member_res = check_expression(ctx, &member_expr);

                let obj_inner_sym = Symbol::new(obj_expr as &Expression);
                ctx.declarations
                    .borrow_mut()
                    .push(Declaration::new(&obj_inner_sym, &Sort::Map));

                obj_res
                    .constraints
                    .iter()
                    .chain(member_res.constraints.iter())
                    .chain(
                        [
                            constraint!("=", obj_res.value, constraint!("map", obj_inner_sym)),
                            constraint!("=", cur_value, member_res.value),
                            constraint!(
                                "=",
                                member_res.value,
                                constraint!("list-get", obj_inner_sym, variable_name)
                            ),
                        ]
                        .iter(),
                    )
                    .cloned()
                    .collect()
            }
            ExpressionKind::FunctionCallExpression(fn_name, params_expr) => {
                let obj_res = check_expression(ctx, &obj_expr);
                let params_res: Vec<_> = params_expr
                    .iter()
                    .map(|expr| check_expression(ctx, expr))
                    .collect();
                let mut params = vec![&obj_res];
                params.extend(params_res.iter().map(|x| x));
                check_function_calling(
                    cur_expr,
                    ctx,
                    &FunctionKind::Function(fn_name.clone()),
                    &params,
                    &cur_value,
                    ctx.declarations.borrow_mut().as_mut(),
                )
            }
            _ => panic!(),
        },
    };
    Res {
        value: cur_value,
        constraints: constraints,
    }
}

fn run_z3(source: &String) -> String {
    debug!("{}", source);
    let mut debug_source = "".to_owned();
    let mut line_count = 0;
    for line in source.split("\n") {
        debug_source += format!("{}: {}\n", line_count + 1, line).as_str();
        line_count += 1;
    }
    info!("RUN Z3:\n{}", debug_source);
    let mut source_file = NamedTempFile::new().unwrap();
    let _ = source_file.write_all(source.as_bytes());
    let command_result = Command::new("z3").arg(source_file.path()).output();
    let command_output = String::from_utf8_lossy(&command_result.unwrap().stdout)
        .trim()
        .into();
    command_output
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SolverResult {
    Sat(String),
    Unsat,
    Unknown,
}

fn solve(source: &String) -> SolverResult {
    let input = format!(
        "
{}

(check-sat)
(get-model)
",
        source
    );
    let output = run_z3(&input);
    match output.split("\n").nth(0) {
        Some("sat") => {
            SolverResult::Sat(output.split("\n").skip(1).collect::<Vec<&str>>().join("\n"))
        }
        Some("unsat") => SolverResult::Unsat,
        Some("unknown") => SolverResult::Unknown,
        Some(error) => {
            eprintln!("Z3 Error: {}", error);
            panic!()
        }
        _ => panic!(),
    }
}

fn check_rule(ctx: &AnalysysGlobalContext, rule: &Rule) -> Vec<AnalysysError> {
    info!(
        "check rule at {} line",
        rule.get_span().0.start_point.row + 1
    );

    let ctx = AnalysysContext {
        bindings: ctx.bindings,
        symbol_references: ctx.symbol_references,
        source_code: ctx.source_code,
        variable_bindings: &HashMap::new(),
        declarations: &RefCell::new(vec![Declaration {
            smtlib2: format!(
                r#"
(declare-datatypes (T1 T2) ((Entry (entry (key T1) (value T2)))))

(declare-datatypes ((Refl 0)) (
    (
        (undefined)
        (null)
        (bool (bool_val Bool))
        (int (int_val Int))
        (float (float_val Float64))
        (str (str_val String) (str_bytes Int))
        (bytes (bytes_val String) (bytes_bytes Int))
        (duration)
        (latlng)
        (timestamp)
        (list (list_val (List Refl)) (list_bytes Int))
        (map (map_val (List (Entry String Refl))))
        (mapdiff (mapdiff_left (List (Entry String Refl))) (mapdiff_right (List (Entry String Refl))) (mapdiff_bytes Int))
        (set (set_val (List Refl)) (set_bytes Int))
        (path)
    )
))

(define-fun-rec
    list-get
    (
        (lst (List (Entry String Refl)))
        (sk String)
    )
    Refl
    (if
        (= lst (as nil (List (Entry String Refl))))
        undefined
        (if
            (= (key (head lst)) sk)
            (value (head lst))
            (list-get (tail lst) sk)
        )
    )
)

(define-fun-rec
    list-exists
    (
        (lst (List (Entry String Refl)))
        (sk String)
    )
    Bool
    (if
        (= lst (as nil (List (Entry String Refl))))
        false
        (if
            (= (key (head lst)) sk)
            true
            (list-exists (tail lst) sk)
        )
    )
)

(define-fun-rec
    map-is-uniq
    (
        (lst (List (Entry String Refl)))
    )
    Bool
    (if
        (= lst (as nil (List (Entry String Refl))))
        true
        (and
            (not (list-exists (tail lst) (key (head lst))))
            ;(match (value (head lst)) (
            ;    (undefined true)
            ;    (null true)
            ;    ((bool x) true)
            ;    ((int x) true)
            ;    ((float x) true)
            ;    ((str v b) true)
            ;    ((bytes v b) true)
            ;    (duration true)
            ;    (latlng true)
            ;    (timestamp true)
            ;    ((list v b) true)
            ;    ((map x) (map-is-uniq x))
            ;    ((mapdiff l r b) true)
            ;    ((set v b) true)
            ;    (path true)
            ;))
            (map-is-uniq (tail lst))
        )
    )
)

(define-fun-rec
    list-sum
    (
        (lst (List (Entry String Refl)))
    )
    Int
    (if
        (= lst (as nil (List (Entry String Refl))))
        0
        (if
            (= (value (head lst)) undefined)
            0
            (+
                2
                (match (value (head lst)) (
                    (undefined (* 1024 1024))
                    (null 1)
                    ((bool x) 1)
                    ((int x) 8)
                    ((float x) 8)
                    ((str v b) b)
                    ((bytes v b) b)
                    (duration 8)
                    (latlng 16)
                    (timestamp 8)
                    ((list v b) b)
                    ((map x) (list-sum x))
                    ((mapdiff l r b) (* 1024 1024))
                    ((set v b) (* 1024 1024))
                    (path (* 6 1024))
                ))
                (list-sum (tail lst))
            )
        )
    )
)

(define-fun-rec
    refl-sum
    (
        (refl Refl)
    )
    Int
    (match refl (
        (undefined (* 1024 1024))
        (null 1)
        ((bool x) 1)
        ((int x) 8)
        ((float x) 8)
        ((str v b) b)
        ((bytes v b) b)
        (duration 8)
        (latlng 16)
        (timestamp 8)
        ((list v b) b)
        ((map x) (list-sum x))
        ((mapdiff l r b) (* 1024 1024))
        ((set v b) (* 1024 1024))
        (path (* 6 1024))
    ))
)

(define-fun-rec
    list-keys
    (
        (lst (List (Entry String Refl)))
    )
    (List Refl)
    (if
        (= lst (as nil (List (Entry String Refl))))
        (as nil (List Refl))
        (insert
            (str (key (head lst)) (str.len (key (head lst))))
            (list-keys (tail lst))
        )
    )
)

(define-fun-rec
    refl-list-exists
    (
        (lst (List Refl))
        (sk Refl)
    )
    Bool
    (if
        (= lst (as nil (List Refl)))
        false
        (if
            (= (head lst) sk)
            true
            (refl-list-exists (tail lst) sk)
        )
    )
)

(define-fun-rec
    refl-list-in-refl-list
    (
        (left (List Refl))
        (right (List Refl))
    )
    Bool
    (if
        (= left (as nil (List Refl)))
        true
        (and
            (refl-list-exists right (head left))
            (refl-list-in-refl-list (tail left) right)
        )
    )
)

(define-fun
    refl-map-is-uniq
    (
        (refl Refl)
    )
    Bool
    (match refl (
        (undefined true)
        (null true)
        ((bool x) true)
        ((int x) true)
        ((float x) true)
        ((str v b) true)
        ((bytes v b) true)
        (duration true)
        (latlng true)
        (timestamp true)
        ((list v b) true)
        ((map x) (map-is-uniq x))
        ((mapdiff l r b) true)
        ((set v b) true)
        (path true)
    ))
)

(declare-const request_resource_data Refl)
(declare-const request_resource_data_inner (List (Entry String Refl)))
(assert (= request_resource_data (map request_resource_data_inner)))

;(declare-const request_resource Refl)
;(declare-const request_resource_inner (List (Entry String Refl)))
;(assert (= (list-get request_resource_inner "data") request_resource_data))
;(assert (= request_resource (map request_resource_inner)))

;(declare-const request Refl)
;(declare-const request_inner (List (Entry String Refl)))
;(assert (= (list-get request_inner "resource") request_resource))
;(assert (= request (map request_inner)))

(assert (refl-map-is-uniq request_resource_data))
"#
            ),
        }]),
    };

    let Res {
        value: condition_value,
        constraints: condition_constraints,
    } = check_expression(&ctx, &rule.condition);

    let mut errors = vec![];

    // check always false
    let mut is_always_false_unsat: bool = false;
    {
        info!("check always false");
        let source_code = format!(
            "{}

{}

{}
",
            ctx.declarations
                .borrow()
                .iter()
                .map(|declaration| declaration.as_smtlib2())
                .collect::<Vec<String>>()
                .join("\n"),
            condition_constraints
                .iter()
                .map(|constraint| Assert::new(constraint).as_smtlib2())
                .collect::<Vec<String>>()
                .join("\n"),
            Assert::new(&constraint!(
                "=",
                condition_value,
                constraint!("bool", true)
            ))
            .as_smtlib2()
        );
        match solve(&source_code) {
            SolverResult::Sat(example) => {
                info!("sat");
                info!("truthly example:\n{}", example);
            }
            SolverResult::Unsat => {
                info!("unsat");
                is_always_false_unsat = true;
                errors.push(AnalysysError::new(format!("Always false"), rule))
            }
            SolverResult::Unknown => errors.push(AnalysysError::new(
                format!("Static analysis failed because this conditions are too complex."),
                rule,
            )),
        }
    }

    let check_limit_mode = true;

    if is_always_false_unsat == false && check_limit_mode {
        // 1MB limit
        {
            info!("check 1MB limit");
            let source_code = format!(
                "{}

{}

{}
{}
",
                ctx.declarations
                    .borrow()
                    .iter()
                    .map(|declaration| declaration.as_smtlib2())
                    .collect::<Vec<String>>()
                    .join("\n"),
                condition_constraints
                    .iter()
                    .map(|constraint| Assert::new(constraint).as_smtlib2())
                    .collect::<Vec<String>>()
                    .join("\n"),
                Assert::new(&constraint!(
                    "=",
                    condition_value,
                    constraint!("bool", true)
                ))
                .as_smtlib2(),
                Assert::new(&constraint!(
                    ">",
                    constraint!(
                        "list-sum",
                        Symbol {
                            smtlib2: "request_resource_data_inner".to_string()
                        }
                    ),
                    1024 * 1024
                ))
                .as_smtlib2()
            );
            match solve(&source_code) {
                SolverResult::Sat(example) => {
                    errors.push(AnalysysError::new(format!("over 1MB limit"), rule));
                    info!("sat");
                    info!("truthly example:\n{}", example);
                }
                SolverResult::Unsat => {
                    info!("unsat");
                }
                SolverResult::Unknown => errors.push(AnalysysError::new(
                    format!("Static analysis failed because this conditions are too complex."),
                    rule,
                )),
            }
        }
    }

    errors
}

fn check_rule_group(ctx: &AnalysysGlobalContext, rule_group: &RuleGroup) -> Vec<AnalysysError> {
    rule_group
        .rules
        .iter()
        .map(|rule| check_rule(ctx, rule))
        .flatten()
        .chain(
            rule_group
                .rule_groups
                .iter()
                .map(|rule_group| check_rule_group(ctx, rule_group))
                .flatten(),
        )
        .collect()
}

pub fn analyze(ctx: &AnalysysGlobalContext, ast: &crate::ast::Ast) -> Vec<AnalysysError> {
    ast.tree
        .services
        .iter()
        .map(|service| {
            service
                .rule_groups
                .iter()
                .map(|rule_group| check_rule_group(ctx, rule_group))
                .flatten()
        })
        .flatten()
        .collect()
}
