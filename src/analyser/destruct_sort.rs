use crate::ast::Node;

use super::z3::{Constraint, Declaration, Sort, Symbol};

pub fn destruct_bool(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Constraint) {
    let dest_value = Symbol::new(expr);
    declarations.push(Declaration::new(&dest_value, &Sort::Bool));
    (
        dest_value.clone(),
        Constraint::new2("=", refl_sym, &Constraint::new1("bool", &dest_value)),
    )
}

pub fn destruct_bytes(
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
        Constraint::new2(
            "=",
            refl_sym,
            &Constraint::new2("bytes", &dest_value, &dest_bytes_sym),
        ),
    )
}

pub fn destruct_int(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Constraint) {
    let dest_value = Symbol::new(expr);
    declarations.push(Declaration::new(&dest_value, &Sort::Int));
    (
        dest_value.clone(),
        Constraint::new2("=", refl_sym, &Constraint::new1("int", &dest_value)),
    )
}

pub fn destruct_list(
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
        Constraint::new2(
            "=",
            refl_sym,
            &Constraint::new2("list", &dest_value, &dest_bytes_sym),
        ),
    )
}

pub fn destruct_map(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Constraint) {
    let dest_value = Symbol::new(expr);
    declarations.push(Declaration::new(&dest_value, &Sort::Map));
    (
        dest_value.clone(),
        Constraint::new2("=", refl_sym, &Constraint::new1("map", &dest_value)),
    )
}

pub fn destruct_mapdiff(
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
        Constraint::new2(
            "=",
            refl_sym,
            &Constraint::new3("mapdiff", &dest_lvalue, &dest_rvalue, &dest_bytes_sym),
        ),
    )
}

pub fn destruct_set(
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
        Constraint::new2(
            "=",
            refl_sym,
            &Constraint::new2("set", &dest_value, &dest_bytes_sym),
        ),
    )
}

pub fn destruct_string(
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
        Constraint::new2(
            "=",
            refl_sym,
            &Constraint::new2("str", &dest_value, &dest_bytes_sym),
        ),
    )
}
