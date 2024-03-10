use crate::ast::Node;

use super::z3::{Constraint, Declaration, Sort, Symbol};

pub fn destruct_null(refl_sym: &Symbol) -> Constraint {
    Constraint::new2("=", refl_sym, &Constraint::mono("null"))
}

pub fn destruct_float(refl_sym: &Symbol) -> Constraint {
    Constraint::new2("=", refl_sym, &Constraint::mono("float"))
}

pub fn destruct_duration(refl_sym: &Symbol) -> Constraint {
    Constraint::new2("=", refl_sym, &Constraint::mono("duration"))
}

pub fn destruct_latlng(refl_sym: &Symbol) -> Constraint {
    Constraint::new2("=", refl_sym, &Constraint::mono("latlng"))
}

pub fn destruct_timestamp(refl_sym: &Symbol) -> Constraint {
    Constraint::new2("=", refl_sym, &Constraint::mono("timestamp"))
}

pub fn destruct_path(refl_sym: &Symbol) -> Constraint {
    Constraint::new2("=", refl_sym, &Constraint::mono("path"))
}

pub fn destruct_bool(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Constraint) {
    let dest_value = Symbol::new(expr, "bool");
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
    let dest_value = Symbol::new(expr, "bytes");
    let dest_bytes_sym = Symbol::new(expr, "bytes_bytes");
    declarations.push(Declaration::new(&dest_value, &Sort::String));
    declarations.push(Declaration::new(&dest_bytes_sym, &Sort::Int));
    (
        dest_value.clone(),
        dest_bytes_sym.clone(),
        Constraint::new2(
            "and",
            &Constraint::new2(">=", &dest_bytes_sym, &0),
            &Constraint::new2(
                "=",
                refl_sym,
                &Constraint::new2("bytes", &dest_value, &dest_bytes_sym),
            ),
        ),
    )
}

pub fn destruct_int(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Constraint) {
    let dest_value = Symbol::new(expr, "int");
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
    let dest_value = Symbol::new(expr, "list");
    let dest_bytes_sym = Symbol::new(expr, "list_bytes");
    declarations.push(Declaration::new(
        &dest_value,
        &Sort::List(Box::new(Sort::Refl)),
    ));
    declarations.push(Declaration::new(&dest_bytes_sym, &Sort::Int));
    (
        dest_value.clone(),
        dest_bytes_sym.clone(),
        Constraint::new2(
            "and",
            &Constraint::new2(">=", &dest_bytes_sym, &0),
            &Constraint::new2(
                "=",
                refl_sym,
                &Constraint::new2("list", &dest_value, &dest_bytes_sym),
            ),
        ),
    )
}

pub fn destruct_map(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Constraint) {
    let dest_value = Symbol::new(expr, "map");
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
) -> (Symbol, Symbol, Constraint) {
    let dest_lvalue = Symbol::new(expr, "mapdiff_l");
    let dest_rvalue = Symbol::new(expr, "mapdiff_r");
    declarations.push(Declaration::new(&dest_lvalue, &Sort::Map));
    declarations.push(Declaration::new(&dest_rvalue, &Sort::Map));
    (
        dest_lvalue.clone(),
        dest_rvalue.clone(),
        Constraint::new2(
            "=",
            refl_sym,
            &Constraint::new2("mapdiff", &dest_lvalue, &dest_rvalue),
        ),
    )
}

pub fn destruct_set(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Symbol, Constraint) {
    let dest_value = Symbol::new(expr, "set");
    let dest_bytes_sym = Symbol::new(expr, "set_bytes");
    declarations.push(Declaration::new(
        &dest_value,
        &Sort::List(Box::new(Sort::Refl)),
    ));
    declarations.push(Declaration::new(&dest_bytes_sym, &Sort::Int));
    (
        dest_value.clone(),
        dest_bytes_sym.clone(),
        Constraint::new2(
            "and",
            &Constraint::new2(">=", &dest_bytes_sym, &0),
            &Constraint::new2(
                "=",
                refl_sym,
                &Constraint::new2("set", &dest_value, &dest_bytes_sym),
            ),
        ),
    )
}

pub fn destruct_string(
    refl_sym: &Symbol,
    expr: &dyn Node,
    declarations: &mut Vec<Declaration>,
) -> (Symbol, Symbol, Constraint) {
    let dest_value = Symbol::new(expr, "str");
    let dest_bytes_sym = Symbol::new(expr, "str_bytes");
    declarations.push(Declaration::new(&dest_value, &Sort::String));
    declarations.push(Declaration::new(&dest_bytes_sym, &Sort::Int));
    (
        dest_value.clone(),
        dest_bytes_sym.clone(),
        Constraint::new2(
            "and",
            &Constraint::new2(">=", &dest_bytes_sym, &0),
            &Constraint::new2(
                "=",
                refl_sym,
                &Constraint::new2("str", &dest_value, &dest_bytes_sym),
            ),
        ),
    )
}
