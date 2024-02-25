use crate::{
    ast::{BinaryLiteral, Node},
    ty::FunctionKind,
};

use super::{
    destruct_sort::{
        destruct_bool, destruct_bytes, destruct_int, destruct_list, destruct_map, destruct_set,
        destruct_string,
    },
    types::{AnalysysContext, Res},
    z3::{Constraint, Declaration, Sort, Symbol},
};

pub fn check_function_calling(
    cur_expr: &dyn Node,
    ctx: &AnalysysContext,
    func: &FunctionKind,
    args: &Vec<&Res>,
    cur_value: &Symbol,
    declarations: &mut Vec<Declaration>,
) -> Vec<Constraint> {
    // FIXME: Because most functions crash when arguments are evaluated and fail, constraint is assigned first as a precondition.
    let mut constraints: Vec<Constraint> = args
        .iter()
        .flat_map(|res| res.constraints.clone())
        .collect();
    match func {
        FunctionKind::Function(fn_name) => match fn_name.as_str() {
            // bytes, list, map, set, string
            "size" => {
                let [obj_val] = args[..] else { panic!() };

                let (obj_bytes_val, obj_bytes_bytes, obj_bytes_constraint) =
                    destruct_bytes(&obj_val.value, cur_expr, declarations);
                let (obj_list_val, obj_list_bytes, obj_list_constraint) =
                    destruct_list(&obj_val.value, cur_expr, declarations);
                let (obj_map_val, obj_map_constraint) =
                    destruct_map(&obj_val.value, cur_expr, declarations);
                let (obj_set_val, obj_set_bytes, obj_set_constraint) =
                    destruct_set(&obj_val.value, cur_expr, declarations);
                let (obj_string_val, obj_string_bytes, obj_string_constraint) =
                    destruct_string(&obj_val.value, cur_expr, declarations);

                let (cur_inner_val, cur_constraint) =
                    destruct_int(&cur_value, cur_expr, declarations);

                constraints.push(cur_constraint);
                constraints.push(Constraint::new5(
                    "or",
                    &Constraint::new2(
                        "and",
                        &obj_bytes_constraint,
                        &Constraint::new2("=", &cur_inner_val, &obj_bytes_bytes),
                    ),
                    &Constraint::new2(
                        "and",
                        &obj_list_constraint,
                        &Constraint::new2(
                            "<=",
                            &cur_inner_val,
                            &Constraint::new1("refl-list-len", &obj_list_val),
                        ),
                    ),
                    &Constraint::new2(
                        "and",
                        &obj_map_constraint,
                        &Constraint::new2(
                            "<=",
                            &cur_inner_val,
                            &Constraint::new1("list-len", &obj_map_val),
                        ),
                    ),
                    &Constraint::new2(
                        "and",
                        &obj_set_constraint,
                        &Constraint::new2(
                            "<=",
                            &cur_inner_val,
                            &Constraint::new1("refl-list-len", &obj_set_val),
                        ),
                    ),
                    &Constraint::new2(
                        "and",
                        &obj_string_constraint,
                        &Constraint::new2(
                            ">",
                            &Constraint::new2("*", &cur_inner_val, &4),
                            &obj_string_bytes,
                        ),
                    ),
                ));
                constraints
            }
            // bytes
            "toHexString" => {
                let [obj_val] = args[..] else { panic!() };
                let (_, obj_inner_bytes, obj_constraint) =
                    destruct_bytes(&obj_val.value, cur_expr, declarations);
                let (_, cur_inner_bytes, cur_constraint) =
                    destruct_string(&cur_value, cur_expr, declarations);
                constraints.extend([
                    obj_constraint,
                    cur_constraint,
                    Constraint::new2(
                        "=",
                        &cur_inner_bytes,
                        &Constraint::new2("*", &obj_inner_bytes, &2),
                    ),
                ]);
                constraints
            }
            "toBase64" => {
                let [obj_val] = args[..] else { panic!() };
                let (_, obj_inner_bytes, obj_constraint) =
                    destruct_bytes(&obj_val.value, cur_expr, declarations);
                let (_, cur_inner_bytes, cur_constraint) =
                    destruct_string(&cur_value, cur_expr, declarations);
                constraints.extend([
                    obj_constraint,
                    cur_constraint,
                    Constraint::new2(
                        "=",
                        &cur_inner_bytes,
                        &Constraint::new2(
                            "*",
                            &4,
                            &Constraint::new2(
                                "div",
                                &Constraint::new2("+", &obj_inner_bytes, &3),
                                &3,
                            ),
                        ),
                    ),
                ]);
                constraints
            }
            // list, set
            "hasOnly" => {
                let [target_val, keys_val] = args[..] else {
                    panic!()
                };
                let (target_list_val, _, target_list_constraint) =
                    destruct_list(&target_val.value, cur_expr, declarations);
                let (target_set_val, _, target_set_constraint) =
                    destruct_set(&target_val.value, cur_expr, declarations);
                let (keys_list_val, _, keys_constraint) =
                    destruct_list(&keys_val.value, cur_expr, declarations);
                let (cur_inner_val, cur_constraint) =
                    destruct_bool(&cur_value, cur_expr, declarations);
                constraints.push(Constraint::new2(
                    "or",
                    &Constraint::new4(
                        "and",
                        &target_list_constraint,
                        &keys_constraint,
                        &cur_constraint,
                        &Constraint::new2(
                            "=",
                            &cur_inner_val,
                            &Constraint::new2(
                                if ctx.quick_mode {
                                    "="
                                } else {
                                    "refl-list-in-refl-list"
                                },
                                &target_list_val,
                                &keys_list_val,
                            ),
                        ),
                    ),
                    &Constraint::new4(
                        "and",
                        &target_set_constraint,
                        &keys_constraint,
                        &cur_constraint,
                        &Constraint::new2(
                            "=",
                            &cur_inner_val,
                            &Constraint::new2(
                                "refl-list-in-refl-list",
                                &target_set_val,
                                &keys_list_val,
                            ),
                        ),
                    ),
                ));
                constraints
            }
            "hasAll" => {
                let [target_val, keys_val] = args[..] else {
                    panic!()
                };
                let (target_list_val, _, target_list_constraint) =
                    destruct_list(&target_val.value, cur_expr, declarations);
                let (target_set_val, _, target_set_constraint) =
                    destruct_set(&target_val.value, cur_expr, declarations);
                let (keys_list_val, _, keys_constraint) =
                    destruct_list(&keys_val.value, cur_expr, declarations);
                let (cur_inner_val, cur_constraint) =
                    destruct_bool(&cur_value, cur_expr, declarations);
                constraints.push(Constraint::new2(
                    "or",
                    &Constraint::new4(
                        "and",
                        &target_list_constraint,
                        &keys_constraint,
                        &cur_constraint,
                        &Constraint::new2(
                            "=",
                            &cur_inner_val,
                            &Constraint::new2(
                                "refl-list-in-refl-list",
                                &keys_list_val,
                                &target_list_val,
                            ),
                        ),
                    ),
                    &Constraint::new4(
                        "and",
                        &target_set_constraint,
                        &keys_constraint,
                        &cur_constraint,
                        &Constraint::new2(
                            "=",
                            &cur_inner_val,
                            &Constraint::new2(
                                "refl-list-in-refl-list",
                                &keys_list_val,
                                &target_set_val,
                            ),
                        ),
                    ),
                ));
                constraints
            }
            "hasAny" => {
                let [target_val, keys_val] = args[..] else {
                    panic!()
                };
                let (target_list_val, _, target_list_constraint) =
                    destruct_list(&target_val.value, cur_expr, declarations);
                let (target_set_val, _, target_set_constraint) =
                    destruct_set(&target_val.value, cur_expr, declarations);
                let (keys_list_val, _, keys_constraint) =
                    destruct_list(&keys_val.value, cur_expr, declarations);
                let (cur_inner_val, cur_constraint) =
                    destruct_bool(&cur_value, cur_expr, declarations);
                constraints.push(Constraint::new2(
                    "or",
                    &Constraint::new4(
                        "and",
                        &target_list_constraint,
                        &keys_constraint,
                        &cur_constraint,
                        &Constraint::new2(
                            "=",
                            &cur_inner_val,
                            &Constraint::new2(
                                "refl-list-is-not-exclusive",
                                &keys_list_val,
                                &target_list_val,
                            ),
                        ),
                    ),
                    &Constraint::new4(
                        "and",
                        &target_set_constraint,
                        &keys_constraint,
                        &cur_constraint,
                        &Constraint::new2(
                            "=",
                            &cur_inner_val,
                            &Constraint::new2(
                                "refl-list-is-not-exclusive",
                                &keys_list_val,
                                &target_set_val,
                            ),
                        ),
                    ),
                ));
                constraints
            }
            // list
            "concat" => {
                let [obj1_val, obj2_val] = args[..] else {
                    panic!()
                };
                let (_, obj1_inner_bytes, obj1_constraint) =
                    destruct_list(&obj1_val.value, cur_expr, declarations);
                let (_, obj2_inner_bytes, obj2_constraint) =
                    destruct_list(&obj2_val.value, cur_expr, declarations);
                let (_, cur_inner_bytes, cur_constraint) =
                    destruct_string(&cur_value, cur_expr, declarations);
                constraints.extend([
                    obj1_constraint,
                    obj2_constraint,
                    cur_constraint,
                    Constraint::new2(
                        "=",
                        &cur_inner_bytes,
                        &Constraint::new2("+", &obj1_inner_bytes, &obj2_inner_bytes),
                    ),
                ]);
                constraints
            }
            "join" => {
                let [obj_res, param_res] = args[..] else {
                    panic!()
                };
                let (_, obj_inner_bytes, obj_constraint) =
                    destruct_list(&obj_res.value, cur_expr, declarations);
                let (_, _, param_constraint) =
                    destruct_string(&param_res.value, cur_expr, declarations);
                let (_, cur_inner_bytes, cur_constraint) =
                    destruct_string(&cur_value, cur_expr, declarations);
                constraints.extend([
                    obj_constraint,
                    param_constraint,
                    cur_constraint,
                    Constraint::new2(">", &cur_inner_bytes, &obj_inner_bytes),
                ]);
                constraints
            }
            "removeAll" => {
                let [obj1_val, obj2_val] = args[..] else {
                    panic!()
                };
                let (_, obj1_inner_bytes, obj1_constraint) =
                    destruct_list(&obj1_val.value, cur_expr, declarations);
                let (_, _, obj2_constraint) =
                    destruct_list(&obj2_val.value, cur_expr, declarations);
                let (_, cur_inner_bytes, cur_constraint) =
                    destruct_string(&cur_value, cur_expr, declarations);
                constraints.extend([
                    obj1_constraint,
                    obj2_constraint,
                    cur_constraint,
                    Constraint::new2("<=", &cur_inner_bytes, &obj1_inner_bytes),
                ]);
                constraints
            }
            "toSet" => {
                let [obj1_val] = args[..] else { panic!() };
                let (obj1_inner_val, obj1_inner_bytes, obj1_constraint) =
                    destruct_list(&obj1_val.value, cur_expr, declarations);
                let (cur_inner_val, cur_inner_bytes, cur_constraint) =
                    destruct_string(&cur_value, cur_expr, declarations);
                constraints.extend([
                    obj1_constraint,
                    cur_constraint,
                    Constraint::new2("<=", &cur_inner_bytes, &obj1_inner_bytes),
                    Constraint::new2("refl-list-in-refl-list", &cur_inner_val, &obj1_inner_val),
                ]);
                constraints
            }
            // set
            "difference" => todo!(),
            "intersection" => todo!(),
            "union" => todo!(),
            // string
            "lower" => {
                let [obj_val] = args[..] else { panic!() };
                let (_, obj_inner_bytes, obj_constraint) =
                    destruct_string(&obj_val.value, cur_expr, declarations);
                let (_, cur_inner_bytes, cur_constraint) =
                    destruct_string(&cur_value, cur_expr, declarations);
                constraints.extend([
                    obj_constraint,
                    cur_constraint,
                    Constraint::new2("=", &cur_inner_bytes, &obj_inner_bytes),
                ]);
                constraints
            }
            "matches" => todo!(),
            "replace" => todo!(),
            "split" => todo!(),
            "toUtf8" => {
                let [obj_val] = args[..] else { panic!() };
                let (_, obj_inner_bytes, obj_constraint) =
                    destruct_string(&obj_val.value, cur_expr, declarations);
                let (_, cur_inner_bytes, cur_constraint) =
                    destruct_string(&cur_value, cur_expr, declarations);
                constraints.extend([
                    obj_constraint,
                    cur_constraint,
                    Constraint::new2("=", &cur_inner_bytes, &obj_inner_bytes),
                ]);
                constraints
            }
            "trim" => {
                let [obj_val] = args[..] else { panic!() };
                let (_, obj_inner_bytes, obj_constraint) =
                    destruct_string(&obj_val.value, cur_expr, declarations);
                let (_, cur_inner_bytes, cur_constraint) =
                    destruct_string(&cur_value, cur_expr, declarations);
                constraints.extend([
                    obj_constraint,
                    cur_constraint,
                    Constraint::new2("<=", &cur_inner_bytes, &obj_inner_bytes),
                ]);
                constraints
            }
            "upper" => {
                let [obj_val] = args[..] else { panic!() };
                let (_, obj_inner_bytes, obj_constraint) =
                    destruct_string(&obj_val.value, cur_expr, declarations);
                let (_, cur_inner_bytes, cur_constraint) =
                    destruct_string(&cur_value, cur_expr, declarations);
                constraints.extend([
                    obj_constraint,
                    cur_constraint,
                    Constraint::new2("=", &cur_inner_bytes, &obj_inner_bytes),
                ]);
                constraints
            }
            // map
            "keys" => {
                let [map_val] = args[..] else { panic!() };
                let (map_inner, map_constraint) =
                    destruct_map(&map_val.value, cur_expr, declarations);
                let (cur_inner_value, _, cur_inner_constraint) =
                    destruct_list(&cur_value, cur_expr, declarations);
                constraints.extend([
                    map_constraint,
                    cur_inner_constraint,
                    Constraint::new2(
                        "=",
                        &cur_inner_value,
                        &Constraint::new1("list-keys", &map_inner),
                    ),
                ]);
                constraints
            }
            "diff" => {
                let [left_map_res, right_map_res] = args[..] else {
                    panic!()
                };
                let (left_map_val, left_map_constraint) =
                    destruct_map(&left_map_res.value, cur_expr, declarations);
                let (right_map_val, right_map_constraint) =
                    destruct_map(&right_map_res.value, cur_expr, declarations);
                constraints.extend([
                    left_map_constraint,
                    right_map_constraint,
                    Constraint::new2(
                        "=",
                        cur_value,
                        &Constraint::new2("mapdiff", &left_map_val, &right_map_val),
                    ),
                ]);
                constraints
            }
            "get" => {
                let [obj_res, key_res] = args[..] else {
                    panic!()
                };

                let (key_str_val, _, key_str_constraint) =
                    destruct_string(&obj_res.value, cur_expr, declarations);
                let (obj_map_val, obj_map_constraint) =
                    destruct_map(&obj_res.value, cur_expr, declarations);

                constraints.extend([
                    key_str_constraint,
                    obj_map_constraint,
                    Constraint::new2(
                        "=",
                        cur_value,
                        &Constraint::new2("list-get", &obj_map_val, &key_str_val),
                    ),
                ]);
                constraints
            }
            "values" => {
                let [map_val] = args[..] else { panic!() };
                let (map_inner, map_constraint) =
                    destruct_map(&map_val.value, cur_expr, declarations);
                let (cur_inner_value, _, cur_inner_constraint) =
                    destruct_list(&cur_value, cur_expr, declarations);
                constraints.extend([
                    map_constraint,
                    cur_inner_constraint,
                    Constraint::new2(
                        "=",
                        &cur_inner_value,
                        &Constraint::new1("list-values", &map_inner),
                    ),
                ]);
                constraints
            }
            // timestamp
            "date" | "time" => {
                constraints.push(Constraint::new2(
                    "=",
                    cur_value,
                    &Constraint::mono("timestamp"),
                ));
                constraints
            }
            "day" | "dayOfWeek" | "dayOfYear" | "hours" | "minutes" | "month" | "year"
            | "toMillis" => {
                let [obj_val] = args[..] else { panic!() };
                let (_, cur_constraint) = destruct_int(&cur_value, cur_expr, declarations);
                constraints.extend([
                    Constraint::new2("=", &obj_val.value, &Constraint::mono("timestamp")),
                    cur_constraint,
                ]);
                constraints
            }
            // timestamp, duration
            "nanos" | "seconds" => {
                let [obj_val] = args[..] else { panic!() };
                let (_, cur_constraint) = destruct_int(&cur_value, cur_expr, declarations);
                constraints.extend([
                    Constraint::new2(
                        "or",
                        &Constraint::new2("=", &obj_val.value, &Constraint::mono("timestamp")),
                        &Constraint::new2("=", &obj_val.value, &Constraint::mono("duration")),
                    ),
                    cur_constraint,
                ]);
                constraints
            }
            // mapdiff
            "addedKeys" => todo!(),
            "affectedKeys" => todo!(),
            "changedKeys" => todo!(),
            "removedKeys" => todo!(),
            "unchangedKeys" => todo!(),
            // path
            "bind" => {
                constraints.push(Constraint::new2("=", cur_value, &Constraint::mono("path")));
                constraints
            }
            // latlng
            "distance" | "latitude" | "longitude" => {
                let [obj_val] = args[..] else { panic!() };
                constraints.extend([
                    Constraint::new2("=", cur_value, &Constraint::mono("float")),
                    Constraint::new2("=", &obj_val.value, &Constraint::mono("latlng")),
                ]);
                constraints
            }
            _ => panic!(),
        },
        FunctionKind::UnaryOp(unary_op) => match unary_op {
            crate::ast::UnaryLiteral::Not => {
                let [target] = args[..] else { panic!() };
                let (target_val, target_destruct_constraint) =
                    destruct_bool(&target.value, cur_expr, declarations);

                constraints.push(target_destruct_constraint);
                constraints.push(Constraint::new2(
                    "=",
                    cur_value,
                    &Constraint::new1("bool", &Constraint::new1("not", &target_val)),
                ));
                constraints
            }
            crate::ast::UnaryLiteral::Minus => {
                let [target] = args[..] else { panic!() };
                let (target_int_val, target_int_destruct_constraint) =
                    destruct_int(&target.value, cur_expr, declarations);

                constraints.push(Constraint::new2(
                    "or",
                    &Constraint::new2(
                        "and",
                        &target_int_destruct_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1("int", &Constraint::new1("-", &target_int_val)),
                        ),
                    ),
                    &Constraint::new2("=", cur_value, &Constraint::mono("float")),
                ));
                constraints
            }
        },
        FunctionKind::BinaryOp(binary_op) => match binary_op {
            BinaryLiteral::And => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };
                let (left_val, left_constraint) =
                    destruct_bool(&left_res.value, cur_expr, declarations);
                let (right_val, right_constraint) =
                    destruct_bool(&right_res.value, cur_expr, declarations);

                constraints.push(Constraint::new2(
                    "=",
                    cur_value,
                    &Constraint::new1(
                        "bool",
                        &Constraint::new2(
                            "and",
                            &Constraint::new2("and", &left_val, &left_constraint),
                            &Constraint::new2("and", &right_val, &right_constraint),
                        ),
                    ),
                ));
                constraints
            }
            BinaryLiteral::Or => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };
                let (left_val, left_constraint) =
                    destruct_bool(&left_res.value, cur_expr, declarations);
                let (right_val, right_constraint) =
                    destruct_bool(&right_res.value, cur_expr, declarations);

                vec![Constraint::new2(
                    "=",
                    cur_value,
                    &Constraint::new1(
                        "bool",
                        &Constraint::new2(
                            "or",
                            &Constraint::new3(
                                "and",
                                &left_val,
                                &left_constraint,
                                &Constraint::new("and", args[0].constraints.iter().collect()),
                            ),
                            &Constraint::new3(
                                "and",
                                &right_val,
                                &right_constraint,
                                &Constraint::new("and", args[1].constraints.iter().collect()),
                            ),
                        ),
                    ),
                )]
            }
            BinaryLiteral::Add => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };

                let (left_int_val, left_int_constraint) =
                    destruct_int(&left_res.value, cur_expr, declarations);
                let (left_str_val, left_str_bytes, left_str_constraint) =
                    destruct_string(&left_res.value, cur_expr, declarations);

                let (right_int_val, right_int_constraint) =
                    destruct_int(&right_res.value, cur_expr, declarations);
                let (right_str_val, right_str_bytes, right_str_constraint) =
                    destruct_string(&right_res.value, cur_expr, declarations);

                constraints.push(Constraint::new3(
                    "or",
                    &Constraint::new3(
                        "and",
                        &left_int_constraint,
                        &right_int_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "int",
                                &Constraint::new2("+", &left_int_val, &right_int_val),
                            ),
                        ),
                    ),
                    &Constraint::new3(
                        "and",
                        &Constraint::new2("=", cur_value, &Constraint::mono("float")),
                        &Constraint::new2("=", &left_res.value, &Constraint::mono("float")),
                        &Constraint::new2("=", &right_res.value, &Constraint::mono("float")),
                    ),
                    &Constraint::new3(
                        "and",
                        &left_str_constraint,
                        &right_str_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new2(
                                "str",
                                &Constraint::new2("str.++", &left_str_val, &right_str_val),
                                &Constraint::new2("+", &left_str_bytes, &right_str_bytes),
                            ),
                        ),
                    ),
                ));
                constraints
            }
            BinaryLiteral::Sub => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };

                let (left_int_val, left_int_constraint) =
                    destruct_int(&left_res.value, cur_expr, declarations);

                let (right_int_val, right_int_constraint) =
                    destruct_int(&right_res.value, cur_expr, declarations);

                constraints.push(Constraint::new2(
                    "or",
                    &Constraint::new3(
                        "and",
                        &left_int_constraint,
                        &right_int_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "int",
                                &Constraint::new2("-", &left_int_val, &right_int_val),
                            ),
                        ),
                    ),
                    &Constraint::new3(
                        "and",
                        &Constraint::new2("=", cur_value, &Constraint::mono("float")),
                        &Constraint::new2("=", &left_res.value, &Constraint::mono("float")),
                        &Constraint::new2("=", &right_res.value, &Constraint::mono("float")),
                    ),
                ));
                constraints
            }
            BinaryLiteral::Mul => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };

                let (left_int_val, left_int_constraint) =
                    destruct_int(&left_res.value, cur_expr, declarations);

                let (right_int_val, right_int_constraint) =
                    destruct_int(&right_res.value, cur_expr, declarations);

                constraints.push(Constraint::new2(
                    "or",
                    &Constraint::new3(
                        "and",
                        &left_int_constraint,
                        &right_int_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "int",
                                &Constraint::new2("*", &left_int_val, &right_int_val),
                            ),
                        ),
                    ),
                    &Constraint::new3(
                        "and",
                        &Constraint::new2("=", cur_value, &Constraint::mono("float")),
                        &Constraint::new2("=", &left_res.value, &Constraint::mono("float")),
                        &Constraint::new2("=", &right_res.value, &Constraint::mono("float")),
                    ),
                ));
                constraints
            }
            BinaryLiteral::Div => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };

                let (left_int_val, left_int_constraint) =
                    destruct_int(&left_res.value, cur_expr, declarations);

                let (right_int_val, right_int_constraint) =
                    destruct_int(&right_res.value, cur_expr, declarations);

                constraints.push(Constraint::new2(
                    "or",
                    &Constraint::new3(
                        "and",
                        &left_int_constraint,
                        &right_int_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "int",
                                &Constraint::new2("div", &left_int_val, &right_int_val),
                            ),
                        ),
                    ),
                    &Constraint::new3(
                        "and",
                        &Constraint::new2("=", cur_value, &Constraint::mono("float")),
                        &Constraint::new2("=", &left_res.value, &Constraint::mono("float")),
                        &Constraint::new2("=", &right_res.value, &Constraint::mono("float")),
                    ),
                ));
                constraints
            }
            BinaryLiteral::Mod => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };

                let (left_int_val, left_int_constraint) =
                    destruct_int(&left_res.value, cur_expr, declarations);

                let (right_int_val, right_int_constraint) =
                    destruct_int(&right_res.value, cur_expr, declarations);

                constraints.push(Constraint::new2(
                    "or",
                    &Constraint::new3(
                        "and",
                        &left_int_constraint,
                        &right_int_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "int",
                                &Constraint::new2("mod", &left_int_val, &right_int_val),
                            ),
                        ),
                    ),
                    &Constraint::new3(
                        "and",
                        &Constraint::new2("=", cur_value, &Constraint::mono("float")),
                        &Constraint::new2("=", &left_res.value, &Constraint::mono("float")),
                        &Constraint::new2("=", &right_res.value, &Constraint::mono("float")),
                    ),
                ));
                constraints
            }
            BinaryLiteral::Gt => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };

                let (left_int_val, left_int_constraint) =
                    destruct_int(&left_res.value, cur_expr, declarations);
                let (left_str_val, _, left_str_constraint) =
                    destruct_string(&left_res.value, cur_expr, declarations);

                let (right_int_val, right_int_constraint) =
                    destruct_int(&right_res.value, cur_expr, declarations);
                let (right_str_val, _, right_str_constraint) =
                    destruct_string(&right_res.value, cur_expr, declarations);

                constraints.push(Constraint::new3(
                    "or",
                    &Constraint::new3(
                        "and",
                        &left_int_constraint,
                        &right_int_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "bool",
                                &Constraint::new2(">", &left_int_val, &right_int_val),
                            ),
                        ),
                    ),
                    &Constraint::new3(
                        "and",
                        &Constraint::new2("=", cur_value, &Constraint::mono("float")),
                        &Constraint::new2("=", &left_res.value, &Constraint::mono("float")),
                        &Constraint::new2("=", &right_res.value, &Constraint::mono("float")),
                    ),
                    &Constraint::new3(
                        "and",
                        &left_str_constraint,
                        &right_str_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "bool",
                                &Constraint::new2("str.<", &right_str_val, &left_str_val),
                            ),
                        ),
                    ),
                ));
                constraints
            }
            BinaryLiteral::Gte => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };

                let (left_int_val, left_int_constraint) =
                    destruct_int(&left_res.value, cur_expr, declarations);
                let (left_str_val, _, left_str_constraint) =
                    destruct_string(&left_res.value, cur_expr, declarations);

                let (right_int_val, right_int_constraint) =
                    destruct_int(&right_res.value, cur_expr, declarations);
                let (right_str_val, _, right_str_constraint) =
                    destruct_string(&right_res.value, cur_expr, declarations);

                constraints.push(Constraint::new3(
                    "or",
                    &Constraint::new3(
                        "and",
                        &left_int_constraint,
                        &right_int_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "bool",
                                &Constraint::new2(">=", &left_int_val, &right_int_val),
                            ),
                        ),
                    ),
                    &Constraint::new3(
                        "and",
                        &Constraint::new2("=", cur_value, &Constraint::mono("float")),
                        &Constraint::new2("=", &left_res.value, &Constraint::mono("float")),
                        &Constraint::new2("=", &right_res.value, &Constraint::mono("float")),
                    ),
                    &Constraint::new3(
                        "and",
                        &left_str_constraint,
                        &right_str_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "bool",
                                &Constraint::new2("str.<=", &right_str_val, &left_str_val),
                            ),
                        ),
                    ),
                ));
                constraints
            }
            BinaryLiteral::Lt => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };

                let (left_int_val, left_int_constraint) =
                    destruct_int(&left_res.value, cur_expr, declarations);
                let (left_str_val, _, left_str_constraint) =
                    destruct_string(&left_res.value, cur_expr, declarations);

                let (right_int_val, right_int_constraint) =
                    destruct_int(&right_res.value, cur_expr, declarations);
                let (right_str_val, _, right_str_constraint) =
                    destruct_string(&right_res.value, cur_expr, declarations);

                constraints.push(Constraint::new3(
                    "or",
                    &Constraint::new3(
                        "and",
                        &left_int_constraint,
                        &right_int_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "bool",
                                &Constraint::new2("<", &left_int_val, &right_int_val),
                            ),
                        ),
                    ),
                    &Constraint::new3(
                        "and",
                        &Constraint::new2("=", cur_value, &Constraint::mono("float")),
                        &Constraint::new2("=", &left_res.value, &Constraint::mono("float")),
                        &Constraint::new2("=", &right_res.value, &Constraint::mono("float")),
                    ),
                    &Constraint::new3(
                        "and",
                        &left_str_constraint,
                        &right_str_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "bool",
                                &Constraint::new2("str.<", &left_str_val, &right_str_val),
                            ),
                        ),
                    ),
                ));
                constraints
            }
            BinaryLiteral::Lte => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };

                let (left_int_val, left_int_constraint) =
                    destruct_int(&left_res.value, cur_expr, declarations);
                let (left_str_val, _, left_str_constraint) =
                    destruct_string(&left_res.value, cur_expr, declarations);

                let (right_int_val, right_int_constraint) =
                    destruct_int(&right_res.value, cur_expr, declarations);
                let (right_str_val, _, right_str_constraint) =
                    destruct_string(&right_res.value, cur_expr, declarations);

                constraints.push(Constraint::new3(
                    "or",
                    &Constraint::new3(
                        "and",
                        &left_int_constraint,
                        &right_int_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "bool",
                                &Constraint::new2("<=", &left_int_val, &right_int_val),
                            ),
                        ),
                    ),
                    &Constraint::new3(
                        "and",
                        &Constraint::new2("=", cur_value, &Constraint::mono("float")),
                        &Constraint::new2("=", &left_res.value, &Constraint::mono("float")),
                        &Constraint::new2("=", &right_res.value, &Constraint::mono("float")),
                    ),
                    &Constraint::new3(
                        "and",
                        &left_str_constraint,
                        &right_str_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "bool",
                                &Constraint::new2("str.<=", &left_str_val, &right_str_val),
                            ),
                        ),
                    ),
                ));
                constraints
            }
            BinaryLiteral::Eq => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };
                constraints.push(Constraint::new2(
                    "=",
                    cur_value,
                    &Constraint::new1(
                        "bool",
                        &Constraint::new2("=", &left_res.value, &right_res.value),
                    ),
                ));
                constraints
            }
            BinaryLiteral::NotEq => {
                let [left_res, right_res] = args[..] else {
                    panic!()
                };
                constraints.push(Constraint::new2(
                    "=",
                    cur_value,
                    &Constraint::new1(
                        "bool",
                        &Constraint::new1(
                            "not",
                            &Constraint::new2("=", &left_res.value, &right_res.value),
                        ),
                    ),
                ));
                constraints
            }
            BinaryLiteral::In => {
                let [obj_res, key_res] = args[..] else {
                    panic!()
                };

                let (obj_map_val, obj_map_constraint) =
                    destruct_map(&obj_res.value, cur_expr, declarations);
                let (key_str_val, _, key_str_constraint) =
                    destruct_string(&key_res.value, cur_expr, declarations);

                let (obj_list_val, _, obj_list_constraint) =
                    destruct_list(&obj_res.value, cur_expr, declarations);

                let (obj_set_val, _, obj_set_constraint) =
                    destruct_set(&obj_res.value, cur_expr, declarations);

                let normal = &Constraint::new3(
                    "and",
                    &obj_map_constraint,
                    &key_str_constraint,
                    &Constraint::new2(
                        "=",
                        cur_value,
                        &Constraint::new1(
                            "bool",
                            &Constraint::new2("list-exists", &obj_map_val, &key_str_val),
                        ),
                    ),
                );

                let quick = &Constraint::new4(
                    "and",
                    &obj_map_constraint,
                    &key_str_constraint,
                    &Constraint::new2("=", cur_value, &Constraint::new1("bool", &true)),
                    &Constraint::new2("list-exists", &obj_map_val, &key_str_val),
                );

                constraints.push(Constraint::new3(
                    "or",
                    if ctx.quick_mode { quick } else { normal },
                    &Constraint::new2(
                        "and",
                        &obj_list_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "bool",
                                &Constraint::new2(
                                    "refl-list-exists",
                                    &obj_list_val,
                                    &key_res.value,
                                ),
                            ),
                        ),
                    ),
                    &Constraint::new2(
                        "and",
                        &obj_set_constraint,
                        &Constraint::new2(
                            "=",
                            cur_value,
                            &Constraint::new1(
                                "bool",
                                &Constraint::new2("refl-list-exists", &obj_set_val, &key_res.value),
                            ),
                        ),
                    ),
                ));
                constraints
            }
        },
        FunctionKind::Subscript => {
            let [obj_res, key_res] = args[..] else {
                panic!()
            };

            let (key_str_val, _, key_str_constraint) =
                destruct_string(&key_res.value, cur_expr, declarations);

            let (key_int_val, _, key_int_constraint) =
                destruct_string(&key_res.value, cur_expr, declarations);

            let (obj_list_val, _, obj_list_constraint) =
                destruct_list(&obj_res.value, cur_expr, declarations);

            let (obj_map_val, obj_map_constraint) =
                destruct_map(&obj_res.value, cur_expr, declarations);

            let (obj_str_val, _, obj_str_constraint) =
                destruct_string(&obj_res.value, cur_expr, declarations);

            constraints.push(Constraint::new5(
                "or",
                &Constraint::new3(
                    "and",
                    &key_int_constraint,
                    &obj_list_constraint,
                    &Constraint::new2(
                        "=",
                        cur_value,
                        &Constraint::new2("refl-list-at", &obj_list_val, &key_int_val),
                    ),
                ),
                &Constraint::new3(
                    "and",
                    &key_str_constraint,
                    &obj_map_constraint,
                    &Constraint::new2(
                        "=",
                        cur_value,
                        &Constraint::new2("list-get", &obj_map_val, &key_str_val),
                    ),
                ),
                &Constraint::new2(
                    "and",
                    &key_str_constraint,
                    &Constraint::new2("=", cur_value, &Constraint::mono("path")),
                ),
                &Constraint::new2(
                    "and",
                    &key_int_constraint,
                    &Constraint::new2("=", cur_value, &Constraint::mono("path")),
                ),
                &Constraint::new3(
                    "and",
                    &key_int_constraint,
                    &obj_str_constraint,
                    &Constraint::new2(
                        "=",
                        cur_value,
                        &Constraint::new2("str.at", &obj_str_val, &key_int_val),
                    ),
                ),
            ));
            constraints
        }
        FunctionKind::SubscriptRange => {
            let [obj_res, from_res, to_res] = args[..] else {
                panic!()
            };

            let (from_int_val, from_int_constraint) =
                destruct_int(&from_res.value, cur_expr, declarations);

            let (to_int_val, to_int_constraint) =
                destruct_int(&to_res.value, cur_expr, declarations);

            let (obj_list_val, obj_list_bytes, obj_list_constraint) =
                destruct_list(&obj_res.value, cur_expr, declarations);

            let list_bytes_sym = Symbol::new(cur_expr, "subscript_bytes");
            declarations.push(Declaration::new(&list_bytes_sym, &Sort::Int));

            let (obj_str_val, _, obj_str_constraint) =
                destruct_string(&obj_res.value, cur_expr, declarations);

            constraints.push(Constraint::new2(
                "or",
                &Constraint::new5(
                    "and",
                    &from_int_constraint,
                    &to_int_constraint,
                    &obj_list_constraint,
                    &Constraint::new2(
                        "=",
                        cur_value,
                        &Constraint::new2(
                            "list",
                            &Constraint::new3(
                                "refl-list-range",
                                &obj_list_val,
                                &from_int_val,
                                &Constraint::new2("-", &to_int_val, &from_int_val),
                            ),
                            &list_bytes_sym,
                        ),
                    ),
                    &Constraint::new2("<=", &list_bytes_sym, &obj_list_bytes),
                ),
                &Constraint::new4(
                    "and",
                    &from_int_constraint,
                    &to_int_constraint,
                    &obj_str_constraint,
                    &Constraint::new2(
                        "=",
                        cur_value,
                        &Constraint::new2(
                            "str",
                            &Constraint::new3(
                                "str.substr",
                                &obj_list_val,
                                &from_int_val,
                                &Constraint::new2("-", &to_int_val, &from_int_val),
                            ),
                            &Constraint::new2(
                                "*",
                                &Constraint::new2("-", &to_int_val, &from_int_val),
                                &4,
                            ),
                        ),
                    ),
                ),
            ));
            constraints
        }
    }
}
