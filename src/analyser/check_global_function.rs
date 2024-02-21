use crate::ast::Node;

use super::{
    destruct_sort::{
        destruct_bool, destruct_bytes, destruct_duration, destruct_float, destruct_int,
        destruct_latlng, destruct_map, destruct_null, destruct_path, destruct_string,
        destruct_timestamp,
    },
    types::{AnalysysContext, Res},
    z3::{Constraint, Declaration, Sort, Symbol},
};

pub fn check_global_function_calling(
    cur_expr: &dyn Node,
    ctx: &AnalysysContext,
    namespace: &Option<String>,
    name: &String,
    args: &Vec<&Res>,
    cur_value: &Symbol,
    declarations: &mut Vec<Declaration>,
) -> Vec<Constraint> {
    // FIXME: Because most functions crash when arguments are evaluated and fail, constraint is assigned first as a precondition.
    let mut constraints: Vec<Constraint> = args
        .iter()
        .flat_map(|res| res.constraints.clone())
        .collect();
    match (namespace.as_deref(), name.as_str()) {
        (None, "debug") => {
            let [param_res] = args[..] else { panic!() };
            // let (_, obj_inner_bytes, obj_constraint) =
            //     destruct_bytes(&obj_val.value, cur_expr, declarations);
            // let (_, cur_inner_bytes, cur_constraint) =
            //     destruct_string(&cur_value, cur_expr, declarations);
            constraints.extend([Constraint::new2("=", &param_res.value, cur_value)]);
            constraints
        }
        (None, "exists") => {
            let [param_res] = args[..] else { panic!() };
            let param_constraint = destruct_path(&param_res.value);
            let (_, cur_constraint) = destruct_bool(&cur_value, cur_expr, declarations);
            constraints.extend([param_constraint, cur_constraint]);
            constraints
        }
        (None, "existsAfter") => {
            let [param_res] = args[..] else { panic!() };
            let param_constraint = destruct_path(&param_res.value);
            let (_, cur_constraint) = destruct_bool(&cur_value, cur_expr, declarations);
            constraints.extend([param_constraint, cur_constraint]);
            constraints
        }
        (None, "get") | (None, "getAfter") => {
            let [param_res] = args[..] else { panic!() };
            let param_constraint = destruct_path(&param_res.value);
            let (cur_val, cur_constraint) = destruct_map(&cur_value, cur_expr, declarations);

            let data_value = Symbol::new(cur_expr);
            let id_value = Symbol::new(cur_expr);
            let name_value = Symbol::new(cur_expr);
            declarations.push(Declaration::new(&data_value, &Sort::Refl));
            declarations.push(Declaration::new(&id_value, &Sort::Refl));
            declarations.push(Declaration::new(&name_value, &Sort::Refl));
            let (_, data_constraint) = destruct_map(&data_value, cur_expr, declarations);
            let (_, _, id_constraint) = destruct_string(&id_value, cur_expr, declarations);
            let name_constraint = destruct_path(&name_value);

            constraints.extend([
                param_constraint,
                cur_constraint,
                data_constraint,
                id_constraint,
                name_constraint,
                Constraint::new2(
                    "=",
                    &data_value,
                    &Constraint::new2("list-get", &cur_val, &"data"),
                ),
                Constraint::new2(
                    "=",
                    &id_value,
                    &Constraint::new2("list-get", &cur_val, &"data"),
                ),
                Constraint::new2(
                    "=",
                    &name_value,
                    &Constraint::new2("list-get", &cur_val, &"data"),
                ),
            ]);
            constraints
        }
        (None, "float") => {
            let [param_res] = args[..] else { panic!() };
            let (_, _, param_is_string_constraint) =
                destruct_string(&param_res.value, cur_expr, declarations);
            let (_, param_is_int_constraint) =
                destruct_int(&param_res.value, cur_expr, declarations);
            let param_is_float_constraint = destruct_float(&param_res.value);
            let cur_constraint = destruct_float(&cur_value);
            constraints.extend([
                Constraint::new3(
                    "or",
                    &param_is_string_constraint,
                    &param_is_int_constraint,
                    &param_is_float_constraint,
                ),
                cur_constraint,
            ]);
            constraints
        }
        (None, "int") => {
            let [param_res] = args[..] else { panic!() };
            let (_, _, param_is_string_constraint) =
                destruct_string(&param_res.value, cur_expr, declarations);
            let (_, param_is_int_constraint) =
                destruct_int(&param_res.value, cur_expr, declarations);
            let param_is_float_constraint = destruct_float(&param_res.value);
            let (_, cur_constraint) = destruct_int(&cur_value, cur_expr, declarations);
            constraints.extend([
                Constraint::new3(
                    "or",
                    &param_is_string_constraint,
                    &param_is_float_constraint,
                    &Constraint::new2(
                        "and",
                        &param_is_int_constraint,
                        &Constraint::new2("=", &param_res.value, cur_value),
                    ),
                ),
                cur_constraint,
            ]);
            constraints
        }
        (None, "string") => {
            let [param_res] = args[..] else { panic!() };
            let (param_as_bool_val, param_is_bool_constraint) =
                destruct_bool(&param_res.value, cur_expr, declarations);
            let param_is_null_constraint = destruct_null(&param_res.value);
            let param_is_path_constraint = destruct_path(&param_res.value);
            let (_, _, param_is_string_constraint) =
                destruct_string(&param_res.value, cur_expr, declarations);
            let (_, param_is_int_constraint) =
                destruct_int(&param_res.value, cur_expr, declarations);
            let param_is_float_constraint = destruct_float(&param_res.value);
            let (_, _, cur_constraint) = destruct_string(&cur_value, cur_expr, declarations);
            constraints.extend([
                Constraint::new6(
                    "or",
                    &Constraint::new2(
                        "and",
                        &param_is_null_constraint,
                        &Constraint::new2("=", &Constraint::new2("string", &"null", &4), cur_value),
                    ),
                    &Constraint::new2(
                        "and",
                        &param_is_bool_constraint,
                        &Constraint::new2(
                            "=",
                            &Constraint::new3(
                                "if",
                                &param_as_bool_val,
                                &Constraint::new2("string", &"true", &4),
                                &Constraint::new2("string", &"false", &5),
                            ),
                            cur_value,
                        ),
                    ),
                    &param_is_path_constraint,
                    &param_is_int_constraint,
                    &param_is_float_constraint,
                    &Constraint::new2(
                        "and",
                        &param_is_string_constraint,
                        &Constraint::new2("=", &param_res.value, cur_value),
                    ),
                ),
                cur_constraint,
            ]);
            constraints
        }
        (Some("duration"), "abs") => {
            let [param_res] = args[..] else { panic!() };
            let param_constraint = destruct_duration(&param_res.value);
            let cur_constraint = destruct_duration(&cur_value);
            constraints.extend([param_constraint, cur_constraint]);
            constraints
        }
        (Some("duration"), "time") => {
            let [param1_res, param2_res, param3_res, param4_res] = args[..] else {
                panic!()
            };
            let (_, param1_constraint) = destruct_int(&param1_res.value, cur_expr, declarations);
            let (_, param2_constraint) = destruct_int(&param2_res.value, cur_expr, declarations);
            let (_, param3_constraint) = destruct_int(&param3_res.value, cur_expr, declarations);
            let (_, param4_constraint) = destruct_int(&param4_res.value, cur_expr, declarations);
            let cur_constraint = destruct_duration(&cur_value);
            constraints.extend([
                param1_constraint,
                param2_constraint,
                param3_constraint,
                param4_constraint,
                cur_constraint,
            ]);
            constraints
        }
        (Some("duration"), "value") => {
            let [param_res] = args[..] else { panic!() };
            let (_, param_constraint) = destruct_int(&param_res.value, cur_expr, declarations);
            let cur_constraint = destruct_duration(&cur_value);
            constraints.extend([param_constraint, cur_constraint]);
            constraints
        }
        (Some("hashing"), "crc32")
        | (Some("hashing"), "crc32c")
        | (Some("hashing"), "md5")
        | (Some("hashing"), "sha256") => {
            let [param_res] = args[..] else { panic!() };
            let (_, _, param_as_bytes_constraint) =
                destruct_bytes(&param_res.value, cur_expr, declarations);
            let (_, _, param_as_string_constraint) =
                destruct_string(&param_res.value, cur_expr, declarations);
            let cur_constraint = destruct_duration(&cur_value);
            constraints.extend([
                Constraint::new2(
                    "or",
                    &param_as_bytes_constraint,
                    &param_as_string_constraint,
                ),
                cur_constraint,
            ]);
            constraints
        }
        (Some("latlng"), "value") => {
            let [param1_res, param2_res] = args[..] else {
                panic!()
            };
            let param1_constraint = destruct_float(&param1_res.value);
            let param2_constraint = destruct_float(&param2_res.value);
            let cur_constraint = destruct_latlng(&cur_value);
            constraints.extend([param1_constraint, param2_constraint, cur_constraint]);
            constraints
        }
        (Some("math"), "abs") => {
            let [param_res] = args[..] else { panic!() };
            let (param_as_int_val, param_as_int_constraint) =
                destruct_int(&param_res.value, cur_expr, declarations);
            let param_as_float_constraint = destruct_float(&param_res.value);
            let (cur_as_int_val, cur_as_int_constraint) =
                destruct_int(&cur_value, cur_expr, declarations);
            let cur_as_float_constraint = destruct_float(&cur_value);
            constraints.extend([Constraint::new2(
                "or",
                &Constraint::new3(
                    "and",
                    &param_as_int_constraint,
                    &cur_as_int_constraint,
                    &Constraint::new2(
                        "=",
                        &Constraint::new3(
                            "if",
                            &Constraint::new2(">=", &param_as_int_val, &0),
                            &param_as_int_val,
                            &Constraint::new1("-", &param_as_int_val),
                        ),
                        &cur_as_int_val,
                    ),
                ),
                &Constraint::new2("and", &param_as_float_constraint, &cur_as_float_constraint),
            )]);
            constraints
        }
        (Some("math"), "ceil")
        | (Some("math"), "floor")
        | (Some("math"), "pow")
        | (Some("math"), "round")
        | (Some("math"), "sqrt") => {
            let [param_res] = args[..] else { panic!() };
            let param_constraint = destruct_float(&param_res.value);
            let cur_constraint = destruct_float(&cur_value);
            constraints.extend([param_constraint, cur_constraint]);
            constraints
        }
        (Some("timestamp"), "date") => {
            let [param1_res, param2_res, param3_res] = args[..] else {
                panic!()
            };
            let (_, param1_constraint) = destruct_int(&param1_res.value, cur_expr, declarations);
            let (_, param2_constraint) = destruct_int(&param2_res.value, cur_expr, declarations);
            let (_, param3_constraint) = destruct_int(&param3_res.value, cur_expr, declarations);
            let cur_constraint = destruct_timestamp(&cur_value);
            constraints.extend([
                param1_constraint,
                param2_constraint,
                param3_constraint,
                cur_constraint,
            ]);
            constraints
        }
        (Some("timestamp"), "value") => {
            let [param_res] = args[..] else { panic!() };
            let (_, param_constraint) = destruct_int(&param_res.value, cur_expr, declarations);
            let cur_constraint = destruct_timestamp(&cur_value);
            constraints.extend([param_constraint, cur_constraint]);
            constraints
        }
        (_, _) => panic!(),
    }
}
