use std::collections::HashMap;

use itertools::Itertools;
use log::debug;
use serde_json::{Map, Number, Value};
use smt2parser::{
    concrete::{self, Command, Constant, QualIdentifier, Symbol, Term},
    visitors::Identifier,
    CommandStream,
};

#[test]
fn term_with_let() {
    let term = r#"(let ((a!1 (insert (entry "room_id" (str "t" 1277))
    (insert (entry "user_id" (str "t" 605))
            (insert (entry "created_at" timestamp)
                    (as nil (List (Entry String Refl))))))))
(insert (entry "text" (str "t" 1046637)) (insert (entry "star" (int 97)) a!1)))"#;
    println!("{}", parse_smt2_result(term.to_owned()));
}

pub fn parse_smt2_result(result_smt2: String) -> Value {
    let mut context = Context {
        vars: HashMap::new(),
    };
    parse_smt2_term_json(&parse_smt2_term(
        &mut context,
        &parse_smt2_result_str_to_ast(result_smt2),
    ))
}

fn parse_smt2_result_str_to_ast(result_smt2: String) -> Term {
    let result_as_valid_syntax_smt2 = format!("(assert (= a {}))", result_smt2).into_bytes();
    let result_ast = &CommandStream::new(
        &result_as_valid_syntax_smt2[..],
        concrete::SyntaxBuilder,
        None,
    )
    .collect::<Result<Vec<_>, _>>()
    .unwrap()[0];
    let result_ast = if let Command::Assert { term } = result_ast {
        if let Term::Application {
            qual_identifier: _,
            arguments,
        } = term
        {
            &arguments[1]
        } else {
            panic!()
        }
    } else {
        panic!()
    };
    debug!("{:#?}", result_ast);
    result_ast.clone()
}

struct Context {
    vars: HashMap<Symbol, Value>,
}

fn parse_name(term: &Term) -> &String {
    if let Term::Constant(Constant::String(name)) = term {
        name
    } else {
        panic!()
    }
}

fn parse_int(term: &Term) -> usize {
    match term {
        Term::Constant(Constant::Numeral(bytes_length)) => bytes_length.try_into().unwrap(),
        Term::Application {
            qual_identifier:
                QualIdentifier::Simple {
                    identifier:
                        Identifier::Simple {
                            symbol: Symbol(name),
                        },
                },
            arguments,
        } if name == "int" => match &arguments[0] {
            Term::Constant(Constant::Numeral(bytes_length)) => bytes_length.try_into().unwrap(),
            _ => panic!(),
        },
        _ => panic!(),
    }
}

fn parse_smt2_term_json(value: &Value) -> Value {
    if let Value::Array(items) = value {
        if let Some(&Value::Array(ref inner_items)) = items.get(0) {
            if inner_items.get(0) == Some(&Value::String("__entry__".to_owned())) {
                let mut map = Map::new();
                for item in items {
                    if let Value::Array(inner_items) = item {
                        if let Value::String(key) = &inner_items[1] {
                            map.insert(key.clone(), parse_smt2_term_json(&inner_items[2]));
                        } else {
                            panic!()
                        }
                    } else {
                        panic!()
                    }
                }
                return Value::Object(map);
            }
        }
        return Value::Array(
            items
                .iter()
                .map(|item| parse_smt2_term_json(item))
                .collect(),
        );
    }
    value.clone()
}

fn parse_smt2_term(context: &mut Context, term: &Term) -> Value {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let application_name = match qual_identifier {
                concrete::QualIdentifier::Simple { identifier } => match identifier {
                    concrete::Identifier::Simple { symbol } => symbol.0.as_str(),
                    _ => panic!(),
                },
                _ => panic!(),
            };
            match application_name {
                "insert" => {
                    let item = parse_smt2_term(context, &arguments[0]);
                    let array = parse_smt2_term(context, &arguments[1]);
                    match array {
                        Value::Array(mut items) => {
                            items.push(item);
                            Value::Array(items)
                        }
                        Value::Null => Value::Array(vec![item]),
                        _ => panic!(),
                    }
                }
                "entry" => {
                    let key = if let Term::Constant(Constant::String(name)) = &arguments[0] {
                        name
                    } else {
                        panic!()
                    };
                    let value = parse_smt2_term(context, &arguments[1]);
                    Value::Array(vec![
                        Value::String("__entry__".to_owned()),
                        Value::String(key.clone()),
                        value,
                    ])
                }
                "bool" => {
                    let value = match qual_identifier {
                        concrete::QualIdentifier::Simple { identifier } => match identifier {
                            concrete::Identifier::Simple { symbol } => symbol.0.as_str(),
                            _ => panic!(),
                        },
                        _ => panic!(),
                    };
                    Value::Bool(value == "true")
                }
                "int" => {
                    let value = parse_int(&arguments[0]);
                    Value::Number(Number::from(value))
                }
                "str" => {
                    let value = parse_name(&arguments[0]);
                    let byte_length = parse_int(&arguments[1]);
                    if value.len() == byte_length {
                        Value::String(value.clone())
                    } else {
                        Value::String(format!("[string of {} bytes]", byte_length))
                    }
                }
                "bytes" => Value::String("[any]".to_owned()),
                "list" => {
                    let value = parse_smt2_term(context, &arguments[0]);
                    let byte_length = parse_int(&arguments[1]);
                    if let Value::Array(items) = &value {
                        if items.len() == byte_length {
                            value.clone()
                        } else {
                            Value::String(format!("[list of {} bytes]", byte_length))
                        }
                    } else {
                        panic!()
                    }
                }
                "map" => {
                    let value = parse_smt2_term(context, &arguments[0]);
                    value.clone()
                }
                "mapdiff" => Value::String("[any]".to_owned()),
                "set" => Value::String("[any]".to_owned()),
                _ => panic!(),
            }
        }
        Term::Let { var_bindings, term } => {
            for var_binding in var_bindings.into_iter() {
                let var = parse_smt2_term(context, &var_binding.1);
                context.vars.insert(var_binding.0.clone(), var);
            }
            parse_smt2_term(context, term)
        }
        Term::QualIdentifier(qual_identifier) => {
            let identifier = match qual_identifier {
                QualIdentifier::Simple { identifier } => match identifier {
                    Identifier::Simple { symbol } => symbol,
                    _ => panic!(),
                },
                QualIdentifier::Sorted {
                    sort: _,
                    identifier,
                } => match identifier {
                    Identifier::Simple { symbol } => symbol,
                    _ => panic!(),
                },
            };
            match identifier.0.as_str() {
                "undefined" => Value::String("[any]".to_owned()),
                "null" => Value::Null,
                "float" => Value::String("[float]".to_owned()),
                "duration" => Value::String("[any]".to_owned()),
                "latlng" => Value::String("[latlng]".to_owned()),
                "timestamp" => Value::String("[timestamp]".to_owned()),
                "path" => Value::String("[path]".to_owned()),
                "nil" => Value::Null,
                _ => context.vars.get(identifier).unwrap().clone(),
            }
        }
        _ => panic!(),
    }
}
