use crate::ast::*;
use tree_sitter::{Node, Parser, Tree};

struct Context<'a> {
    pub source_code: &'a String,
}

pub fn parse(code: &String) -> Ast {
    let mut tree_sitter_parser = Parser::new();
    tree_sitter_parser
        .set_language(tree_sitter_rules::language())
        .expect("Error loading grammar");
    // TODO: get parser error
    let tree_sitter_tree = tree_sitter_parser.parse(code, None).unwrap();
    // TODO: catch error
    let ast = tree_sitter_parser_tree_to_ast(tree_sitter_tree, code.into());
    ast
}

fn tree_sitter_parser_tree_to_ast(parser_tree: Tree, source_code: String) -> Ast {
    Ast {
        tree: parse_code(
            &parser_tree.root_node(),
            &Context {
                source_code: &source_code,
            },
        ),
    }
}

fn get_text<'a>(n: &Node, context: &'a Context) -> &'a str {
    n.utf8_text(context.source_code.as_bytes()).unwrap()
}

fn parse_string(x: &str) -> String {
    if x.starts_with('"') && x.ends_with('"') {
        x[1..x.len() - 1].replace("\\\"", "\"")
    } else if x.starts_with('\'') && x.ends_with('\'') {
        x[1..x.len() - 1].replace("\\'", "'")
    } else {
        panic!()
    }
}

fn parse_literal(_node: &Node, context: &Context) -> Literal {
    let node = _node.child(0).unwrap();
    match node.kind() {
        "string" => Literal::String(parse_string(get_text(&node, context))),
        "int" => Literal::Int(get_text(&node, context).parse::<i64>().unwrap()),
        "float" => Literal::Float(get_text(&node, context).parse::<f64>().unwrap()),
        "boolean" => Literal::Bool(get_text(&node, context).parse::<bool>().unwrap()),
        "list" => Literal::List(
            node.children_by_field_name("element", &mut node.walk())
                .map(|node| parse_expression(&node, context))
                .collect(),
        ),
        "path" => Literal::Path(
            node.children(&mut node.walk())
                .map(|node| match node.kind() {
                    "path_string" => PathLiteral::Path(
                        get_text(&node.child_by_field_name("path").unwrap(), context).into(),
                    ),
                    "path_reference_string" => PathLiteral::PathReference(Box::new(
                        parse_expression(&node.child_by_field_name("value").unwrap(), context),
                    )),
                    _ => panic!(),
                })
                .collect(),
        ),
        "null" => Literal::Null,
        _ => panic!(),
    }
}

fn parse_expression(node: &Node, context: &Context) -> Expression {
    match node.kind() {
        "literal" => Expression::Literal(parse_literal(node, context)),
        "identifier" => Expression::Value(get_text(node, context).into()),
        "unary_expression" => Expression::UnaryOperation(
            match node.child_by_field_name("operator").unwrap().kind() {
                "!" => UnaryLiteral::Not,
                "-" => UnaryLiteral::Minus,
                "+" => UnaryLiteral::Plus,
                "~" => UnaryLiteral::Tilde,
                _ => panic!(),
            },
            Box::new(parse_expression(
                &node.child_by_field_name("expression").unwrap(),
                context,
            )),
        ),
        "binary_expression" => Expression::BinaryOperation(
            match node.child_by_field_name("operator").unwrap().kind() {
                "&&" => BinaryLiteral::LogicalAnd,
                "||" => BinaryLiteral::LogicalOr,
                "&" => BinaryLiteral::BitwiseAnd,
                "^" => BinaryLiteral::BitwiseOr,
                "|" => BinaryLiteral::BitwiseXor,
                "+" => BinaryLiteral::Add,
                "-" => BinaryLiteral::Sub,
                "*" => BinaryLiteral::Mul,
                "/" => BinaryLiteral::Div,
                "%" => BinaryLiteral::Mod,
                "<" => BinaryLiteral::Gt,
                "<=" => BinaryLiteral::Gte,
                "==" => BinaryLiteral::Eq,
                "!=" => BinaryLiteral::NotEq,
                ">=" => BinaryLiteral::Lte,
                ">" => BinaryLiteral::Lt,
                "is" => BinaryLiteral::Is,
                "in" => BinaryLiteral::In,
                _ => panic!(),
            },
            Box::new(parse_expression(
                &node.child_by_field_name("left").unwrap(),
                context,
            )),
            Box::new(parse_expression(
                &node.child_by_field_name("right").unwrap(),
                context,
            )),
        ),
        "ternary_expression" => Expression::TernaryOperation(
            Box::new(parse_expression(
                &node.child_by_field_name("condition").unwrap(),
                context,
            )),
            Box::new(parse_expression(
                &node.child_by_field_name("true").unwrap(),
                context,
            )),
            Box::new(parse_expression(
                &node.child_by_field_name("false").unwrap(),
                context,
            )),
        ),
        "paran" => parse_expression(&node.child_by_field_name("expression").unwrap(), context),
        "member_expression" => Expression::MemberExpression(
            Box::new(parse_expression(
                &node.child_by_field_name("object").unwrap(),
                context,
            )),
            Box::new(parse_expression(
                &node.child_by_field_name("member").unwrap(),
                context,
            )),
        ),
        "subscript_expression" => Expression::SubscriptExpression(
            Box::new(parse_expression(
                &node.child_by_field_name("object").unwrap(),
                context,
            )),
            Box::new(parse_expression(
                &node.child_by_field_name("subscript").unwrap(),
                context,
            )),
        ),
        "function_call_expression" => Expression::FunctionCallExpression(
            get_text(&node.child_by_field_name("name").unwrap(), context).into(),
            node.child_by_field_name("params")
                .unwrap()
                .children_by_field_name("param", &mut node.walk())
                .map(|node| parse_expression(&node, context))
                .collect(),
        ),
        _ => panic!(),
    }
}

fn parse_function(node: &Node, context: &Context) -> Function {
    Function {
        name: get_text(&node.child_by_field_name("name").unwrap(), context).into(),
        arguments: node
            .child_by_field_name("argument")
            .unwrap()
            .children_by_field_name("arg", &mut node.walk())
            .map(|node| get_text(&node, context).into())
            .collect(),
        let_bindings: node
            .child_by_field_name("body")
            .unwrap()
            .children_by_field_name("statement", &mut node.walk())
            .map(|node| Binding {
                name: get_text(&node.child_by_field_name("name").unwrap(), context).into(),
                expression: parse_expression(
                    &node.child_by_field_name("expression").unwrap(),
                    context,
                ),
            })
            .collect(),
        return_expression: parse_expression(
            &node
                .child_by_field_name("body")
                .unwrap()
                .child_by_field_name("return")
                .unwrap()
                .child_by_field_name("expression")
                .unwrap(),
            context,
        ),
    }
}

fn parse_rule(node: &Node, context: &Context) -> Rule {
    Rule {
        permissions: node
            .children_by_field_name("operation", &mut node.walk())
            .map(|node| match get_text(&node, context) {
                "read" => Permission::Read,
                "get" => Permission::Get,
                "list" => Permission::List,
                "write" => Permission::Write,
                "create" => Permission::Create,
                "update" => Permission::Update,
                "delete" => Permission::Delete,
                _ => panic!(),
            })
            .collect(),
        condition: parse_expression(&node.child_by_field_name("expression").unwrap(), context),
    }
}

fn parse_rule_groups(node: &Node, context: &Context) -> RuleGroup {
    RuleGroup {
        match_path: node
            .child_by_field_name("path")
            .unwrap()
            .children(&mut node.walk())
            .map(|node| match node.kind() {
                "path_string" => MatchPathLiteral::Path(
                    get_text(&node.child_by_field_name("path").unwrap(), context).into(),
                ),
                "path_capture_string" => MatchPathLiteral::PathCapture(
                    get_text(&node.child_by_field_name("value").unwrap(), context).into(),
                ),
                "path_capture_group_string" => MatchPathLiteral::PathCaptureGroup(
                    get_text(&node.child_by_field_name("value").unwrap(), context).into(),
                ),
                _ => panic!(),
            })
            .collect(),
        functions: node
            .children_by_field_name("function", &mut node.walk())
            .map(|node| parse_function(&node, context))
            .collect(),
        rule_groups: node
            .children_by_field_name("match", &mut node.walk())
            .map(|node| parse_rule_groups(&node, context))
            .collect(),
        rules: node
            .children_by_field_name("allow", &mut node.walk())
            .map(|node| parse_rule(&node, context))
            .collect(),
    }
}

fn parse_code(node: &Node, context: &Context) -> RulesTree {
    RulesTree {
        version: node.child_by_field_name("version").map(|version| {
            parse_string(get_text(
                &version.child_by_field_name("version").unwrap(),
                context,
            ))
        }),
        services: node
            .children_by_field_name("service", &mut node.walk())
            .map(|node| Service {
                service_type: match get_text(&node.child_by_field_name("name").unwrap(), context) {
                    "cloud.firestore" => ServiceType::Firestore,
                    "firebase.storage" => ServiceType::Storage,
                    _ => panic!(),
                },
                functions: node
                    .children_by_field_name("function", &mut node.walk())
                    .map(|node| parse_function(&node, context))
                    .collect(),
                rule_groups: node
                    .children_by_field_name("match", &mut node.walk())
                    .map(|node| parse_rule_groups(&node, context))
                    .collect(),
            })
            .collect(),
    }
}
