use nanoid::nanoid;

use crate::ast::{
    Argument, Ast, Expression, ExpressionKind, Function, LetBinding, MatchPathLiteral, NodeID,
    PathCapture, PathCaptureGroup, Rule, RuleGroup, RulesTree, Service,
};
use std::collections::HashMap;

#[derive(Clone, Copy, Debug)]
pub enum VariableNodeRef<'a> {
    LetBinding(&'a LetBinding),
    FunctionArgument(&'a Argument),
    FunctionPhantomArgument(&'static str, &'a Function),
    PathCapture(&'a PathCapture),
    PathCaptureGroup(&'a PathCaptureGroup),
    RuleGroupPhantomArgument(&'static str, &'a RuleGroup),
}

#[derive(Clone, Copy, Debug)]
pub enum FunctionNodeRef<'a> {
    Function(&'a Function),
    GlobalFunction(&'static str),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymbolID(pub String);

impl SymbolID {
    pub fn new() -> SymbolID {
        SymbolID(nanoid!())
    }
}

#[derive(Clone)]
pub struct Bindings<'a> {
    pub variable_table: HashMap<&'a NodeID, (SymbolID, VariableNodeRef<'a>)>,
    pub function_table: HashMap<&'a NodeID, (SymbolID, FunctionNodeRef<'a>)>,
}

#[derive(Clone, Debug)]
pub struct SymbolReferences<'a> {
    pub variable_table: HashMap<SymbolID, Vec<&'a NodeID>>,
    pub function_table: HashMap<SymbolID, Vec<&'a NodeID>>,
}

impl std::fmt::Debug for Bindings<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Bindings")
            .field(
                "variable_table",
                &self
                    .variable_table
                    .iter()
                    .map(|(k, v)| match v.1 {
                        VariableNodeRef::LetBinding(x) => {
                            format!("{} ({}) -> ({}:{})", x.name, k.0, x.id.0, v.0 .0)
                        }
                        VariableNodeRef::FunctionArgument(x) => {
                            format!("{} ({}) -> ({}:{})", x.name, k.0, x.id.0, v.0 .0)
                        }
                        VariableNodeRef::FunctionPhantomArgument(n, x) => {
                            format!("{} ({}) -> ({}:{})", n, k.0, x.id.0, v.0 .0)
                        }
                        VariableNodeRef::PathCapture(x) => {
                            format!("{} ({}) -> ({}:{})", x.name, k.0, x.id.0, v.0 .0)
                        }
                        VariableNodeRef::PathCaptureGroup(x) => {
                            format!("{} ({}) -> ({}:{})", x.name, k.0, x.id.0, v.0 .0)
                        }
                        VariableNodeRef::RuleGroupPhantomArgument(n, x) => {
                            format!("{} ({}) -> ({}:{})", n, k.0, x.id.0, v.0 .0)
                        }
                    })
                    .collect::<Vec<String>>(),
            )
            .field(
                "function_table",
                &self
                    .function_table
                    .iter()
                    .map(|(k, v)| match v.1 {
                        FunctionNodeRef::Function(x) => {
                            format!("{} ({}) -> ({}:{})", x.name, k.0, x.id.0, v.0 .0)
                        }
                        FunctionNodeRef::GlobalFunction(n) => {
                            format!("{} ({}) -> (__global__:{})", n, k.0, v.0 .0)
                        }
                    })
                    .collect::<Vec<String>>(),
            )
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct Definitions<'a> {
    pub variables: HashMap<&'a str, (SymbolID, VariableNodeRef<'a>)>,
    pub functions: HashMap<&'a str, (SymbolID, FunctionNodeRef<'a>)>,
}

#[derive(Clone, Debug)]
pub struct BindLintResult<'a> {
    pub node_id: &'a NodeID,
    pub kind: BindLintKind,
}

#[derive(Clone, Debug)]
pub enum BindLintKind {
    VariableNotFound,
    FunctionNotFound,
    VariableShadowed,
    FunctionShadowed,
}

fn search_variable_symbol<'a, 'b, 'c>(
    name: &'c str,
    scopes: &'b Vec<Definitions<'a>>,
) -> Option<(SymbolID, VariableNodeRef<'a>)> {
    scopes
        .iter()
        .rev()
        .map(|scope| scope.variables.get(name))
        .find(|option| option.is_some())
        .flatten()
        .cloned()
}

fn search_function_symbol<'a, 'b, 'c>(
    name: &'c str,
    scopes: &'b mut Vec<Definitions<'a>>,
) -> Option<(SymbolID, FunctionNodeRef<'a>)> {
    scopes
        .iter()
        .rev()
        .map(|scope| scope.functions.get(name))
        .find(|option| option.is_some())
        .flatten()
        .cloned()
}

fn bind_expression<'a, 'b>(
    expression: &'a Expression,
    scopes_definitions: &'b mut Vec<Definitions<'a>>,
    bindings: &'b mut Bindings<'a>,
    bind_lint_results: &'b mut Vec<BindLintResult<'a>>,
) {
    match &expression.kind {
        ExpressionKind::Literal(_) => (),
        ExpressionKind::Variable(variable) => {
            if let Some(symbol) = search_variable_symbol(&variable, scopes_definitions) {
                let _ = bindings.variable_table.insert(&expression.id, symbol);
            } else {
                bind_lint_results.push(BindLintResult {
                    node_id: &expression.id,
                    kind: BindLintKind::VariableNotFound,
                })
            }
        }
        ExpressionKind::UnaryOperation(_, expression) => {
            bind_expression(&expression, scopes_definitions, bindings, bind_lint_results)
        }
        ExpressionKind::BinaryOperation(_, left_expression, right_expression) => {
            bind_expression(
                &left_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            );
            bind_expression(
                &right_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            )
        }
        ExpressionKind::TernaryOperation(
            condition_expression,
            true_expression,
            false_expression,
        ) => {
            bind_expression(
                &condition_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            );
            bind_expression(
                &true_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            );
            bind_expression(
                &false_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            )
        }
        ExpressionKind::TypeCheckOperation(expression, _type_literal) => {
            bind_expression(&expression, scopes_definitions, bindings, bind_lint_results);
        }
        ExpressionKind::MemberExpression(object_expression, _member_expression) => {
            bind_expression(
                &object_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            );
        }
        ExpressionKind::SubscriptExpression(object_expression, subscript_expression) => {
            bind_expression(
                &object_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            );
            bind_expression(
                &subscript_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            )
        }
        ExpressionKind::FunctionCallExpression(name, params_expression) => {
            if let Some(symbol) = search_function_symbol(&name, scopes_definitions) {
                let _ = bindings.function_table.insert(&expression.id, symbol);
            } else {
                bind_lint_results.push(BindLintResult {
                    node_id: &expression.id,
                    kind: BindLintKind::FunctionNotFound,
                })
            }
            for param_expression in params_expression.iter() {
                bind_expression(
                    &param_expression,
                    scopes_definitions,
                    bindings,
                    bind_lint_results,
                );
            }
        }
    }
}

fn bind_function<'a, 'b>(
    function: &'a Function,
    scopes_definitions: &'b mut Vec<Definitions<'a>>,
    bindings: &'b mut Bindings<'a>,
    bind_lint_results: &'b mut Vec<BindLintResult<'a>>,
) {
    scopes_definitions.last_mut().unwrap().functions.insert(
        &function.name,
        (SymbolID::new(), FunctionNodeRef::Function(function)),
    );

    let mut definitions = Definitions {
        variables: HashMap::new(),
        functions: HashMap::new(),
    };

    definitions.variables.insert(
        "resource",
        (
            SymbolID::new(),
            VariableNodeRef::FunctionPhantomArgument("resource", function),
        ),
    );

    definitions.variables.insert(
        "request",
        (
            SymbolID::new(),
            VariableNodeRef::FunctionPhantomArgument("request", function),
        ),
    );

    for arg in function.arguments.iter() {
        let _ = definitions.variables.insert(
            &arg.name as &str,
            (SymbolID::new(), VariableNodeRef::FunctionArgument(arg)),
        );
    }

    scopes_definitions.push(definitions);

    for let_binding in function.let_bindings.iter() {
        bind_expression(
            &let_binding.expression,
            scopes_definitions,
            bindings,
            bind_lint_results,
        );

        let _ = scopes_definitions.last_mut().unwrap().variables.insert(
            &let_binding.name as &str,
            (SymbolID::new(), VariableNodeRef::LetBinding(let_binding)),
        );
    }

    scopes_definitions.pop();
}

fn bind_rule<'a, 'b>(
    rule: &'a Rule,
    scopes_definitions: &'b mut Vec<Definitions<'a>>,
    bindings: &'b mut Bindings<'a>,
    bind_lint_results: &'b mut Vec<BindLintResult<'a>>,
) {
    bind_expression(
        &rule.condition,
        scopes_definitions,
        bindings,
        bind_lint_results,
    );
}

fn bind_rule_group<'a, 'b>(
    rule_group: &'a RuleGroup,
    scopes_definitions: &'b mut Vec<Definitions<'a>>,
    bindings: &'b mut Bindings<'a>,
    bind_lint_results: &'b mut Vec<BindLintResult<'a>>,
) {
    scopes_definitions.push(Definitions {
        variables: rule_group
            .match_path
            .iter()
            .map(|match_path| match match_path {
                MatchPathLiteral::PathIdentifier(_) => None,
                MatchPathLiteral::PathCapture(path_capture) => Some((
                    &path_capture.name as &str,
                    (SymbolID::new(), VariableNodeRef::PathCapture(&path_capture)),
                )),
                MatchPathLiteral::PathCaptureGroup(path_capture_group) => Some((
                    &path_capture_group.name as &str,
                    (
                        SymbolID::new(),
                        VariableNodeRef::PathCaptureGroup(&path_capture_group),
                    ),
                )),
            })
            .flatten()
            .collect::<HashMap<&str, (SymbolID, VariableNodeRef)>>(),
        functions: HashMap::new(),
    });

    scopes_definitions.last_mut().unwrap().variables.insert(
        "resource",
        (
            SymbolID::new(),
            VariableNodeRef::RuleGroupPhantomArgument("resource", rule_group),
        ),
    );

    scopes_definitions.last_mut().unwrap().variables.insert(
        "request",
        (
            SymbolID::new(),
            VariableNodeRef::RuleGroupPhantomArgument("request", rule_group),
        ),
    );

    for function in rule_group.functions.iter() {
        bind_function(function, scopes_definitions, bindings, bind_lint_results);
    }

    for rule in rule_group.rules.iter() {
        bind_rule(rule, scopes_definitions, bindings, bind_lint_results);
    }

    for rule_group in rule_group.rule_groups.iter() {
        bind_rule_group(rule_group, scopes_definitions, bindings, bind_lint_results);
    }

    scopes_definitions.pop();
}

fn bind_service<'a, 'b>(
    service: &'a Service,
    scopes_definitions: &'b mut Vec<Definitions<'a>>,
    bindings: &'b mut Bindings<'a>,
    bind_lint_results: &'b mut Vec<BindLintResult<'a>>,
) {
    scopes_definitions.push(Definitions {
        variables: HashMap::new(),
        functions: service
            .functions
            .iter()
            .map(|function| {
                (
                    &function.name as &str,
                    (SymbolID::new(), FunctionNodeRef::Function(&function)),
                )
            })
            .collect(),
    });

    for function in service.functions.iter() {
        bind_function(function, scopes_definitions, bindings, bind_lint_results);
    }

    for rule_group in service.rule_groups.iter() {
        bind_rule_group(rule_group, scopes_definitions, bindings, bind_lint_results);
    }

    scopes_definitions.pop();
}

fn bind_rules_tree<'a, 'b>(
    rules_tree: &'a RulesTree,
    scopes_definitions: &'b mut Vec<Definitions<'a>>,
    bindings: &'b mut Bindings<'a>,
    bind_lint_results: &'b mut Vec<BindLintResult<'a>>,
) {
    for service in rules_tree.services.iter() {
        bind_service(service, scopes_definitions, bindings, bind_lint_results);
    }
}

pub fn bind(ast: &Ast) -> (Bindings, SymbolReferences, Vec<BindLintResult>) {
    let mut bindings = Bindings {
        variable_table: HashMap::new(),
        function_table: HashMap::new(),
    };

    let mut symbol_references = SymbolReferences {
        variable_table: HashMap::new(),
        function_table: HashMap::new(),
    };

    let mut scopes_definitions = Vec::<Definitions>::from([Definitions {
        variables: HashMap::new(),
        functions: HashMap::from([
            (
                "get",
                (SymbolID::new(), FunctionNodeRef::GlobalFunction("get")),
            ),
            (
                "getAfter",
                (SymbolID::new(), FunctionNodeRef::GlobalFunction("getAfter")),
            ),
            (
                "exists",
                (SymbolID::new(), FunctionNodeRef::GlobalFunction("exists")),
            ),
            (
                "existsAfter",
                (
                    SymbolID::new(),
                    FunctionNodeRef::GlobalFunction("existsAfter"),
                ),
            ),
        ]),
    }]);

    let mut bind_lint_results = Vec::<BindLintResult>::new();

    bind_rules_tree(
        &ast.tree,
        &mut scopes_definitions,
        &mut bindings,
        &mut bind_lint_results,
    );

    for var_binding in bindings.variable_table.iter() {
        let _ = symbol_references
            .variable_table
            .entry((var_binding.1).0.clone())
            .and_modify(|v| v.push(var_binding.0))
            .or_insert(vec![var_binding.0]);
    }

    for fn_binding in bindings.function_table.iter() {
        let _ = symbol_references
            .function_table
            .entry((fn_binding.1).0.clone())
            .and_modify(|v| v.push(fn_binding.0))
            .or_insert(vec![fn_binding.0]);
    }

    (bindings, symbol_references, bind_lint_results)
}
