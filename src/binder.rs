use miette::{Diagnostic, Report, SourceSpan};
use thiserror::Error;

use crate::{
    ast::{
        Argument, Ast, Expression, ExpressionKind, Function, MatchPathLiteral, Node, PathLiteral,
        Rule, RuleGroup, RulesTree, Service,
    },
    config::{Config, LintError},
    symbol::{Bindings, FunctionNodeRef, SymbolID, SymbolReferences, VariableNodeRef},
    ty::{FunctionInterface, Ty},
};
use std::{collections::HashMap, env::var};

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
                        VariableNodeRef::PathCapture(x) => {
                            format!("{} ({}) -> ({}:{})", x.name, k.0, x.id.0, v.0 .0)
                        }
                        VariableNodeRef::PathCaptureGroup(x) => {
                            format!("{} ({}) -> ({}:{})", x.name, k.0, x.id.0, v.0 .0)
                        }
                        VariableNodeRef::GlobalVariable(t) => {
                            format!("{:?} ({}) -> (__global__:{})", t, k.0, v.0 .0)
                        }
                    })
                    .collect::<Vec<String>>(),
            )
            .field(
                "function_table",
                &self
                    .function_table
                    .iter()
                    .map(|(k, v)| match &v.1 {
                        FunctionNodeRef::Function(x) => {
                            format!("{} ({}) -> ({}:{})", x.name, k.0, x.id.0, v.0 .0)
                        }
                        FunctionNodeRef::GlobalFunction(namespace, name, n) => {
                            format!(
                                "{:?} {} {:?} ({}) -> (__global__:{})",
                                namespace, name, n, k.0, v.0 .0
                            )
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
    pub namespaces: HashMap<&'a str, HashMap<&'a str, (SymbolID, FunctionNodeRef<'a>)>>,
}

pub struct ScopeDefinitions<'a> {
    scope_definitions: Vec<Definitions<'a>>,
}

impl<'a> ScopeDefinitions<'a> {
    pub fn new() -> ScopeDefinitions<'a> {
        ScopeDefinitions {
            scope_definitions: vec![],
        }
    }
    pub fn get(&self) -> &Vec<Definitions<'a>> {
        &self.scope_definitions
    }
    fn get_variable_already_declared(
        &self,
        name: &'a str,
    ) -> Option<&(SymbolID, VariableNodeRef<'a>)> {
        self.scope_definitions
            .iter()
            .rev()
            .find_map(|def| def.variables.get(name))
    }
    fn get_function_already_declared(
        &self,
        name: &'a str,
    ) -> Option<&(SymbolID, FunctionNodeRef<'a>)> {
        self.scope_definitions
            .iter()
            .rev()
            .find_map(|def| def.functions.get(name))
    }
    pub fn push(&mut self, definitions: Definitions<'a>) {
        self.scope_definitions.push(definitions)
    }
    pub fn pop(&mut self) {
        self.scope_definitions.pop();
    }
    pub fn insert_variable(
        &mut self,
        config: &Config,
        name: &'a str,
        symbol: (SymbolID, VariableNodeRef<'a>),
    ) -> Option<LintError> {
        let shadowed = self.get_variable_already_declared(name).cloned();
        self.scope_definitions
            .last_mut()
            .unwrap()
            .variables
            .insert(name, symbol.clone());
        if config.rules.no_shadow {
            if let Some(shadowed_symbol) = shadowed {
                return Some(LintError {
                    report: Report::from(VariableShadowed {
                        name: name.to_owned(),
                        at: symbol.1.get_node().unwrap().get_span().into(),
                        to: shadowed_symbol
                            .1
                            .get_node()
                            .and_then(|n| Some(n.get_span().into())),
                    }),
                    span: symbol.1.get_node().unwrap().get_span().into(),
                });
            }
        }
        None
    }
    pub fn insert_function(
        &mut self,
        config: &'a Config,
        name: &'a str,
        symbol: (SymbolID, FunctionNodeRef<'a>),
    ) -> Option<LintError> {
        let shadowed = self.get_function_already_declared(name).cloned();
        self.scope_definitions
            .last_mut()
            .unwrap()
            .functions
            .insert(name, symbol.clone());
        if config.rules.no_shadow {
            if let Some(shadowed_symbol) = shadowed {
                return Some(LintError {
                    report: Report::from(FunctionShadowed {
                        name: name.to_owned(),
                        at: symbol.1.get_node().unwrap().get_span().into(),
                        to: shadowed_symbol
                            .1
                            .get_node()
                            .and_then(|n| Some(n.get_span().into())),
                    }),
                    span: symbol.1.get_node().unwrap().get_span().into(),
                });
            }
        }
        None
    }
}

#[derive(Clone, Debug, Error, Diagnostic, PartialEq, Eq, Hash)]
#[error("Variable `{}` not found", self.name)]
#[diagnostic()]
pub struct VariableNotFound {
    pub name: String,
    #[label]
    pub at: SourceSpan,
}

#[derive(Clone, Debug, Error, Diagnostic, PartialEq, Eq, Hash)]
#[error("Function `{}()` not found", self.name)]
#[diagnostic()]
pub struct FunctionNotFound {
    pub name: String,
    #[label]
    pub at: SourceSpan,
}

#[derive(Clone, Debug, Error, Diagnostic, PartialEq, Eq, Hash)]
#[error("Argument {} already declared", self.name)]
#[diagnostic()]
pub struct ArgumentDuplicated {
    pub name: String,
    #[label("already declared here")]
    pub to: SourceSpan,
    #[label("declared here")]
    pub at: SourceSpan,
}

#[derive(Clone, Debug, Error, Diagnostic, PartialEq, Eq, Hash)]
#[error("Variable `{}` shadowed (no-shadow)", self.name)]
#[diagnostic()]
pub struct VariableShadowed {
    pub name: String,
    #[label("already declared here")]
    pub to: Option<SourceSpan>,
    #[label("declared here")]
    pub at: SourceSpan,
}

#[derive(Clone, Debug, Error, Diagnostic, PartialEq, Eq, Hash)]
#[error("Function `{}()` shadowed (no-shadow)", self.name)]
#[diagnostic()]
pub struct FunctionShadowed {
    pub name: String,
    #[label("already declared here")]
    pub to: Option<SourceSpan>,
    #[label("declared here")]
    pub at: SourceSpan,
}

fn search_variable_symbol<'a, 'b, 'c>(
    name: &'c str,
    scopes: &'b ScopeDefinitions<'a>,
) -> Option<(SymbolID, VariableNodeRef<'a>)> {
    scopes
        .get()
        .iter()
        .rev()
        .find_map(|scope| scope.variables.get(name))
        .cloned()
}

fn search_function_symbol<'a, 'b, 'c>(
    name: &'c str,
    scopes: &'b mut ScopeDefinitions<'a>,
) -> Option<(SymbolID, FunctionNodeRef<'a>)> {
    scopes
        .get()
        .iter()
        .rev()
        .find_map(|scope| scope.functions.get(name))
        .cloned()
}

fn search_namespace_symbol<'a, 'b, 'c>(
    name: &'c str,
    member: &'a Box<Expression>,
    scopes: &'b mut ScopeDefinitions<'a>,
) -> Option<(SymbolID, FunctionNodeRef<'a>)> {
    scopes
        .get()
        .iter()
        .rev()
        .find_map(|scope| {
            if let Some(namespace) = scope.namespaces.get(name) {
                if let ExpressionKind::FunctionCallExpression(function_name, _) = &member.kind {
                    namespace.get(&**function_name)
                } else {
                    panic!()
                }
            } else {
                None
            }
        })
        .cloned()
}

fn bind_expression<'a, 'b>(
    config: &'a Config,
    expression: &'a Expression,
    scopes_definitions: &'b mut ScopeDefinitions<'a>,
    bindings: &'b mut Bindings<'a>,
    bind_lint_results: &'b mut Vec<LintError>,
) {
    match &expression.kind {
        ExpressionKind::Literal(literal) => match literal {
            crate::ast::Literal::Null => (),
            crate::ast::Literal::Bool(_) => (),
            crate::ast::Literal::Int(_) => (),
            crate::ast::Literal::Float(_) => (),
            crate::ast::Literal::String(_) => (),
            crate::ast::Literal::List(elements) => {
                for element_expr in elements {
                    bind_expression(
                        config,
                        element_expr,
                        scopes_definitions,
                        bindings,
                        bind_lint_results,
                    )
                }
            }
            crate::ast::Literal::Map(entries) => {
                for (_, entry_expr) in entries {
                    bind_expression(
                        config,
                        entry_expr,
                        scopes_definitions,
                        bindings,
                        bind_lint_results,
                    )
                }
            }
            crate::ast::Literal::Path(args) => {
                for arg in args {
                    if let PathLiteral::PathExpressionSubstitution(arg_expr) = arg {
                        bind_expression(
                            config,
                            arg_expr,
                            scopes_definitions,
                            bindings,
                            bind_lint_results,
                        )
                    }
                }
            }
        },
        ExpressionKind::Variable(variable) => {
            if let Some(symbol) = search_variable_symbol(&variable, scopes_definitions) {
                let _ = bindings.variable_table.insert(&expression.id, symbol);
            } else {
                bind_lint_results.push(LintError {
                    report: Report::from(VariableNotFound {
                        name: variable.clone(),
                        at: expression.get_span().into(),
                    }),
                    span: expression.get_span().into(),
                })
            }
        }
        ExpressionKind::UnaryOperation(_, expression) => bind_expression(
            config,
            &expression,
            scopes_definitions,
            bindings,
            bind_lint_results,
        ),
        ExpressionKind::BinaryOperation(_, left_expression, right_expression) => {
            bind_expression(
                config,
                &left_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            );
            bind_expression(
                config,
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
                config,
                &condition_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            );
            bind_expression(
                config,
                &true_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            );
            bind_expression(
                config,
                &false_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            )
        }
        ExpressionKind::TypeCheckOperation(expression, _type_literal) => {
            bind_expression(
                config,
                &expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            );
        }
        ExpressionKind::MemberExpression(object_expression, member_expression) => {
            let mut is_namespace = false;
            if let ExpressionKind::Variable(name) = &object_expression.kind {
                if let Some(symbol) =
                    search_namespace_symbol(&name, member_expression, scopes_definitions)
                {
                    is_namespace = true;
                    let _ = bindings
                        .function_table
                        .insert(&member_expression.id, symbol);
                }
            }

            if !is_namespace {
                bind_expression(
                    config,
                    &object_expression,
                    scopes_definitions,
                    bindings,
                    bind_lint_results,
                );
            }

            if let ExpressionKind::FunctionCallExpression(_, args_expression) =
                &member_expression.kind
            {
                for arg_expression in args_expression {
                    bind_expression(
                        config,
                        &arg_expression,
                        scopes_definitions,
                        bindings,
                        bind_lint_results,
                    );
                }
            }
        }
        ExpressionKind::SubscriptExpression(object_expression, subscript_expression) => {
            bind_expression(
                config,
                &object_expression,
                scopes_definitions,
                bindings,
                bind_lint_results,
            );
            bind_expression(
                config,
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
                bind_lint_results.push(LintError {
                    report: Report::from(FunctionNotFound {
                        name: name.clone(),
                        at: expression.get_span().into(),
                    }),
                    span: expression.get_span().into(),
                })
            }
            for param_expression in params_expression.iter() {
                bind_expression(
                    config,
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
    config: &'a Config,
    function: &'a Function,
    scopes_definitions: &'b mut ScopeDefinitions<'a>,
    bindings: &'b mut Bindings<'a>,
    bind_lint_results: &'b mut Vec<LintError>,
) {
    if let Some(report) = scopes_definitions.insert_function(
        config,
        &function.name,
        (SymbolID::new(), FunctionNodeRef::Function(function)),
    ) {
        bind_lint_results.push(report);
    }

    let mut definitions = Definitions {
        variables: HashMap::new(),
        functions: HashMap::new(),
        namespaces: HashMap::new(),
    };

    let mut pre_args: Vec<&Argument> = vec![];
    for arg in function.arguments.iter() {
        if let Some(duplicated_pre_arg) = pre_args.iter().find(|pre_arg| pre_arg.name == arg.name) {
            bind_lint_results.push(LintError {
                report: Report::from(ArgumentDuplicated {
                    name: arg.name.clone(),
                    to: duplicated_pre_arg.get_span().into(),
                    at: arg.get_span().into(),
                }),
                span: arg.get_span().into(),
            })
        }
        let _ = definitions.variables.insert(
            &*arg.name,
            (SymbolID::new(), VariableNodeRef::FunctionArgument(arg)),
        );
        pre_args.push(arg);
    }

    scopes_definitions.push(definitions);

    for let_binding in function.let_bindings.iter() {
        bind_expression(
            config,
            &let_binding.expression,
            scopes_definitions,
            bindings,
            bind_lint_results,
        );

        if let Some(report) = scopes_definitions.insert_variable(
            config,
            &*let_binding.name,
            (SymbolID::new(), VariableNodeRef::LetBinding(let_binding)),
        ) {
            bind_lint_results.push(report)
        }
    }

    bind_expression(
        config,
        &function.return_expression,
        scopes_definitions,
        bindings,
        bind_lint_results,
    );

    scopes_definitions.pop();
}

fn bind_rule<'a, 'b>(
    config: &'a Config,
    rule: &'a Rule,
    scopes_definitions: &'b mut ScopeDefinitions<'a>,
    bindings: &'b mut Bindings<'a>,
    bind_lint_results: &'b mut Vec<LintError>,
) {
    bind_expression(
        config,
        &rule.condition,
        scopes_definitions,
        bindings,
        bind_lint_results,
    );
}

fn bind_rule_group<'a, 'b>(
    config: &'a Config,
    rule_group: &'a RuleGroup,
    scopes_definitions: &'b mut ScopeDefinitions<'a>,
    bindings: &'b mut Bindings<'a>,
    bind_lint_results: &'b mut Vec<LintError>,
) {
    scopes_definitions.push(Definitions {
        variables: rule_group
            .match_path
            .iter()
            .map(|match_path| match match_path {
                MatchPathLiteral::PathIdentifier(_) => None,
                MatchPathLiteral::PathCapture(path_capture) => Some((
                    &*path_capture.name,
                    (SymbolID::new(), VariableNodeRef::PathCapture(&path_capture)),
                )),
                MatchPathLiteral::PathCaptureGroup(path_capture_group) => Some((
                    &*path_capture_group.name,
                    (
                        SymbolID::new(),
                        VariableNodeRef::PathCaptureGroup(&path_capture_group),
                    ),
                )),
            })
            .flatten()
            .collect::<HashMap<&str, (SymbolID, VariableNodeRef)>>(),
        functions: HashMap::new(),
        namespaces: HashMap::new(),
    });

    for function in rule_group.functions.iter() {
        bind_function(
            config,
            function,
            scopes_definitions,
            bindings,
            bind_lint_results,
        );
    }

    for rule in rule_group.rules.iter() {
        bind_rule(
            config,
            rule,
            scopes_definitions,
            bindings,
            bind_lint_results,
        );
    }

    for rule_group in rule_group.rule_groups.iter() {
        bind_rule_group(
            config,
            rule_group,
            scopes_definitions,
            bindings,
            bind_lint_results,
        );
    }

    scopes_definitions.pop();
}

fn bind_service<'a, 'b>(
    config: &'a Config,
    service: &'a Service,
    scopes_definitions: &'b mut ScopeDefinitions<'a>,
    bindings: &'b mut Bindings<'a>,
    bind_lint_results: &'b mut Vec<LintError>,
) {
    scopes_definitions.push(Definitions {
        variables: HashMap::new(),
        functions: service
            .functions
            .iter()
            .map(|function| {
                (
                    &*function.name,
                    (SymbolID::new(), FunctionNodeRef::Function(&function)),
                )
            })
            .collect(),
        namespaces: HashMap::new(),
    });

    for function in service.functions.iter() {
        bind_function(
            config,
            function,
            scopes_definitions,
            bindings,
            bind_lint_results,
        );
    }

    for rule_group in service.rule_groups.iter() {
        bind_rule_group(
            config,
            rule_group,
            scopes_definitions,
            bindings,
            bind_lint_results,
        );
    }

    scopes_definitions.pop();
}

fn bind_rules_tree<'a, 'b>(
    config: &'a Config,
    rules_tree: &'a RulesTree,
    scopes_definitions: &'b mut ScopeDefinitions<'a>,
    bindings: &'b mut Bindings<'a>,
    bind_lint_results: &'b mut Vec<LintError>,
) {
    for service in rules_tree.services.iter() {
        bind_service(
            config,
            service,
            scopes_definitions,
            bindings,
            bind_lint_results,
        );
    }
}

pub fn bind<'a>(
    config: &'a Config,
    ast: &'a Ast,
    globals: &'a (
        HashMap<&'static str, Ty>,
        HashMap<&'static str, Vec<FunctionInterface>>,
        HashMap<&'static str, HashMap<&'static str, Vec<FunctionInterface>>>,
    ),
) -> (Bindings<'a>, SymbolReferences<'a>, Vec<LintError>) {
    let mut bindings = Bindings {
        variable_table: HashMap::new(),
        function_table: HashMap::new(),
    };

    let mut symbol_references = SymbolReferences {
        variable_table: HashMap::new(),
        function_table: HashMap::new(),
    };

    let mut scopes_definitions = ScopeDefinitions::new();

    scopes_definitions.push(Definitions {
        variables: globals
            .0
            .iter()
            .map(|(name, type_kind)| {
                (
                    *name,
                    (SymbolID::new(), VariableNodeRef::GlobalVariable(&type_kind)),
                )
            })
            .collect(),
        functions: globals
            .1
            .iter()
            .map(|(name, func)| {
                (
                    *name,
                    (
                        SymbolID::new(),
                        FunctionNodeRef::GlobalFunction(None, (*name).to_owned(), func),
                    ),
                )
            })
            .collect(),
        namespaces: globals
            .2
            .iter()
            .map(|(namespace, functions)| {
                (
                    *namespace,
                    functions
                        .iter()
                        .map(|(name, func)| {
                            (
                                *name,
                                (
                                    SymbolID::new(),
                                    FunctionNodeRef::GlobalFunction(
                                        Some((*namespace).to_owned()),
                                        (*name).to_owned(),
                                        func,
                                    ),
                                ),
                            )
                        })
                        .collect(),
                )
            })
            .collect(),
    });

    let mut bind_lint_results = Vec::<LintError>::new();

    bind_rules_tree(
        config,
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
