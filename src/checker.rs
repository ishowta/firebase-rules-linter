use crate::{
    ast::{Ast, Expression, ExpressionKind, Literal, NodeID, Rule, RuleGroup},
    symbol::{Bindings, SymbolReferences, VariableNodeRef},
    ty::TypeKind,
};

#[derive(Clone, Debug)]
pub struct TypeCheckResult<'a> {
    pub node_id: &'a NodeID,
    pub reason: String,
}

#[derive(Clone, Debug)]
pub struct TypeCheckContext<'a> {
    pub bindings: &'a Bindings<'a>,
    pub symbol_references: &'a SymbolReferences<'a>,
}

fn assert_type<'a, 'b>(
    ty: &'b TypeKind,
    kind: &'b TypeKind,
    expr: &'a Expression,
) -> Option<TypeCheckResult<'a>> {
    if *ty != *kind {
        Some(TypeCheckResult {
            node_id: &expr.id,
            reason: format!("Expected {:#?}, Get {:#?}", kind, ty).into(),
        })
    } else {
        None
    }
}

fn check_expression<'a>(
    expr: &'a Expression,
    context: &'a TypeCheckContext<'a>,
) -> (TypeKind, Vec<TypeCheckResult<'a>>) {
    match expr.kind {
        ExpressionKind::Literal(Literal::Bool(_)) => todo!(),
        ExpressionKind::Literal(Literal::Float(_)) => todo!(),
        ExpressionKind::Literal(Literal::Int(_)) => todo!(),
        ExpressionKind::Literal(Literal::String(_)) => todo!(),
        ExpressionKind::Literal(Literal::List(_)) => todo!(),
        ExpressionKind::Literal(Literal::Path(_)) => todo!(),
        ExpressionKind::Literal(Literal::Null) => todo!(),
        ExpressionKind::Variable(_) => match context
            .bindings
            .variable_table
            .get(&expr.id)
            .and_then(|node| Some(node.1))
        {
            Some(VariableNodeRef::LetBinding(node)) => check_expression(&node.expression, context),
            Some(VariableNodeRef::FunctionArgument(node)) => todo!(),
            Some(VariableNodeRef::PathCapture(node)) => todo!(),
            Some(VariableNodeRef::PathCaptureGroup(node)) => todo!(),
            Some(VariableNodeRef::GlobalVariable(type_kind)) => todo!(),
            None => todo!(),
        },
        ExpressionKind::UnaryOperation(_, _) => todo!(),
        ExpressionKind::BinaryOperation(_, _, _) => todo!(),
        ExpressionKind::TernaryOperation(_, _, _) => todo!(),
        ExpressionKind::TypeCheckOperation(_, _) => todo!(),
        ExpressionKind::MemberExpression(_, _) => todo!(),
        ExpressionKind::SubscriptExpression(_, _) => todo!(),
        ExpressionKind::FunctionCallExpression(_, _) => todo!(),
    }
}

fn check_rule<'a>(rule: &'a Rule, context: &'a TypeCheckContext<'a>) -> Vec<TypeCheckResult<'a>> {
    let (ty, mut result) = check_expression(&rule.condition, context);
    if let Some(res) = assert_type(&ty, &TypeKind::Boolean, &rule.condition) {
        result.push(res)
    }
    result
}

fn check_rule_group<'a>(
    rule_group: &'a RuleGroup,
    context: &'a TypeCheckContext<'a>,
) -> Vec<TypeCheckResult<'a>> {
    rule_group
        .rules
        .iter()
        .map(|rule| check_rule(rule, context))
        .flatten()
        .chain(
            rule_group
                .rule_groups
                .iter()
                .map(|rule_group| check_rule_group(rule_group, context))
                .flatten(),
        )
        .collect()
}

pub fn check<'a>(ast: &'a Ast, context: &'a TypeCheckContext<'a>) -> Vec<TypeCheckResult<'a>> {
    ast.tree
        .services
        .iter()
        .map(|service| {
            service
                .rule_groups
                .iter()
                .map(|rule_group| check_rule_group(rule_group, context))
                .flatten()
        })
        .flatten()
        .collect()
}
