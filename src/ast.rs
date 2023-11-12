use nanoid::nanoid;
use tree_sitter::Range;

#[derive(Debug)]
pub struct Ast {
    pub tree: RulesTree,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NodeID(pub String);

impl NodeID {
    pub fn new() -> NodeID {
        NodeID(nanoid!())
    }
}

#[derive(Clone)]
pub struct Span(pub Range);

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Span")
            .field(&format!(
                "({},{}), ({},{})",
                &self.0.start_point.row,
                &self.0.start_point.column,
                &self.0.end_point.row,
                &self.0.end_point.column
            ))
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct RulesTree {
    pub id: NodeID,
    pub span: Span,
    pub version: Option<String>,
    pub services: Vec<Service>,
}

#[derive(Clone, Debug)]
pub struct Service {
    pub id: NodeID,
    pub span: Span,
    pub service_type: ServiceType,
    pub functions: Vec<Function>,
    pub rule_groups: Vec<RuleGroup>,
}

#[derive(Clone, Debug)]
pub enum ServiceType {
    Firestore,
    Storage,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub id: NodeID,
    pub span: Span,
    pub name: String,
    pub arguments: Vec<Argument>,
    pub let_bindings: Vec<LetBinding>,
    pub return_expression: Expression,
}

#[derive(Clone, Debug)]
pub struct Argument {
    pub id: NodeID,
    pub span: Span,
    pub name: String,
}

#[derive(Clone, Debug)]
pub struct LetBinding {
    pub id: NodeID,
    pub span: Span,
    pub name: String,
    pub expression: Expression,
}

#[derive(Clone, Debug)]
pub struct RuleGroup {
    pub id: NodeID,
    pub span: Span,
    pub match_path: Vec<MatchPathLiteral>,
    pub functions: Vec<Function>,
    pub rules: Vec<Rule>,
    pub rule_groups: Vec<RuleGroup>,
}

#[derive(Clone, Debug)]
pub enum MatchPathLiteral {
    PathIdentifier(String),
    PathCapture(PathCapture),
    PathCaptureGroup(PathCaptureGroup),
}

#[derive(Clone, Debug)]
pub struct PathCapture {
    pub id: NodeID,
    pub span: Span,
    pub name: String,
}

#[derive(Clone, Debug)]
pub struct PathCaptureGroup {
    pub id: NodeID,
    pub span: Span,
    pub name: String,
}

#[derive(Clone, Debug)]
pub struct Rule {
    pub id: NodeID,
    pub span: Span,
    pub permissions: Vec<Permission>,
    pub condition: Expression,
}

#[derive(Clone, Debug)]
pub enum Permission {
    Read,
    Get,
    List,
    Write,
    Update,
    Delete,
    Create,
}

#[derive(Clone, Debug)]
pub struct Expression {
    pub id: NodeID,
    pub span: Span,
    pub kind: ExpressionKind,
}

#[derive(Clone, Debug)]
pub enum ExpressionKind {
    Literal(Literal),
    Variable(String),
    UnaryOperation(UnaryLiteral, Box<Expression>),
    BinaryOperation(BinaryLiteral, Box<Expression>, Box<Expression>),
    TernaryOperation(Box<Expression>, Box<Expression>, Box<Expression>),
    TypeCheckOperation(Box<Expression>, String),
    MemberExpression(Box<Expression>, Box<Expression>),
    SubscriptExpression(Box<Expression>, Box<Expression>),
    FunctionCallExpression(String, Vec<Expression>),
}

#[derive(Clone, Debug)]
pub enum Literal {
    Null,
    Bool(bool),
    Int(i64),
    Float(f64),
    String(String),
    List(Vec<Expression>),
    Path(Vec<PathLiteral>),
}

#[derive(Clone, Debug)]
pub enum PathLiteral {
    Path(String),
    PathReference(Box<Expression>),
}

#[derive(Clone, Debug)]
pub enum UnaryLiteral {
    Not,
    Tilde,
    Plus,
    Minus,
}

#[derive(Clone, Debug)]
pub enum BinaryLiteral {
    LogicalAnd,
    LogicalOr,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Gt,
    Gte,
    Lt,
    Lte,
    Eq,
    NotEq,
    In,
}

pub trait Node {
    fn get_id(&self) -> &NodeID;
    fn get_span(&self) -> &Span;
}

macro_rules! impl_node_trait {
    ($($T:ty),+ $(,)?) => {
        $(
            impl Node for $T {
                fn get_id(&self) -> &NodeID {
                    &self.id
                }
                fn get_span(&self) -> &Span {
                    &self.span
                }
            }
        )+
    };
}

impl_node_trait!(
    RulesTree,
    Service,
    Function,
    Argument,
    LetBinding,
    RuleGroup,
    PathCapture,
    PathCaptureGroup,
    Rule,
    Expression
);
