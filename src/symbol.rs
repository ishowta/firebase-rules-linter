use nanoid::nanoid;

use crate::ast::{
    Argument, Function, LetBinding, NodeID, PathCapture, PathCaptureGroup, RuleGroup,
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
