use nanoid::{alphabet, nanoid};

use crate::{
    ast::{Argument, Function, LetBinding, Node, NodeID, PathCapture, PathCaptureGroup},
    ty::{FunctionInterface, Ty},
};
use std::collections::HashMap;

#[derive(Clone, Copy, Debug)]
pub enum VariableNodeRef<'a> {
    LetBinding(&'a LetBinding),
    FunctionArgument(&'a Argument),
    PathCapture(&'a PathCapture),
    PathCaptureGroup(&'a PathCaptureGroup),
    GlobalVariable(&'a Ty),
}

impl<'a> VariableNodeRef<'a> {
    pub fn get_node(&'a self) -> Option<&'a dyn Node> {
        match self {
            VariableNodeRef::LetBinding(node) => Some(*node),
            VariableNodeRef::FunctionArgument(node) => Some(*node),
            VariableNodeRef::PathCapture(node) => Some(*node),
            VariableNodeRef::PathCaptureGroup(node) => Some(*node),
            VariableNodeRef::GlobalVariable(_) => None,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum FunctionNodeRef<'a> {
    Function(&'a Function),
    GlobalFunction(&'a Vec<FunctionInterface<'a>>),
}

impl<'a> FunctionNodeRef<'a> {
    pub fn get_node(&'a self) -> Option<&'a dyn Node> {
        match self {
            FunctionNodeRef::Function(node) => Some(*node),
            FunctionNodeRef::GlobalFunction(_) => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymbolID(pub String);

impl SymbolID {
    pub fn new() -> SymbolID {
        SymbolID(nanoid!(6, &alphabet::SAFE[12..]))
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
