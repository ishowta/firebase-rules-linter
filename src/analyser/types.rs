use std::{cell::RefCell, collections::HashMap};

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::{
    ast::{Node, NodeID},
    config::Config,
    symbol::{Bindings, SymbolReferences},
};

use super::z3::{Constraint, Declaration, Symbol};

#[derive(Clone, Debug, Error, Diagnostic, PartialEq, Eq, Hash)]
#[error("{reason}")]
#[diagnostic()]
pub struct AnalysysError {
    pub reason: String,
    #[label]
    pub at: SourceSpan,
}

impl AnalysysError {
    pub fn new(reason: String, node: &dyn Node) -> AnalysysError {
        AnalysysError {
            reason: reason,
            at: node.get_span().into(),
        }
    }
}

#[derive(Clone, Debug, Error, Diagnostic, PartialEq, Eq, Hash)]
#[error("{reason}")]
#[diagnostic(severity(Warning))]
pub struct AnalysysWarning {
    pub reason: String,
    #[label]
    pub at: SourceSpan,
}

impl AnalysysWarning {
    pub fn new(reason: String, node: &dyn Node) -> AnalysysWarning {
        AnalysysWarning {
            reason: reason,
            at: node.get_span().into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AnalysysResult {
    Error(AnalysysError),
    Warning(AnalysysWarning),
}

#[derive(Clone, Debug)]
pub struct Res {
    pub value: Symbol,
    pub constraints: Vec<Constraint>,
}

#[derive(Clone, Debug)]
pub struct AnalysysGlobalContext<'a> {
    pub bindings: &'a Bindings<'a>,
    pub symbol_references: &'a SymbolReferences<'a>,
    pub source_code: &'a String,
    pub config: &'a Config,
}

#[derive(Clone, Debug)]
pub struct AnalysysContext<'a, 'ctx> {
    pub bindings: &'a Bindings<'a>,
    pub symbol_references: &'a SymbolReferences<'a>,
    pub source_code: &'a String,
    pub declarations: &'ctx RefCell<Vec<Declaration>>,
    pub variable_bindings: &'ctx HashMap<&'a NodeID, Symbol>,
    pub quick_mode: bool,
}
