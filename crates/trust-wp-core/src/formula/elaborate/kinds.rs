// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The kinds of node a clause's AST is made of: one per variant of
//! [`PureExpr`], [`BinOp`], [`UnOp`] and [`Pattern`].
//!
//! A generated oracle that claims to cover the contract language counts its
//! cases by these kinds. [`ExprKind::of`] and [`PatternKind::of`] are
//! exhaustive `match`es over the AST enums they mirror, so a new variant
//! does not build until it has a kind, and every list here is written by
//! `listed_enum!` from the variants themselves (`BinOp::ALL`, `UnOp::ALL`
//! too), so a new kind is in the list the oracle counts over, where it has no
//! case.

use std::{collections::BTreeSet, fmt};

use crate::{
    contract_parser::PatternForm,
    formula::{listed_enum::listed_enum, BinOp, Pattern, PureExpr, UnOp},
};

listed_enum! {
    /// One variant of [`PureExpr`].
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum ExprKind {
        Bool,
        Int,
        Float,
        Var,
        BinOp,
        UnOp,
        Ite,
        Old,
        Deref,
        Final,
        View,
        MethodCall,
        Forall,
        Exists,
        Match,
        LogicFnCall,
        Let,
        LetAssume,
        LetObligation,
        Closure,
    }
}

impl ExprKind {
    #[must_use]
    pub fn of(expr: &PureExpr) -> Self {
        match expr {
            PureExpr::Bool(_) => Self::Bool,
            PureExpr::Int(_) => Self::Int,
            PureExpr::Float(_) => Self::Float,
            PureExpr::Var(..) => Self::Var,
            PureExpr::BinOp(..) => Self::BinOp,
            PureExpr::UnOp(..) => Self::UnOp,
            PureExpr::Ite(..) => Self::Ite,
            PureExpr::Old(_) => Self::Old,
            PureExpr::Deref(_) => Self::Deref,
            PureExpr::Final(_) => Self::Final,
            PureExpr::View(_) => Self::View,
            PureExpr::MethodCall { .. } => Self::MethodCall,
            PureExpr::Forall { .. } => Self::Forall,
            PureExpr::Exists { .. } => Self::Exists,
            PureExpr::Match { .. } => Self::Match,
            PureExpr::LogicFnCall { .. } => Self::LogicFnCall,
            PureExpr::Let { .. } => Self::Let,
            PureExpr::LetAssume { .. } => Self::LetAssume,
            PureExpr::LetObligation { .. } => Self::LetObligation,
            PureExpr::Closure { .. } => Self::Closure,
        }
    }
}

listed_enum! {
    /// One variant of [`Pattern`].
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum PatternKind {
        Wildcard,
        Binding,
        Literal,
        Constructor,
        Alias,
        Tuple,
    }
}

impl PatternKind {
    #[must_use]
    pub fn of(pattern: &Pattern) -> Self {
        match pattern {
            Pattern::Wildcard => Self::Wildcard,
            Pattern::Binding(_) => Self::Binding,
            Pattern::Literal(_) => Self::Literal,
            Pattern::Constructor { .. } => Self::Constructor,
            Pattern::Alias { .. } => Self::Alias,
            Pattern::Tuple(_) => Self::Tuple,
        }
    }
}

/// One kind a clause can hold: an AST node's variant, a binary or unary
/// operator, a pattern's variant, or a pattern form the parser reads and
/// desugars ([`PatternForm`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NodeKind {
    Expr(ExprKind),
    BinOp(BinOp),
    UnOp(UnOp),
    Pattern(PatternKind),
    Form(PatternForm),
}

impl NodeKind {
    /// Every kind: each list's variants.
    #[must_use]
    pub fn all() -> Vec<Self> {
        ExprKind::ALL
            .iter()
            .map(|&kind| Self::Expr(kind))
            .chain(BinOp::ALL.iter().map(|&op| Self::BinOp(op)))
            .chain(UnOp::ALL.iter().map(|&op| Self::UnOp(op)))
            .chain(PatternKind::ALL.iter().map(|&kind| Self::Pattern(kind)))
            .chain(PatternForm::ALL.iter().map(|&form| Self::Form(form)))
            .collect()
    }

    /// Whether the contract parser builds this kind from clause text. The
    /// rest are built by the verifier: a call's assumption or obligation
    /// scoped to its branch, and an integer complement from MIR (the parser
    /// reads `!e` as `Not`, whatever `e` is).
    #[must_use]
    pub const fn written_by_the_parser(self) -> bool {
        !matches!(
            self,
            Self::Expr(ExprKind::LetAssume | ExprKind::LetObligation) | Self::UnOp(UnOp::BitNot)
        )
    }
}

impl fmt::Display for NodeKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expr(kind) => write!(formatter, "{kind:?}"),
            Self::BinOp(op) => write!(formatter, "BinOp::{op:?}"),
            Self::UnOp(op) => write!(formatter, "UnOp::{op:?}"),
            Self::Pattern(kind) => write!(formatter, "Pattern::{kind:?}"),
            Self::Form(form) => write!(formatter, "form {form:?}"),
        }
    }
}

/// Every kind `expr`'s nodes are, each once, with every pattern its `match`
/// arms hold.
#[must_use]
pub fn node_kinds(expr: &PureExpr) -> BTreeSet<NodeKind> {
    fn patterns(pattern: &Pattern, out: &mut BTreeSet<NodeKind>) {
        out.insert(NodeKind::Pattern(PatternKind::of(pattern)));
        match pattern {
            Pattern::Constructor {
                inner: Some(inner), ..
            } => patterns(inner, out),
            Pattern::Alias { pattern, .. } => patterns(pattern, out),
            Pattern::Tuple(elements) => {
                for element in elements {
                    patterns(element, out);
                }
            }
            Pattern::Literal(literal) => {
                out.extend(node_kinds(literal));
            }
            Pattern::Wildcard | Pattern::Binding(_) | Pattern::Constructor { inner: None, .. } => {}
        }
    }
    let mut kinds = BTreeSet::new();
    expr.for_each_recursive(|node| {
        kinds.insert(NodeKind::Expr(ExprKind::of(node)));
        match node {
            PureExpr::BinOp(_, op, _) => {
                kinds.insert(NodeKind::BinOp(*op));
            }
            PureExpr::UnOp(op, _) => {
                kinds.insert(NodeKind::UnOp(*op));
            }
            PureExpr::Match { arms, .. } => {
                for arm in arms {
                    patterns(&arm.pattern, &mut kinds);
                }
            }
            _ => {}
        }
    });
    kinds
}
