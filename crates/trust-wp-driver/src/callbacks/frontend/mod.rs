// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Experimental typed shadow frontend. Nothing here supplies proof credit or
//! enables THIR retention. Callers must provide retained, authenticated bodies.
//!
//! This first component preserves compiler types, bindings, operator identities,
//! and literal carriers. It deliberately has no conversion to verifier IR yet.

#![allow(dead_code)] // Phase 1: exercised by compiler tests, not production routing.

mod identities;
mod lower;

pub(super) use identities::CanonicalHelpers;
#[cfg(test)]
pub(super) use lower::check_callee_surface_for_test;
pub(super) use lower::{lower_clause, lower_owner_clauses};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{thir::LocalVarId, ty::Ty};
use rustc_span::Span;

#[derive(Debug)]
pub(super) struct TypedClause<'tcx> {
    owner: LocalDefId,
    closure: LocalDefId,
    /// Authenticated metadata only; never parsed for expression semantics.
    tag: (String, String),
    body: TypedExpr<'tcx>,
}

impl<'tcx> TypedClause<'tcx> {
    pub(super) fn owner(&self) -> LocalDefId {
        self.owner
    }
    pub(super) fn closure(&self) -> LocalDefId {
        self.closure
    }
    pub(super) fn tag(&self) -> &(String, String) {
        &self.tag
    }
    pub(super) fn body(&self) -> &TypedExpr<'tcx> {
        &self.body
    }
}

#[derive(Debug)]
pub(super) struct TypedExpr<'tcx> {
    ty: Ty<'tcx>,
    span: Span,
    kind: ExprKind<'tcx>,
}

impl<'tcx> TypedExpr<'tcx> {
    pub(super) fn ty(&self) -> Ty<'tcx> {
        self.ty
    }
    pub(super) fn span(&self) -> Span {
        self.span
    }
    pub(super) fn kind(&self) -> &ExprKind<'tcx> {
        &self.kind
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Binding {
    Local(LocalVarId),
    Upvar {
        closure: DefId,
        variable: LocalVarId,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Op {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Implies,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum UnaryOp {
    Not,
    Neg,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LiteralSide {
    Left,
    Right,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Origin<'tcx> {
    /// Rust's native typed operation, including its machine-integer behavior.
    Native,
    /// Canonical logical vocabulary; distinct from native overflow semantics.
    Helper(DefId),
    /// Keep the physical carrier type AND the sibling's interpretation type.
    LiteralHelper {
        helper: DefId,
        side: LiteralSide,
        value_ty: Ty<'tcx>,
    },
}

#[derive(Debug)]
pub(super) enum ExprKind<'tcx> {
    Bool(bool),
    Integer {
        magnitude: u128,
        negative: bool,
    },
    Char(char),
    Binding(Binding),
    /// These place/value wrappers retain their own compiler types.
    Borrow(Box<TypedExpr<'tcx>>),
    Deref(Box<TypedExpr<'tcx>>),
    Unary {
        op: UnaryOp,
        origin: Origin<'tcx>,
        arg: Box<TypedExpr<'tcx>>,
    },
    Binary {
        op: Op,
        origin: Origin<'tcx>,
        lhs: Box<TypedExpr<'tcx>>,
        rhs: Box<TypedExpr<'tcx>>,
    },
    /// `int_lit` carries a u128 but denotes the canonical logical Int.
    IntLiteral {
        helper: DefId,
        carrier: Box<TypedExpr<'tcx>>,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum Refusal {
    MissingCanonicalItem(&'static str),
    AmbiguousCanonicalCrate,
    CompilerContextMismatch,
    UnauthenticatedClause,
    MissingClauseVehicles(Vec<(String, String)>),
    ThirUnavailable,
    ThirStolen,
    UnsupportedType,
    UnsupportedExpression,
    NontrivialCallee,
    UnsupportedCall(DefId),
    ErasedCall(DefId),
    InvalidHelperArguments(DefId),
    LimitExceeded,
}
