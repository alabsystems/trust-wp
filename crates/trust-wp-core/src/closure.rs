// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Backend-neutral closure capture metadata shared by the driver and backend.

use crate::formula::{ExprSort, PureExpr};

/// How a variable is captured by a closure.
///
/// Determines the correct `hist_inv` and `resolve` decomposition for each
/// capture field in a `FnMut` closure environment (#758):
/// - `ByValue`: unconstrained in `hist_inv`, trivially resolved
/// - `ByRef`: identity in `hist_inv` (value cannot change), trivially resolved
/// - `ByMutRef`: final-prophecy identity in `hist_inv` (`^cap_post == ^cap_pre`),
///   structural resolve (`*cap == ^cap`)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum CaptureKind {
    /// Captured by value (`move` or copy). May change between calls.
    ByValue,
    /// Captured by shared reference (`&T`). Cannot change.
    ByRef,
    /// Captured by mutable reference (`&mut T`). Final prophecy is preserved.
    ByMutRef,
}

/// One captured field in a closure environment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CaptureField {
    name: String,
    sort: ExprSort,
    kind: CaptureKind,
}

impl CaptureField {
    /// Create capture metadata for a single closure field.
    #[must_use]
    pub fn new(name: impl Into<String>, sort: ExprSort, kind: CaptureKind) -> Self {
        Self {
            name: name.into(),
            sort,
            kind,
        }
    }

    /// Returns the captured variable name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the solver-neutral logical sort for the captured value.
    #[must_use]
    pub fn sort(&self) -> &ExprSort {
        &self.sort
    }

    /// Returns how the variable is captured by the closure.
    #[must_use]
    pub fn kind(&self) -> CaptureKind {
        self.kind
    }
}

/// Capture metadata and optional inline body/spec data for a closure.
#[derive(Debug, Clone)]
pub struct ClosureCaptureInfo {
    /// Unique identifier for the closure type (e.g., its `DefId` path string).
    def_id: String,
    /// Capture fields in declaration order.
    captures: Vec<CaptureField>,
    /// The caller's parameter name that holds this closure value (e.g., `"c"`).
    ///
    /// When set, enables capture projection after encoding: for each capture
    /// field `i`, the encoder asserts `capture_i(param_final) == capture_name_final`.
    param_name: Option<String>,
    /// Inlined closure body expression (#2151 Phase 2).
    ///
    /// When the driver can extract the closure's MIR body as a `PureExpr`, it
    /// stores it here. The encoder can then replace `postcondition(env, args,
    /// result)` UF calls with ground `result == body_expr` assertions, eliminating
    /// quantifier load from closure axioms.
    ///
    /// Only populated for same-crate closures with simple bodies (<=6 effective
    /// basic blocks). Cross-crate and complex closures fall back to the UF+axiom
    /// encoding.
    body_expr: Option<PureExpr>,
    /// Closure parameter names (formal arguments, not captures).
    ///
    /// For a closure `|x, y| x + y`, this would be `["x", "y"]`.
    /// Used during body inlining to substitute formal parameters with actual
    /// call-site arguments.
    param_names: Option<Vec<String>>,
    /// User-annotated ensures expressions (#2151 Phase 3).
    ///
    /// When the closure has `#[ensures(...)]` annotations, these are the parsed
    /// contract expressions. For `postcondition_mut` inlining, these are used
    /// instead of the body expression because the body only captures the return
    /// value, not state changes to mutable captures.
    ///
    /// For `#[ensures(x@ == old(x@+1))]`, this would contain the parsed
    /// `PureExpr` representing that postcondition.
    ensures_exprs: Option<Vec<PureExpr>>,
    /// User-annotated requires expressions (#2668).
    ///
    /// When the closure has `#[requires(...)]` annotations, these are the parsed
    /// contract expressions. Enables `precondition` inlining: when a generic
    /// function requires `f.precondition(args)`, the solver can evaluate this
    /// against the concrete closure's requires specification rather than treating
    /// precondition as an opaque UF symbol.
    ///
    /// Without this, callers of generic functions like `call_fnmut<F: FnMut()>`
    /// cannot prove the precondition obligation because the solver has no axiom
    /// connecting `precondition(env, args)` to the concrete closure's requires.
    requires_exprs: Option<Vec<PureExpr>>,
}

impl ClosureCaptureInfo {
    /// Create a new closure capture description with only the required fields.
    #[must_use]
    pub fn new(def_id: String, captures: Vec<CaptureField>) -> Self {
        Self {
            def_id,
            captures,
            param_name: None,
            body_expr: None,
            param_names: None,
            ensures_exprs: None,
            requires_exprs: None,
        }
    }

    /// Set the caller variable name bound to the closure value.
    #[must_use]
    pub fn with_param_name(mut self, name: Option<String>) -> Self {
        self.param_name = name;
        self
    }

    /// Attach an inlined closure body expression.
    #[must_use]
    pub fn with_body_expr(mut self, expr: Option<PureExpr>) -> Self {
        self.body_expr = expr;
        self
    }

    /// Attach the formal parameter names for body inlining.
    #[must_use]
    pub fn with_param_names(mut self, names: Option<Vec<String>>) -> Self {
        self.param_names = names;
        self
    }

    /// Attach parsed ensures clauses for closure spec inlining.
    #[must_use]
    pub fn with_ensures_exprs(mut self, exprs: Option<Vec<PureExpr>>) -> Self {
        self.ensures_exprs = exprs;
        self
    }

    /// Attach parsed requires clauses for precondition inlining (#2668).
    #[must_use]
    pub fn with_requires_exprs(mut self, exprs: Option<Vec<PureExpr>>) -> Self {
        self.requires_exprs = exprs;
        self
    }

    /// Returns the unique identifier for the closure definition.
    #[must_use]
    pub fn def_id(&self) -> &str {
        &self.def_id
    }

    /// Returns the capture field metadata in declaration order.
    #[must_use]
    pub fn captures(&self) -> &[CaptureField] {
        &self.captures
    }

    /// Returns the caller parameter that stores this closure value, if known.
    #[must_use]
    pub fn param_name(&self) -> Option<&str> {
        self.param_name.as_deref()
    }

    /// Returns the inlined body expression, if one was extracted.
    #[must_use]
    pub fn body_expr(&self) -> Option<&PureExpr> {
        self.body_expr.as_ref()
    }

    /// Returns the formal closure parameter names, if available.
    #[must_use]
    pub fn param_names(&self) -> Option<&[String]> {
        self.param_names.as_deref()
    }

    /// Returns the parsed ensures clauses, if available.
    #[must_use]
    pub fn ensures_exprs(&self) -> Option<&[PureExpr]> {
        self.ensures_exprs.as_deref()
    }

    /// Returns the parsed requires clauses, if available (#2668).
    #[must_use]
    pub fn requires_exprs(&self) -> Option<&[PureExpr]> {
        self.requires_exprs.as_deref()
    }
}
