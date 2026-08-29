// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use rustc_middle::mir::{BasicBlock, Local, Location};
use rustc_span::Span;
use trust_wp_core::formula::{ExprSort, PureExpr};

pub(crate) const PROOF_ASSERT_STATE_MARKER_NAME: &str = "__trust_wp_proof_assert_state_marker";

pub(in crate::mir_analysis) fn cutoff_reached(span: Span, cutoff_span: Option<Span>) -> bool {
    let Some(cutoff) = cutoff_span else {
        return false;
    };
    let lhs = span.source_callsite();
    let rhs = cutoff.source_callsite();
    if lhs.is_dummy() || rhs.is_dummy() {
        return false;
    }
    // Stop at the assertion site (spans inside the cutoff span) or after it.
    // Keep broad enclosing spans that start before the assertion, since they
    // often correspond to pre-assert statements in the same source block.
    let starts_after_cutoff = lhs.lo() >= rhs.hi();
    let inside_cutoff = lhs.lo() >= rhs.lo() && lhs.hi() <= rhs.hi();
    starts_after_cutoff || inside_cutoff
}

pub(in crate::mir_analysis) fn cutoff_reached_at_statement(
    span: Span,
    cutoff_span: Option<Span>,
    cutoff_location: Option<Location>,
    block: BasicBlock,
    statement_index: usize,
) -> bool {
    if cutoff_reached(span, cutoff_span) {
        return true;
    }
    cutoff_location.is_some_and(|location| {
        location.block == block && statement_index >= location.statement_index
    })
}

pub(in crate::mir_analysis) fn cutoff_reached_at_terminator(
    span: Span,
    cutoff_span: Option<Span>,
    cutoff_location: Option<Location>,
    block: BasicBlock,
    statement_count: usize,
) -> bool {
    if cutoff_reached(span, cutoff_span) {
        return true;
    }
    cutoff_location.is_some_and(|location| {
        location.block == block && statement_count >= location.statement_index
    })
}

pub(in crate::mir_analysis) fn proof_assert_state_marker(
    local_exprs: &HashMap<Local, PureExpr>,
) -> PureExpr {
    // Use a non-Bool marker so LetAssume/LetObligation side effects are asserted
    // in value-context encoding (path-guarded implications) instead of becoming
    // unconstrained Bool equalities on `result`.
    local_exprs
        .get(&Local::from_u32(0))
        .cloned()
        .unwrap_or_else(|| {
            PureExpr::Var(
                PROOF_ASSERT_STATE_MARKER_NAME.to_string(),
                Some(ExprSort::Int),
            )
        })
}
