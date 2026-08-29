// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

use trust_wp_core::formula::{ProjectedFinalPin, PureExpr};

use crate::mir_analysis::{LoopAnalysis, MutBorrowBody, SpannedBodyExpr};

/// A group of call-site obligations from a single loop, paired with that
/// loop's condition. Replaces the flat obligation list + single condition
/// that dropped conditions for multi-loop functions (#752).
pub(in crate::callbacks) struct LoopObligationGroup {
    /// Postcondition facts from calls that dominate this loop header.
    pub(in crate::callbacks) assumptions: Vec<PureExpr>,
    /// Call-site precondition obligations from INSIDE this loop body.
    pub(in crate::callbacks) obligations: Vec<PureExpr>,
    /// The loop condition expression (e.g., `i < n`), used as an additional
    /// assumption when verifying this loop's in-body call obligations.
    pub(in crate::callbacks) condition: Option<PureExpr>,
}

/// Loop-specific fields from contract parsing.
///
/// Populated when `#[invariant]` or `#[variant]` attributes are present.
/// Used by loop verification dispatch (`loop_contract.rs`, `loop_verify/`).
pub(in crate::callbacks) struct LoopFields {
    /// Loop invariants specified via `#[invariant]` (flattened across all loops)
    pub(in crate::callbacks) invariants: Vec<PureExpr>,
    /// Per-loop invariants with source span (start, end) of the loop expression.
    /// When non-empty, loop_verify uses these instead of the flat `invariants` list
    /// to assign each invariant to its corresponding loop via span containment.
    pub(in crate::callbacks) per_loop_invariants: Vec<(u32, u32, Vec<PureExpr>)>,
    /// Per-loop variants with source span (start, end) of the loop expression.
    /// Used to bind the correct termination variant to each loop in multi-loop
    /// functions (#752).
    pub(in crate::callbacks) per_loop_variants: Vec<(u32, u32, Vec<PureExpr>)>,
    /// Source spans of ALL loop expressions (including those without invariants).
    pub(in crate::callbacks) all_loop_spans: Vec<(u32, u32)>,
    /// Loop variants for termination proofs via `#[variant]`.
    ///
    /// Kept flat for recursive termination checking and as a single-loop
    /// fallback when no per-loop mapping is needed.
    pub(in crate::callbacks) variants: Vec<PureExpr>,
    /// Loop analysis result
    pub(in crate::callbacks) loop_analysis: Option<LoopAnalysis>,
    /// Per-loop obligation groups, each pairing a loop's in-body call
    /// obligations with that loop's condition (#752).
    ///
    /// Multi-loop functions produce one group per loop. Each group's
    /// obligations are verified under `requires ∧ invariants ∧ group.condition`.
    pub(in crate::callbacks) loop_obligation_groups: Vec<LoopObligationGroup>,
}

impl LoopFields {
    /// Return the single loop's condition for single-loop functions (#638).
    ///
    /// For multi-loop functions, returns `None` — per-loop conditions are
    /// only used in obligation verification, not in exit assumptions.
    /// Used by `build_loop_exit_assumptions` for the compositional path (#2085).
    pub(in crate::callbacks) fn single_loop_condition(&self) -> Option<&PureExpr> {
        if self.loop_obligation_groups.len() == 1 {
            self.loop_obligation_groups[0].condition.as_ref()
        } else {
            None
        }
    }
}

/// Mutable borrow analysis fields from contract parsing.
///
/// Populated when function parameters include `&mut` references.
/// Used by mutable borrow verification dispatch.
pub(in crate::callbacks) struct MutBorrowFields {
    /// Mutable borrow body analysis result (for &mut parameters)
    pub(in crate::callbacks) mut_borrow_body: Option<MutBorrowBody>,
    /// Names of function parameters whose signature type is `&mut _`.
    ///
    /// This is populated directly from MIR local declarations so postcondition
    /// mut-ref rewriting can run even when mut-borrow body extraction returns
    /// `None` (e.g., call-heavy bodies like deref wrappers). (#717)
    pub(in crate::callbacks) mut_ref_param_names: HashSet<String>,
    /// Caller-side expiry pins for `&mut` borrows reached out of a call result
    /// (#prophecy-slots M5). Empty unless `projected_expiry` PROVED a death
    /// point; see that module's R0..R11 table.
    pub(in crate::callbacks) projected_final_pins: Vec<ProjectedFinalPin>,
}

/// Parsed and extracted contract data ready for verification.
///
/// Fields are grouped into sub-structs by verification dispatch path:
/// - `loop_fields`: loop invariants, variants, loop analysis (#866)
/// - `mut_borrow`: mutable borrow body, mut-ref parameter names (#866)
/// - Base fields (requires, ensures, arg_names, etc.) are used by all paths.
pub(in crate::callbacks) struct ParsedContract {
    pub(in crate::callbacks) requires: Vec<PureExpr>,
    pub(in crate::callbacks) ensures: Vec<PureExpr>,
    pub(in crate::callbacks) result_expr: Option<PureExpr>,
    /// Result expression with MIR source span (for error reporting)
    pub(in crate::callbacks) result_expr_spanned: Option<SpannedBodyExpr>,
    /// Function argument names (for variable mapping in loop analysis)
    pub(in crate::callbacks) arg_names: Vec<String>,
    /// Call-site predicate assumptions from specs like Fn::call.
    ///
    /// When a call site's spec has a predicate-style postcondition
    /// (e.g., `f.postcondition(x, result)`) that can't be expressed as
    /// `result == <expr>`, the substituted predicate is added here as
    /// an assumption for the outer verification.
    pub(in crate::callbacks) call_assumptions: Vec<PureExpr>,
    /// Call-site predicate assumptions before the first loop.
    ///
    /// Loop-call obligation verification uses this subset to prove genuinely
    /// pre-loop call requirements without leaking post-loop assumptions into
    /// loop-entry checks.
    pub(in crate::callbacks) pre_loop_call_assumptions: Vec<PureExpr>,
    /// Call-site precondition obligations outside loop bodies.
    ///
    /// When a call site has preconditions (requires clauses), the caller
    /// must prove these hold. These are added as additional verification
    /// goals (alongside the caller's own ensures clauses).
    /// Includes obligations before the first loop and after loop exit; in-loop
    /// obligations are in `loop_fields.loop_call_obligations`.
    pub(in crate::callbacks) call_obligations: Vec<PureExpr>,
    /// Call-site precondition obligations before the first loop.
    ///
    /// `call_obligations` contains all non-loop obligations so the
    /// function-level verifier can check both pre-loop and post-loop calls.
    /// The loop-obligation verifier uses this narrower list so post-loop calls
    /// are checked only after loop-exit assumptions have been threaded.
    pub(in crate::callbacks) pre_loop_call_obligations: Vec<PureExpr>,
    /// Call-site precondition obligations after loop exit.
    ///
    /// These force `ContinueWithAssumptions` even when the function has no
    /// user postconditions: they still need the post-loop function-level path.
    pub(in crate::callbacks) post_loop_call_obligations: Vec<PureExpr>,
    /// Loop-specific fields (invariants, variants, loop analysis).
    pub(in crate::callbacks) loop_fields: LoopFields,
    /// Mutable borrow analysis fields.
    pub(in crate::callbacks) mut_borrow: MutBorrowFields,
    /// Recognized recursive `&mut self` match-reborrow shape (rusthorn
    /// `take_some`), used to synthesize the prophecy-pinning premise.
    pub(in crate::callbacks) reborrow_prophecy: Option<crate::mir_analysis::ReborrowProphecyInfo>,
}

impl ParsedContract {
    /// Apply a rewriting function to every `PureExpr` in this contract.
    ///
    /// This eliminates the need for each rewriting pass to enumerate all
    /// expression-holding fields individually. The callback receives a shared
    /// reference to each expression and returns the replacement expression.
    pub(in crate::callbacks) fn rewrite_all_exprs(
        &mut self,
        mut f: impl FnMut(&PureExpr) -> PureExpr,
    ) {
        for expr in &mut self.requires {
            *expr = f(expr);
        }
        for expr in &mut self.ensures {
            *expr = f(expr);
        }
        if let Some(result_expr) = &mut self.result_expr {
            *result_expr = f(result_expr);
        }
        if let Some(result_expr_spanned) = &mut self.result_expr_spanned {
            result_expr_spanned.expr = f(&result_expr_spanned.expr);
        }
        for expr in &mut self.call_assumptions {
            *expr = f(expr);
        }
        for expr in &mut self.pre_loop_call_assumptions {
            *expr = f(expr);
        }
        for expr in &mut self.call_obligations {
            *expr = f(expr);
        }
        for expr in &mut self.pre_loop_call_obligations {
            *expr = f(expr);
        }
        for expr in &mut self.post_loop_call_obligations {
            *expr = f(expr);
        }
        // Loop fields
        for expr in &mut self.loop_fields.invariants {
            *expr = f(expr);
        }
        for (_, _, invariants) in &mut self.loop_fields.per_loop_invariants {
            for expr in invariants {
                *expr = f(expr);
            }
        }
        for expr in &mut self.loop_fields.variants {
            *expr = f(expr);
        }
        for (_, _, variants) in &mut self.loop_fields.per_loop_variants {
            for expr in variants {
                *expr = f(expr);
            }
        }
        for group in &mut self.loop_fields.loop_obligation_groups {
            for expr in &mut group.obligations {
                *expr = f(expr);
            }
            if let Some(cond) = &mut group.condition {
                *cond = f(cond);
            }
        }
        // Mut borrow fields
        self.rewrite_mut_borrow_exprs(&mut f);
    }

    /// Rewrite mut-borrow-related expressions (indexed writes, delayed
    /// writeback assumptions, and final values) with the given function.
    ///
    /// Factored out so that [`rewrite_all_exprs_except_final_values`] can
    /// skip final_values while still processing the other mut-borrow fields.
    fn rewrite_mut_borrow_exprs(&mut self, f: &mut impl FnMut(&PureExpr) -> PureExpr) {
        if let Some(mut_borrow) = &mut self.mut_borrow.mut_borrow_body {
            for indexed_write in &mut mut_borrow.indexed_writes {
                indexed_write.index = f(&indexed_write.index);
                indexed_write.value = f(&indexed_write.value);
            }
            for assumption in &mut mut_borrow.delayed_writeback_assumptions {
                *assumption = f(assumption);
            }
            for final_expr in mut_borrow.final_values.values_mut() {
                *final_expr = f(final_expr);
            }
        }
    }

    /// Apply a rewriting function to contract expressions but NOT to
    /// `mut_borrow_body.final_values`.
    ///
    /// Box deref erasure (#2668) must erase spurious `Deref(Var("bx"))` from
    /// contract expressions (requires/ensures) because `ty_to_expr_sort_enriched`
    /// already peels the Box type. However, `final_values` contain MIR-extracted
    /// deref expressions like `Deref(Var("self.1"))` where the Deref represents
    /// actual `&mut` dereference semantics, NOT Box dereference. Stripping these
    /// breaks the final-value binding in the ay layer, causing `self.N_current_final`
    /// to be uninterpreted instead of bound to the computed expression.
    pub(in crate::callbacks) fn rewrite_all_exprs_except_final_values(
        &mut self,
        mut f: impl FnMut(&PureExpr) -> PureExpr,
    ) {
        for expr in &mut self.requires {
            *expr = f(expr);
        }
        for expr in &mut self.ensures {
            *expr = f(expr);
        }
        if let Some(result_expr) = &mut self.result_expr {
            *result_expr = f(result_expr);
        }
        if let Some(result_expr_spanned) = &mut self.result_expr_spanned {
            result_expr_spanned.expr = f(&result_expr_spanned.expr);
        }
        for expr in &mut self.call_assumptions {
            *expr = f(expr);
        }
        for expr in &mut self.call_obligations {
            *expr = f(expr);
        }
        // Loop fields
        for expr in &mut self.loop_fields.invariants {
            *expr = f(expr);
        }
        for (_, _, invariants) in &mut self.loop_fields.per_loop_invariants {
            for expr in invariants {
                *expr = f(expr);
            }
        }
        for expr in &mut self.loop_fields.variants {
            *expr = f(expr);
        }
        for (_, _, variants) in &mut self.loop_fields.per_loop_variants {
            for expr in variants {
                *expr = f(expr);
            }
        }
        for group in &mut self.loop_fields.loop_obligation_groups {
            for expr in &mut group.obligations {
                *expr = f(expr);
            }
            if let Some(cond) = &mut group.condition {
                *cond = f(cond);
            }
        }
        // Mut borrow fields: rewrite indexed_writes and delayed_writeback
        // but NOT final_values (their Deref wrappers are semantic).
        if let Some(mut_borrow) = &mut self.mut_borrow.mut_borrow_body {
            for indexed_write in &mut mut_borrow.indexed_writes {
                indexed_write.index = f(&indexed_write.index);
                indexed_write.value = f(&indexed_write.value);
            }
            for assumption in &mut mut_borrow.delayed_writeback_assumptions {
                *assumption = f(assumption);
            }
            // final_values intentionally excluded — see doc comment.
        }
    }
}
