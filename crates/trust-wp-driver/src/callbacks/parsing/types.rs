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
    /// Index (into `loop_analysis.loops`) of the loop whose lane produced this
    /// group. The group's VC may assume ONLY that loop's effective invariants:
    /// another loop's invariants and stable pre-loop bindings hold at that
    /// loop's header, not here (`let _y = 10 - i; i = 0; #[invariant(i == 0)]
    /// loop {}` would discharge the first loop's exit-tail check from `i == 0`;
    /// s40v5_seqloop_tail_var_reuse_invariant.rs). `None` assumes no loop
    /// invariant.
    pub(in crate::callbacks) loop_index: Option<usize>,
    /// Why `condition` reads a call result no premise constrains, when it
    /// does: a model of this group's VC picks that value freely, so it is
    /// not a counterexample (`LoopBodyExpr::condition_unstated`).
    pub(in crate::callbacks) condition_unstated: Option<String>,
    /// Names a store through a reference before the loop may have changed
    /// (`LoopBodyExpr::pre_loop_deref_stored_names`). The group's VC reads
    /// each at its entry value, so a model of it is a run of the program only
    /// when no premise links one to what an obligation reads (`PreLoopStoreLinks`).
    pub(in crate::callbacks) pre_loop_stored_names: HashSet<String>,
    /// Havoc variables the arithmetic walk bound for locals no loop writes
    /// (`LoopBodyObligations::unstated_entry_values`): code before the loop
    /// fixes their values and the VC states none, so a model of it is a run
    /// of the program only when no premise links one to what an obligation
    /// reads (`PreLoopStoreLinks`).
    pub(in crate::callbacks) unstated_entry_values: HashSet<String>,
    /// Whether an obligation is a fail-closed `false` the loop body walk
    /// injected under its path (`LoopBodyObligations::injected_fail_closed`):
    /// the group's VC is then unprovable, and a model of it refutes nothing.
    pub(in crate::callbacks) injected_fail_closed: bool,
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
    ///
    /// Groups are one per detected loop, in `loop_analysis.loops` order,
    /// FOLLOWED by condition-free groups (condition `None`), so the
    /// single-loop test counts loops, not groups.
    pub(in crate::callbacks) fn single_loop_condition(&self) -> Option<&PureExpr> {
        let loop_count = self
            .loop_analysis
            .as_ref()
            .map_or(self.loop_obligation_groups.len(), |analysis| {
                analysis.loops.len()
            });
        if loop_count == 1 {
            self.loop_obligation_groups
                .first()
                .and_then(|group| group.condition.as_ref())
        } else {
            None
        }
    }

    /// Why the single loop's condition reads a value no premise states, for
    /// single-loop functions; the exit assumptions carry its negation, so a
    /// model of a VC assuming them picks that value freely.
    pub(in crate::callbacks) fn single_loop_condition_unstated(&self) -> Option<&str> {
        self.single_loop_condition()?;
        self.loop_obligation_groups
            .first()
            .and_then(|group| group.condition_unstated.as_deref())
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
    /// The `&mut`-holding parameters of the contract's `Signature`
    /// (`mir_analysis::contract_signature`): the set a postcondition's states
    /// are read over (`formula::elaborate::postcondition_states`), here and at
    /// every call of the function (`call_signature`). Not the MIR-derived
    /// set above, which body extraction widens: a clause's dialect and the
    /// state of each `*p` must be decided over the one set every caller sees.
    pub(in crate::callbacks) state_params: HashSet<String>,
    /// Caller-side expiry pins for `&mut` borrows reached out of a call result
    /// (#prophecy-slots M5). Empty unless `projected_expiry` PROVED a death
    /// point; see that module's R0..R11 table.
    pub(in crate::callbacks) projected_final_pins: Vec<ProjectedFinalPin>,
    /// Parameters carrying a `&mut` whose call-site prophecy credit (`^p`
    /// collapsed onto `Final(<param>)`) is dead because something other than
    /// that call can still decide the referent: a later write, or an ESCAPE
    /// that leaves the borrow for the caller to resolve.
    ///
    /// Populated straight from MIR, like `mut_ref_param_names` and for the
    /// same reason: the premise it disqualifies is emitted whether or not
    /// mut-borrow body extraction succeeds, and the shape that needs it most
    /// (a write reaching the call through a loop back edge) is one extraction
    /// gives up on.
    pub(in crate::callbacks) stale_call_final_params: HashSet<String>,
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
    /// #1075/#1401 returning-path facts: conditions that hold on every path
    /// that returns from the function (a sibling arm can never return). They
    /// premise ONLY the function's own postconditions (`facts ==> ensures`,
    /// `contract_transform` step F); never requires, call obligations,
    /// loop obligations or proof_asserts.
    pub(in crate::callbacks) returning_path_facts: Vec<PureExpr>,
    /// Fail-closed marker: context extraction gave up (the rendered gap kind)
    /// before walking a body that can still carry obligations. A `Verified`
    /// function-contract verdict is demoted to unknown when this is set.
    pub(in crate::callbacks) extraction_fail_closed_reason: Option<String>,
    /// How many of `call_obligations` are the panic-unreachability goal for a
    /// body that can never return (`fn f() { panic!() }`).
    ///
    /// Every OTHER literal `false` in `call_obligations` is a lane failing
    /// closed because it could not MODEL something, and a refutation over one
    /// of those is trust-wp refuting its own placeholder (D-27). This one is
    /// different — Creusot states the same goal and trust-wp really can refute
    /// it — so the verdict gate subtracts it before asking whether the goal set
    /// carries a marker. Without the subtraction an unconditionally panicking
    /// body would stop reporting FAILED.
    ///
    /// A non-zero value also means THE BODY CAN NEVER RETURN, and that is how
    /// the verdict gate reads it. `panic!("msg")` lowers through a returning
    /// `Arguments::new_const` call with no spec, so the panic prologue injects
    /// a marker of its own; a count-minus-one rule would see `2 > 1` and
    /// withhold a refutation trust-wp can genuinely make. For a body with no
    /// reachable `Return` there is no user-facing claim to manufacture: every
    /// goal in it says only "this body is unreachable", which is the goal
    /// Creusot states too, so the whole marker count is subsumed rather than
    /// decremented.
    pub(in crate::callbacks) panic_unreachability_obligations: usize,
    /// How many of `call_obligations` are a callee's USER-WRITTEN
    /// `#[requires(false)]`, substituted at the call site.
    ///
    /// `PureExpr::Bool(false)` is the spelling of both an injected fail-closed
    /// marker and a written literal `false`, so the written ones are counted
    /// where they are written (`spec_apply::precondition`) and subtracted
    /// before the gate asks its question. This is the same distinction the
    /// ensures side draws by reading `parsed.call_obligations` rather than
    /// `effective_ensures`: a clause a user wrote is a clause a program can
    /// violate, and its refutation keeps its FAILED.
    pub(in crate::callbacks) user_written_false_obligations: usize,
    /// Switch edges the primary walk of a loop-free, exactly-valued body proved
    /// are never taken, on every path to the switch, each by an obligation in
    /// `call_obligations` or a value-stable literal discriminant (D-142).
    /// While this contract's verdict holds no execution crosses one, so
    /// `cap_clause_free_verdict` does not count a panic site only such an edge
    /// leads to.
    pub(in crate::callbacks) proved_dead_edges: crate::mir_analysis::ProvedDeadEdges,
    /// Loop-specific fields (invariants, variants, loop analysis).
    pub(in crate::callbacks) loop_fields: LoopFields,
    /// Mutable borrow analysis fields.
    pub(in crate::callbacks) mut_borrow: MutBorrowFields,
    /// Recognized recursive `&mut self` match-reborrow shape (rusthorn
    /// `take_some`), from which the prophecy-pinning premise is synthesized.
    pub(in crate::callbacks) reborrow_prophecy: Option<crate::mir_analysis::ReborrowProphecyInfo>,
}

impl ParsedContract {
    /// Rewrite the CALL-SITE OBLIGATION expressions and nothing else.
    ///
    /// The four vectors here are what a caller owes its callees; every other
    /// expression-holding field is the caller's own clauses, an assumption, or
    /// borrow bookkeeping. A pass that may only touch what is proved, never
    /// what is assumed, states that by taking this entry instead of
    /// `rewrite_all_exprs`.
    pub(in crate::callbacks) fn rewrite_each_call_obligation(
        &mut self,
        mut f: impl FnMut(&PureExpr) -> PureExpr,
    ) {
        for expr in &mut self.call_obligations {
            *expr = f(expr);
        }
        for expr in &mut self.pre_loop_call_obligations {
            *expr = f(expr);
        }
        for expr in &mut self.post_loop_call_obligations {
            *expr = f(expr);
        }
        for group in &mut self.loop_fields.loop_obligation_groups {
            for expr in &mut group.obligations {
                *expr = f(expr);
            }
        }
    }

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
        for expr in &mut self.returning_path_facts {
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
        for expr in &mut self.returning_path_facts {
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
