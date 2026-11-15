// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{Sort, Term};
use tracing::debug;
use trust_wp_core::formula::{resolve_sort_name, BinOp, ExprSort, PureExpr};

use super::{
    resolve_view_var_name,
    sort_context::{reference_like_inner_sort, resolve_nameable_expr, DerivedKind},
    AYEncoder, SeqValue,
};
use crate::error::EncodingError;

impl AYEncoder {
    /// Ensure a named Seq carrier is bound to the canonical Seq sort.
    ///
    /// The proof_assert lane can reach synthesis after ambiguous collection
    /// dispatch has already bound the same carrier name on a fallback path
    /// (for example, `len` via FSet). In that case the variable term may
    /// exist without Seq sort metadata, and `get_or_declare_var` can reuse the
    /// stale binding instead of upgrading it. Rebind the carrier name onto a
    /// fresh Seq constant before asserting Seq projectors so synthesis always
    /// operates on a Seq-sorted term. (#2616)
    fn ensure_seq_carrier_term(&mut self, var_name: &str) -> Result<Term, EncodingError> {
        let seq_sort = self.get_seq_sort();
        let var_term = self.get_or_declare_var(var_name, seq_sort.clone())?;
        if self.solver.term_sort(var_term) == seq_sort {
            return Ok(var_term);
        }

        crate::encoder::unsoundness::increment(
            crate::encoder::unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
        );
        let role = format!("seq_synth_{}", self.seq_state.next_fresh_seq_lit_id());
        let repaired_term = self.declare_derived_source_var(var_name, &role, seq_sort.clone());
        self.var_env.record_split_source(var_name, var_term);
        self.rebind_var(var_name, repaired_term, seq_sort);
        Ok(repaired_term)
    }

    /// Synthesize a concrete empty `SeqValue` for Seq variables with `len == 0` (#1317).
    ///
    /// Detects either of these patterns:
    ///   `View(Var("x")).len() == 0`  (or `0 == View(Var("x")).len()`)
    ///   `Var("x").len() == 0`       (or `0 == Var("x").len()`)
    /// and creates a concrete `SeqValue` for the corresponding Seq carrier
    /// (`x_view` or `x`) with `{ arr: const_array(0), len: 0, offset: 0 }`.
    ///
    /// This enables the Array+Length encoding to produce ground Array terms
    /// for subsequent `push_back` operations on the same base variable. Without
    /// this, flat call-site assumptions like
    ///   `final_x_view == x_view.push_back(0)`
    ///   `final_x_view == x_view.push_back(1)`
    /// produce UF-based SeqValues (since `x_view` has no registered SeqValue),
    /// preventing ay's Array theory from reasoning about distinctness. With a
    /// concrete empty SeqValue, the push_back shape constraints become ground
    /// Array terms, making the contradictory flat assumptions UNSAT.
    pub(crate) fn try_synthesize_len_zero_seq_value(
        &mut self,
        expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<(), EncodingError> {
        self.try_synthesize_len_zero_seq_value_with_known_len(expr, prefix, None)
    }

    /// Synthesize a sequence whose zero length has already crossed an
    /// assertion boundary.
    ///
    /// Unlike the speculative expression-encoding helper above, this records
    /// the exact finite length in compile-time metadata.  That lets a following
    /// `push_back`/`index_logic` pair reduce to the same ground array index and
    /// therefore produce a small, strictly checkable proof.  Callers must use
    /// this only after asserting `expr` positively; a zero-length condition in
    /// an unselected branch is not global knowledge.
    pub(crate) fn try_synthesize_asserted_len_zero_seq_value(
        &mut self,
        expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<(), EncodingError> {
        self.try_synthesize_len_zero_seq_value_with_known_len(expr, prefix, Some(0))
    }

    fn try_synthesize_len_zero_seq_value_with_known_len(
        &mut self,
        expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
        known_len: Option<usize>,
    ) -> Result<(), EncodingError> {
        let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
            return Ok(());
        };

        // Try both orientations: len==0 and 0==len.
        let receiver_expr: &PureExpr = match (lhs.as_ref(), rhs.as_ref()) {
            (
                PureExpr::MethodCall {
                    receiver,
                    method,
                    args,
                },
                PureExpr::Int(0),
            ) if method == "len" && args.is_empty() => receiver.as_ref(),
            (
                PureExpr::Int(0),
                PureExpr::MethodCall {
                    receiver,
                    method,
                    args,
                },
            ) if method == "len" && args.is_empty() => receiver.as_ref(),
            _ => return Ok(()),
        };

        // Receiver must be a non-final Seq carrier: either View(Var(...)) or
        // a bare Var(...). Final receivers remain excluded because len-zero
        // synthesis seeds pre-state bases, not post-state snapshots.
        if !is_nonfinal_seq_carrier(receiver_expr) {
            return Ok(());
        }

        // Guard: skip Seq synthesis when the receiver has a non-Seq sort
        // annotation. FSet variables use `len()` but are Sort::Int, not Seq.
        // Without this guard, `eq(fset_var.len(), 0)` would pull the FSet
        // variable into Seq sort, causing sort mismatches with ghost aliases
        // and FSet method dispatch. (#2671)
        if let Some(annotation) = receiver_sort_annotation(receiver_expr) {
            if !annotation_is_seq_like(&annotation) {
                debug!(
                    "[len_zero_synth] skipping: receiver has non-Seq annotation {:?}",
                    annotation
                );

                return Ok(());
            }
        }

        // Resolve the SMT variable name: View(Var("x")) -> "x_view",
        // Var("x") -> "x".
        let Some(var_name) = resolve_seq_carrier_name(receiver_expr, prefix) else {
            return Ok(());
        };
        let var_term = self.ensure_seq_carrier_term(&var_name)?;

        // A prior push_back assumption can force an aux/projector-backed
        // SeqValue before the explicit len==0 fact arrives. The positive
        // len-zero fact is a stronger canonical representation for the base.
        if self.has_seq_value(var_term) {
            debug!("[len_zero_synth] replacing existing SeqValue for {var_name}");
        }

        // Create concrete empty SeqValue: const_array(Int, 0), len=0, offset=0.
        let zero = self.solver.int_const(0);
        let empty_arr = self.solver.const_array(Sort::Int, zero);

        debug!("[len_zero_synth] Synthesizing empty SeqValue for {var_name}");

        self.insert_seq_value(
            var_term,
            SeqValue {
                arr: empty_arr,
                len: zero,
                offset: zero,
                known_len,
            },
        );

        // Assert shape constraints so UF projectors agree with the concrete values.
        self.assert_seq_shape_constraints(var_term, empty_arr, zero, zero, "len_zero_synth")?;
        Ok(())
    }

    /// Reconstruct a chained push_back SeqValue from flat call-site assumptions (#1317).
    ///
    /// When the driver produces flat (non-chained) assumptions like:
    ///   `View(Var("x")).len() == 0`
    ///   `View(Final(Var("x"))) == View(Var("x")).push_back(0)`
    ///   `View(Final(Var("x"))) == View(Var("x")).push_back(1)`
    ///   ...
    ///   `View(Final(Var("x"))) == View(Var("x")).push_back(4)`
    ///
    /// The proof_assert pipeline can also emit the bare Seq-carrier forms:
    ///   `Var("x").len() == 0`
    ///   `Final(Var("x")) == Var("x").push_back(0)`
    ///   ...
    ///
    /// all 5 push_back assumptions use the same base variable, which is
    /// semantically incorrect (they should be chained with increasing Final
    /// depth). This method detects the pattern and synthesizes the intended
    /// chained SeqValue for the target variable `final_x_view`:
    ///   `push_back(push_back(...push_back(empty, 0)..., 3), 4)`
    ///
    /// The synthesized SeqValue uses Array `store` operations so postcondition
    /// checks like `select(arr, i) == i` use ay's read-over-write, which
    /// ay-dpll supports. Without this, the flat assumptions are contradictory
    /// but ay-dpll can't detect the contradiction (lacking Array extensionality).
    pub(crate) fn try_reconstruct_flat_push_back_chain(
        &mut self,
        requires: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<(), EncodingError> {
        let (len_zero_bases, push_back_groups) =
            Self::collect_flat_push_back_patterns(requires, prefix);

        // For each group where base has len==0, build chained SeqValue.
        for ((target_name, base_name), values) in &push_back_groups {
            if !len_zero_bases.contains(base_name) {
                continue;
            }
            if values.len() < 2 {
                // Single push_back is handled by normal encoding.
                continue;
            }

            let Ok(target_term) = self.ensure_seq_carrier_term(target_name) else {
                continue;
            };
            // Build chained Array: start with const_array(0), apply stores.
            let zero = self.solver.int_const(0);
            let mut arr = self.solver.const_array(Sort::Int, zero);
            let mut len: i64 = 0;

            // Values are in the order they appear in the requires, which
            // corresponds to the order of push calls in the source.
            for &val in values {
                let idx_term = self.solver.int_const(len);
                let val_term = self.solver.int_const(val);
                arr = self.solver.store(arr, idx_term, val_term);
                len = len.saturating_add(1);
            }

            let len_term = self.solver.int_const(len);

            // Register chained SeqValue for target, overriding any partial one.
            self.insert_seq_value(
                target_term,
                SeqValue {
                    arr,
                    len: len_term,
                    offset: zero,
                    known_len: None,
                },
            );

            // Assert shape constraints so UF projectors agree.
            self.assert_seq_shape_constraints(
                target_term,
                arr,
                len_term,
                zero,
                "flat_push_back_chain",
            )?;
        }
        Ok(())
    }

    /// Reconstruct already-chained push_back SeqValues independent of assertion order.
    ///
    /// Current MIR extraction can emit call-site assumptions in reverse source
    /// order:
    ///   `View(Final^5(x)) == View(Final^4(x)).push_back(4)`
    ///   ...
    ///   `View(Final(x)) == View(x).push_back(0)`
    ///   `View(x).len() == 0`
    ///
    /// Encoding those assumptions directly seeds intermediate final views from
    /// aux/projector-backed SeqValues before the base len-zero fact is seen.
    /// Once all requires are available, rebuild the linear chain from the
    /// len-zero base and overwrite those partial SeqValues with canonical
    /// store/constant-length values for postcondition indexing.
    pub(crate) fn try_reconstruct_chained_push_back_chain(
        &mut self,
        requires: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<(), EncodingError> {
        let (len_zero_bases, push_edges) =
            Self::collect_chained_push_back_patterns(requires, prefix);

        for base_name in &len_zero_bases {
            // Skip a base whose ground chain was already materialized by the
            // pre-encoding pre-seed pass. Re-running would assert the same
            // ground shape constraints a second time. (#1317 pre-seed)
            if self.seq_state.chain_base_reconstructed(base_name) {
                continue;
            }
            if push_edges
                .get(base_name)
                .is_some_and(|edges| edges.len() == 1)
            {
                self.reconstruct_push_back_chain_from_base(base_name, &push_edges)?;
            }
        }

        Ok(())
    }

    /// Pre-encoding pre-seed for LONG chained push_back patterns (#1317 pre-seed).
    ///
    /// Runs the chained reconstruction BEFORE per-assumption encoding so the
    /// per-assumption push_back encoding resolves its receiver against a
    /// concrete (ground) SeqValue and therefore emits GROUND-index store shape
    /// constraints instead of expensive SYMBOLIC-index ones. This is gated to
    /// chains of at least two push_back edges, which are the only ones whose
    /// symbolic-index store chain drives ay's Array theory into a timeout. A
    /// single push_back is left entirely to the existing post-encoding pass so
    /// that mut-borrow temporal-binding flows (which build their final-value
    /// term identities during encoding) keep their established term wiring and
    /// stay structurally satisfiable. (#2616)
    pub(crate) fn preseed_long_chained_push_back_chain(
        &mut self,
        requires: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<(), EncodingError> {
        const MIN_PRESEED_CHAIN_EDGES: usize = 2;

        let (len_zero_bases, push_edges) =
            Self::collect_chained_push_back_patterns(requires, prefix);

        for base_name in &len_zero_bases {
            if self.seq_state.chain_base_reconstructed(base_name) {
                continue;
            }
            if push_edges
                .get(base_name)
                .is_none_or(|edges| edges.len() != 1)
            {
                continue;
            }
            if Self::linear_chain_edge_count(base_name, &push_edges) < MIN_PRESEED_CHAIN_EDGES {
                continue;
            }
            self.reconstruct_push_back_chain_from_base(base_name, &push_edges)?;
        }

        Ok(())
    }

    /// Count the edges on the linear push_back chain rooted at `base_name`,
    /// following the same single-out-edge / no-cycle discipline as
    /// `reconstruct_push_back_chain_from_base`. (#1317 pre-seed)
    fn linear_chain_edge_count(
        base_name: &str,
        push_edges: &std::collections::HashMap<String, Vec<(String, i64)>>,
    ) -> usize {
        let mut count = 0usize;
        let mut current = base_name.to_string();
        let mut seen = std::collections::HashSet::new();
        while let Some(edges) = push_edges.get(&current) {
            if edges.len() != 1 {
                break;
            }
            if !seen.insert(current.clone()) {
                break;
            }
            count = count.saturating_add(1);
            current = edges[0].0.clone();
        }
        count
    }

    fn reconstruct_push_back_chain_from_base(
        &mut self,
        base_name: &str,
        push_edges: &std::collections::HashMap<String, Vec<(String, i64)>>,
    ) -> Result<(), EncodingError> {
        let zero = self.solver.int_const(0);
        let mut arr = self.solver.const_array(Sort::Int, zero);
        let mut len: i64 = 0;
        let mut current_name = base_name.to_string();
        let mut seen = std::collections::HashSet::new();

        // Record this base so the post-encoding reconstruction pass does not
        // re-materialize the same ground chain (#1317 pre-seed).
        self.seq_state.mark_reconstructed_chain_base(base_name);

        let base_term = self.ensure_seq_carrier_term(base_name)?;
        self.insert_seq_value(
            base_term,
            SeqValue {
                arr,
                len: zero,
                offset: zero,
                known_len: Some(0),
            },
        );
        self.assert_seq_shape_constraints(base_term, arr, zero, zero, "chained_push_back_base")?;

        while let Some(edges) = push_edges.get(&current_name) {
            if edges.len() != 1 {
                debug!(
                    "[chained_push_back] ambiguous outgoing edges for {current_name}: {edges:?}"
                );
                break;
            }
            if !seen.insert(current_name.clone()) {
                debug!("[chained_push_back] cycle detected at {current_name}");
                break;
            }

            let (target_name, value) = &edges[0];
            let write_index = self.solver.int_const(len);
            let value_term = self.solver.int_const(*value);
            arr = self.solver.store(arr, write_index, value_term);
            len = len.saturating_add(1);
            let len_term = self.solver.int_const(len);
            let known_len = usize::try_from(len).ok();

            let target_term = self.ensure_seq_carrier_term(target_name)?;
            self.insert_seq_value(
                target_term,
                SeqValue {
                    arr,
                    len: len_term,
                    offset: zero,
                    known_len,
                },
            );
            self.assert_seq_shape_constraints(
                target_term,
                arr,
                len_term,
                zero,
                "chained_push_back_chain",
            )?;
            debug!("[chained_push_back] synthesized {target_name} from {current_name} len={len}");

            current_name = target_name.clone();
        }

        Ok(())
    }

    #[allow(clippy::type_complexity)]
    fn collect_chained_push_back_patterns(
        requires: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> (
        Vec<String>,
        std::collections::HashMap<String, Vec<(String, i64)>>,
    ) {
        use std::collections::HashMap as StdHashMap;

        let mut len_zero_bases: Vec<String> = Vec::new();
        let mut push_edges: StdHashMap<String, Vec<(String, i64)>> = StdHashMap::new();

        for req in requires {
            let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = req else {
                continue;
            };

            match (lhs.as_ref(), rhs.as_ref()) {
                (
                    PureExpr::MethodCall {
                        receiver,
                        method,
                        args,
                    },
                    PureExpr::Int(0),
                )
                | (
                    PureExpr::Int(0),
                    PureExpr::MethodCall {
                        receiver,
                        method,
                        args,
                    },
                ) if method == "len" && args.is_empty() => {
                    if receiver_has_non_seq_annotation(receiver) {
                        continue;
                    }
                    if let Some(name) = resolve_nonfinal_seq_carrier_name(receiver, prefix) {
                        if !len_zero_bases.contains(&name) {
                            len_zero_bases.push(name);
                        }
                    }
                    continue;
                }
                _ => {}
            }

            let (target_expr, push_receiver, push_value) = match (lhs.as_ref(), rhs.as_ref()) {
                (
                    target,
                    PureExpr::MethodCall {
                        receiver,
                        method,
                        args,
                    },
                ) if method == "push_back" && args.len() == 1 => {
                    (target, receiver.as_ref(), &args[0])
                }
                (
                    PureExpr::MethodCall {
                        receiver,
                        method,
                        args,
                    },
                    target,
                ) if method == "push_back" && args.len() == 1 => {
                    (target, receiver.as_ref(), &args[0])
                }
                _ => continue,
            };

            if !is_final_seq_carrier(target_expr) {
                continue;
            }
            let Some(target_name) = resolve_seq_carrier_name(target_expr, prefix) else {
                continue;
            };
            let Some(source_name) = resolve_seq_carrier_name(push_receiver, prefix) else {
                continue;
            };
            let PureExpr::Int(value) = push_value else {
                continue;
            };

            push_edges
                .entry(source_name)
                .or_default()
                .push((target_name, *value));
        }

        (len_zero_bases, push_edges)
    }

    /// Collect len==0 bases and push_back target groups from flat assumptions.
    ///
    /// Returns `(len_zero_bases, push_back_groups)` where `push_back_groups` maps
    /// `(target_var_name, base_var_name)` to the list of pushed integer values.
    #[allow(clippy::type_complexity)]
    fn collect_flat_push_back_patterns(
        requires: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> (
        Vec<String>,
        std::collections::HashMap<(String, String), Vec<i64>>,
    ) {
        use std::collections::HashMap as StdHashMap;

        let mut len_zero_bases: Vec<String> = Vec::new();
        let mut push_back_groups: StdHashMap<(String, String), Vec<i64>> = StdHashMap::new();

        for req in requires {
            let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = req else {
                continue;
            };

            // Check for len==0 pattern.
            match (lhs.as_ref(), rhs.as_ref()) {
                (
                    PureExpr::MethodCall {
                        receiver,
                        method,
                        args,
                    },
                    PureExpr::Int(0),
                )
                | (
                    PureExpr::Int(0),
                    PureExpr::MethodCall {
                        receiver,
                        method,
                        args,
                    },
                ) if method == "len" && args.is_empty() => {
                    if receiver_has_non_seq_annotation(receiver) {
                        continue;
                    }
                    if let Some(name) = resolve_nonfinal_seq_carrier_name(receiver, prefix) {
                        len_zero_bases.push(name);
                    }
                    continue;
                }
                _ => {}
            }

            // Check for push_back pattern: final_X_view == X_view.push_back(N).
            let (target_expr, push_receiver, push_value) = match (lhs.as_ref(), rhs.as_ref()) {
                (
                    target,
                    PureExpr::MethodCall {
                        receiver,
                        method,
                        args,
                    },
                ) if method == "push_back" && args.len() == 1 => {
                    (target, receiver.as_ref(), &args[0])
                }
                (
                    PureExpr::MethodCall {
                        receiver,
                        method,
                        args,
                    },
                    target,
                ) if method == "push_back" && args.len() == 1 => {
                    (target, receiver.as_ref(), &args[0])
                }
                _ => continue,
            };

            // Target must be a final Seq carrier: View(Final(Var(...))) or
            // bare Final(Var(...)).
            if !is_final_seq_carrier(target_expr) {
                continue;
            }
            let Some(target_name) = resolve_seq_carrier_name(target_expr, prefix) else {
                continue;
            };

            // Receiver must be a non-final Seq carrier: View(Var(...)) or bare
            // Var(...).
            let Some(base_name) = resolve_nonfinal_seq_carrier_name(push_receiver, prefix) else {
                continue;
            };

            // Value must be a literal integer.
            let PureExpr::Int(val) = push_value else {
                continue;
            };

            push_back_groups
                .entry((target_name, base_name))
                .or_default()
                .push(*val);
        }

        (len_zero_bases, push_back_groups)
    }

    /// Synthesize a `SeqValue` for IndexMut point-write postconditions (#1317).
    ///
    /// Detects the pattern:
    ///   `View(Final(var)).index_logic(idx) == val`
    /// and creates a concrete `SeqValue` for the `final_var_view` SMT variable,
    /// representing `set(var_view, idx, val)` as an Array `store` operation.
    ///
    /// This bridges the gap between the extern spec postcondition (expressed as
    /// an equality on `index_logic`) and the Array+Length encoding: without this,
    /// the final-view variable has no registered `SeqValue`, so subsequent
    /// `seq_len_term` / `seq_index_term` calls fall back to UF projectors and
    /// ay cannot decide the resulting uninterpreted formula.
    pub(crate) fn try_synthesize_index_mut_seq_value(
        &mut self,
        expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<(), EncodingError> {
        // Pattern: BinOp(Eq, lhs, rhs) where one side is
        // MethodCall { receiver: View(Final(...)), method: "index_logic", args: [idx] }
        let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
            return Ok(());
        };

        // Try both orientations: index_logic==val and val==index_logic.
        let (target_name, idx_expr, val_expr) =
            if let Some(parts) = Self::extract_index_mut_pattern(lhs, rhs, prefix) {
                parts
            } else if let Some(parts) = Self::extract_index_mut_pattern(rhs, lhs, prefix) {
                parts
            } else {
                return Ok(());
            };

        // Resolve source variable name: derive "a_view" from "final_a_view".
        // View(Final(Var("a"))) target -> source is View(Var("a")) -> "a_view".
        // Uses the shared DerivedKind API instead of manual prefix stripping. (#2020)
        let Some(source_name) = DerivedKind::peel_final_view_prefix(&target_name) else {
            return Ok(());
        };

        // Look up SMT terms for target and source.
        let Some(target_term) = self.var_term(&target_name) else {
            return Ok(());
        };
        let seq_sort = self.get_seq_sort();
        let target_sort = self.solver.term_sort(target_term);
        if target_sort != seq_sort {
            return Err(EncodingError::sort_conflict(
                format!("index_mut_synth target `{target_name}`"),
                format!("{target_sort:?}"),
                format!("{seq_sort:?}"),
            ));
        }

        // Don't overwrite if target already has a SeqValue.
        if self.has_seq_value(target_term) {
            return Ok(());
        }

        let Some(source_term) = self.var_term(&source_name) else {
            return Ok(());
        };

        // Encode the index and value expressions.
        let Ok(idx_term) = self.encode_pure_impl(idx_expr, prefix) else {
            return Ok(());
        };
        let Ok(raw_val_term) = self.encode_pure_impl(val_expr, prefix) else {
            return Ok(());
        };
        let val_term = self.coerce_seq_element_to_int(raw_val_term);

        // Get source Array components (from registry or UF projectors).
        let Ok(source_arr) = self.seq_array_term(source_term) else {
            return Ok(());
        };
        let Ok(source_len) = self.seq_len_term(source_term) else {
            return Ok(());
        };
        let Ok(source_off) = self.seq_offset_term(source_term) else {
            return Ok(());
        };

        // Build: new_arr = store(source_arr, source_off + idx, val)
        let shifted_idx = self.solver.add(source_off, idx_term);
        let new_arr = self.solver.store(source_arr, shifted_idx, val_term);

        // Register the synthesized SeqValue: same len/offset, updated array.
        self.insert_seq_value(
            target_term,
            SeqValue {
                arr: new_arr,
                len: source_len,
                offset: source_off,
                known_len: None,
            },
        );

        // Assert shape constraints connecting UF projectors to the concrete values.
        // Without this, the bridge axiom (seq_index_logic -> select(seq_array, seq_offset+i))
        // cannot connect prior UF applications (from the assumption encoding) to the
        // concrete Array values from synthesis.
        self.assert_seq_shape_constraints(
            target_term,
            new_arr,
            source_len,
            source_off,
            "index_mut_synth",
        )?;

        // IndexMut frame conditions are quantifiers triggered on
        // `seq_index_logic(target, i)`. Without ground terms, single-round
        // E-matching may fail to discover the bridge chain (#1640).
        self.set_needs_seq_index_ground_terms();
        Ok(())
    }

    /// Extract the IndexMut point-write pattern from a candidate index side and value side.
    ///
    /// Returns `(target_name, index, value)` for either of these equivalent
    /// forms:
    ///
    /// 1. `MethodCall { receiver: View(Final(...)), method: "index_logic", args: [idx] }`
    /// 2. `View(MethodCall { receiver: Final(...), method: "index_logic", args: [idx] })`
    ///
    /// The second form appears in mutable-borrow postcondition transformation.
    pub(crate) fn extract_index_mut_pattern<'a>(
        index_side: &'a PureExpr,
        value_side: &'a PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<(String, &'a PureExpr, &'a PureExpr)> {
        match index_side {
            // Form 1: MethodCall(receiver = View(Final(...)), method = index_logic/index)
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                if !matches!(method.as_str(), "index_logic" | "index") || args.len() != 1 {
                    return None;
                }
                if !matches!(receiver.as_ref(), PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::Final(_)))
                {
                    return None;
                }
                let target_name = resolve_view_var_name(receiver, prefix)?;
                Some((target_name, &args[0], value_side))
            }

            // Form 2: View(MethodCall(receiver = Final(...), method = index_logic/index))
            PureExpr::View(inner) => {
                let PureExpr::MethodCall {
                    receiver,
                    method,
                    args,
                } = inner.as_ref()
                else {
                    return None;
                };
                if !matches!(method.as_str(), "index_logic" | "index") || args.len() != 1 {
                    return None;
                }
                if !matches!(receiver.as_ref(), PureExpr::Final(_)) {
                    return None;
                }
                let receiver_view = PureExpr::View(receiver.clone());
                let target_name = resolve_view_var_name(&receiver_view, prefix)?;
                Some((target_name, &args[0], value_side))
            }

            _ => None,
        }
    }
}

fn resolve_seq_carrier_name(
    expr: &PureExpr,
    prefix: Option<crate::encoder::sort_context::DerivedKind>,
) -> Option<String> {
    resolve_view_var_name(expr, prefix).or_else(|| resolve_nameable_expr(expr, prefix))
}

fn resolve_nonfinal_seq_carrier_name(
    expr: &PureExpr,
    prefix: Option<crate::encoder::sort_context::DerivedKind>,
) -> Option<String> {
    is_nonfinal_seq_carrier(expr).then(|| resolve_seq_carrier_name(expr, prefix))?
}

fn is_nonfinal_seq_carrier(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, _) => true,
        PureExpr::View(inner) => !matches!(inner.as_ref(), PureExpr::Final(_)),
        _ => false,
    }
}

fn is_final_seq_carrier(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Final(_) => true,
        PureExpr::View(inner) => matches!(inner.as_ref(), PureExpr::Final(_)),
        _ => false,
    }
}

/// Extract the `ExprSort` annotation from a Seq carrier receiver expression.
///
/// Returns the sort annotation if the receiver is a `Var(_, Some(sort))` or
/// `View(Var(_, Some(sort)))`. Used by `try_synthesize_len_zero_seq_value` to
/// skip Seq synthesis for non-Seq receivers like FSet (Sort::Int). (#2671)
fn receiver_sort_annotation(expr: &PureExpr) -> Option<trust_wp_core::formula::ExprSort> {
    match expr {
        PureExpr::Var(_, sort) => sort.clone(),
        PureExpr::View(inner) => match inner.as_ref() {
            PureExpr::Var(_, sort) => sort.clone(),
            _ => None,
        },
        _ => None,
    }
}

fn receiver_has_non_seq_annotation(expr: &PureExpr) -> bool {
    receiver_sort_annotation(expr).is_some_and(|annotation| !annotation_is_seq_like(&annotation))
}

fn annotation_is_seq_like(sort: &ExprSort) -> bool {
    if let Some(inner) = reference_like_inner_sort(sort) {
        return annotation_is_seq_like(inner);
    }
    match sort {
        ExprSort::Seq => true,
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            let type_name = name.rsplit("::").next().unwrap_or(&name);
            super::sort_context::sort_inference::is_seq_model_type(type_name)
        }
        _ => false,
    }
}
