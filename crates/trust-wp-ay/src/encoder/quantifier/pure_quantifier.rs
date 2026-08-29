// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pure expression quantifier encoding.
//!
//! Handles `forall`/`exists` over `PureExpr` with:
//! - Multi-variable collapsing from nested quantifiers
//! - Trigger synthesis (delegating to [`super::super::trigger`])
//! - Bool quantifier expansion (finite domain case splitting)
//! - Constructor equality elimination (delegating to [`super::super::quantifier_ctor_elim`])
//! - Unit-sorted and unused variable elimination
//!
//! Extracted from `quantifier.rs` as part of #1988.

use std::collections::HashSet;

use ay_dpll::api::{Sort, Term};
use tracing::debug;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::{
    super::{
        collect_bool_hints,
        quantifier_ctor_elim::{
            detect_constructor_eq, infer_constructor_arg_sort, infer_constructor_arg_sorts_batch,
            infer_method_call_usage_sort, infer_method_call_usage_sorts_batch,
        },
        trigger::{
            collect_ground_subexprs, collect_nested_quantifier_vars, collect_quantified_var_usage,
            synthesize_triggers,
        },
        AYEncoder,
    },
    QuantifierKind,
};
use crate::{
    encoder::sort_context::{collect_names_as_bool, DerivedKind},
    error::EncodingError,
};

impl AYEncoder {
    /// Resolve bound variable sort using all 8 priority levels.
    ///
    /// Called by both Bool expansion eligibility (Phase 6) and bound variable
    /// creation (Phase 7) to ensure identical resolution. Extracted to fix
    /// the 3-level vs 6-level discrepancy (#2186).
    ///
    /// Priority order:
    /// 1. Explicit `ExprSort` annotation (with Int→hint override for Seq)
    /// 2. Bool hint from body/trigger inference
    /// 3. `resolve_decl_sort` sort hint map
    /// 4. `{var}_view` Seq hint for `View(Var(v)).len()` patterns (#579)
    /// 5. Constructor argument inference from body (#1752)
    /// 6. Method-call usage sort inference from the body (#2696)
    /// 7. `postcondition_mut` receiver sort inference (#2151)
    /// 8. Fallback `Sort::Int`
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn resolve_quantifier_var_sort(
        &mut self,
        var_name: &str,
        var_sort: Option<&trust_wp_core::formula::ExprSort>,
        bool_names: &HashSet<String>,
        innermost_body: &PureExpr,
    ) -> Sort {
        self.resolve_quantifier_var_sort_with_precomputed(
            var_name,
            var_sort,
            bool_names,
            innermost_body,
            None,
            None,
            None,
        )
    }

    /// Resolve bound variable sort with optional pre-computed constructor arg
    /// sort, method-call usage sort, and postcondition_mut receiver sort. When
    /// `precomputed_ctor_sort`
    /// is `Some`, skips the per-variable tree walk in `infer_constructor_arg_sort`.
    /// When `precomputed_usage_sort` is `Some`, skips the per-variable tree walk
    /// in `infer_method_call_usage_sort`.
    /// When `precomputed_pcm_sort` is `Some`, skips the per-variable tree walk
    /// in `find_postcondition_mut_receiver_sort`.
    ///
    /// This is the batch-friendly variant used by `encode_pure_quantifier_impl`
    /// to avoid O(V*T) scaling (#2346).
    fn resolve_quantifier_var_sort_with_precomputed(
        &mut self,
        var_name: &str,
        var_sort: Option<&trust_wp_core::formula::ExprSort>,
        bool_names: &HashSet<String>,
        innermost_body: &PureExpr,
        precomputed_ctor_sort: Option<&Sort>,
        precomputed_usage_sort: Option<&Sort>,
        precomputed_pcm_sort: Option<&Sort>,
    ) -> Sort {
        let base_sort = if let Some(es) = var_sort {
            let explicit = self.sort_from_expr_sort(peel_quantifier_ref_annotation(es));
            // When parser annotates Int (the default fallback), allow sort
            // hints from body analysis to override. The parser cannot
            // distinguish Int-typed vs Seq-typed quantifier variables from
            // syntax alone. (#967)
            if explicit == Sort::Int {
                let hint_sort = self.resolve_decl_sort(var_name, None, Sort::Int);
                if hint_sort == Sort::Int {
                    explicit
                } else {
                    hint_sort
                }
            } else {
                explicit
            }
        } else if bool_names.contains(var_name) {
            Sort::Bool
        } else {
            let decl_sort = self.resolve_decl_sort(var_name, None, Sort::Int);
            if decl_sort == Sort::Int {
                // {var}_view Seq hint (#579)
                let view_name = DerivedKind::View.format_name(var_name);
                let view_sort = self.resolve_decl_sort(&view_name, None, Sort::Int);
                if view_sort == Sort::Int {
                    decl_sort
                } else {
                    view_sort
                }
            } else {
                decl_sort
            }
        };
        // Constructor argument sort inference (#1752)
        let ctor_sort = if base_sort == Sort::Int {
            if let Some(precomputed) = precomputed_ctor_sort {
                precomputed.clone()
            } else {
                infer_constructor_arg_sort(self, innermost_body, var_name).unwrap_or(base_sort)
            }
        } else {
            base_sort
        };
        // Method-call usage sort inference (#2696): when the bound variable
        // appears as a receiver of a recognized collection method (e.g.
        // `s.len()` or `m.lookup(k)`), infer the receiver sort from the
        // expected method family. Argument-position matches currently refine
        // only to `Int`, so the main value here is upgrading fallback-`Int`
        // binders to Seq/FMap before quantifier encoding.
        let usage_sort = if ctor_sort == Sort::Int {
            if let Some(precomputed) = precomputed_usage_sort {
                precomputed.clone()
            } else {
                infer_method_call_usage_sort(innermost_body, var_name).unwrap_or(ctor_sort)
            }
        } else {
            ctor_sort
        };
        // postcondition_mut receiver sort inference (#2151): when the bound
        // variable appears as a state argument (or receiver) in a
        // postcondition_mut call, inherit the closure environment sort from
        // the receiver. This prevents sort mismatches when the UF was declared
        // with a closure-env sort from axiom paths.
        if usage_sort == Sort::Int {
            if let Some(precomputed) = precomputed_pcm_sort {
                precomputed.clone()
            } else {
                self.find_postcondition_mut_receiver_sort(var_name, innermost_body)
                    .unwrap_or(usage_sort)
            }
        } else {
            usage_sort
        }
    }

    /// Encode a pure expression quantifier (forall or exists) with optional prefix.
    ///
    /// Handles multi-variable quantifiers: the parser decomposes `forall<i, j> body`
    /// into nested `Forall { var: "i", body: Forall { var: "j", body, triggers }, triggers }`.
    /// When triggers are present, all bound variables must be visible to ay in a single
    /// `forall_with_triggers` call (ay validates that each trigger term references at
    /// least one bound variable). This method detects the nesting pattern and collapses
    /// into a single multi-variable quantifier. (#610)
    ///
    /// Unified from the previously separate `encode_pure_forall_impl` and
    /// `encode_pure_exists_impl` methods which had nearly identical structure. (#626)
    #[allow(clippy::too_many_lines)]
    pub(in crate::encoder) fn encode_pure_quantifier_impl(
        &mut self,
        kind: QuantifierKind,
        var: &str,
        var_sort: Option<trust_wp_core::formula::ExprSort>,
        body: &PureExpr,
        triggers: &[Vec<PureExpr>],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Collect all variables from nested quantifiers that share the same triggers.
        // The parser clones triggers to each nesting level for multi-variable quantifiers.
        // Each variable carries its own sort annotation from the parser (#968).
        let mut vars_collected: Vec<(String, Option<trust_wp_core::formula::ExprSort>)> =
            vec![(var.to_string(), var_sort.clone())];
        let mut innermost_body = body;
        // Always collapse nested same-kind quantifiers when triggers match.
        // Previously guarded by `!triggers.is_empty()`, which prevented
        // collapsing triggerless nested quantifiers like
        // `exists<a> exists<b> x == Pair(a, b)`. Without collapsing,
        // constructor equality elimination (#1765) only sees the outer
        // variable, causing multi-variable patterns to fall through to
        // the normal quantifier encoder (which returns Unknown for
        // existentials over custom datatypes). Empty triggers trivially
        // match (`[] == []`), so the collapse is always safe. (#994)
        {
            loop {
                let (inner_var, inner_sort, inner_body, inner_triggers) = match innermost_body {
                    PureExpr::Forall {
                        var: v,
                        var_sort: s,
                        body: b,
                        triggers: t,
                    } if kind == QuantifierKind::Forall => (v, s.clone(), b, t),
                    PureExpr::Exists {
                        var: v,
                        var_sort: s,
                        body: b,
                        triggers: t,
                    } if kind == QuantifierKind::Exists => (v, s.clone(), b, t),
                    _ => break,
                };
                if inner_triggers == triggers {
                    vars_collected.push((inner_var.clone(), inner_sort));
                    innermost_body = inner_body;
                } else {
                    break;
                }
            }
        }

        // Trigger synthesis (#1018): when user-provided triggers are empty,
        // attempt to synthesize triggers from the quantifier body. This
        // improves ay's E-matching by providing explicit patterns instead
        // of relying on ay's indiscriminate auto-extraction.
        let mut synthesized_triggers: Vec<Vec<PureExpr>> = Vec::new();
        let mut synthesized_trigger_vars: Option<Vec<String>> = None;
        let effective_triggers: &[Vec<PureExpr>] = if triggers.is_empty() {
            // Collect all nested same-kind quantifier vars (collapse didn't
            // happen because triggers were empty).
            let (all_var_names, deep_body) = collect_nested_quantifier_vars(kind, var, body);
            synthesized_triggers = synthesize_triggers(&all_var_names, deep_body);
            if synthesized_triggers.is_empty() {
                triggers
            } else {
                synthesized_trigger_vars = Some(all_var_names.clone());
                // Re-collect vars and innermost body with the full nesting traversal,
                // now that we have triggers. Also update vars_collected and innermost_body
                // to reflect the multi-variable collection.
                vars_collected.clear();
                vars_collected.push((var.to_string(), var_sort));
                innermost_body = body;
                // Walk nested quantifiers to collect all vars (matching the
                // collapse logic structure but not requiring trigger equality).
                loop {
                    match innermost_body {
                        PureExpr::Forall {
                            var: v,
                            var_sort: s,
                            body: b,
                            triggers: t,
                        } if kind == QuantifierKind::Forall && t.is_empty() => {
                            vars_collected.push((v.clone(), s.clone()));
                            innermost_body = b;
                        }
                        PureExpr::Exists {
                            var: v,
                            var_sort: s,
                            body: b,
                            triggers: t,
                        } if kind == QuantifierKind::Exists && t.is_empty() => {
                            vars_collected.push((v.clone(), s.clone()));
                            innermost_body = b;
                        }
                        _ => break,
                    }
                }

                debug!(
                        "[trust-wp-ay] synthesized {} trigger pattern(s) for triggerless quantifier over [{}]",
                        synthesized_triggers.len(),
                        all_var_names.join(", "),
                    );

                &synthesized_triggers
            }
        } else {
            triggers
        };

        // Reflexive equality elimination (#2696): if the innermost body is
        // `lhs == rhs` where both sides are structurally identical, the
        // quantifier is trivially true (for both forall and exists with
        // inhabited domains — all Rust types are inhabited).
        //
        // This handles patterns like `ensures(u(*a) == u(*a))` (bug/206)
        // where the postcondition generates a quantifier over a trivially
        // true equality. Without this, the quantifier has no triggers and
        // ay-dpll returns quantifier-unhandled.
        //
        // Also handles the guarded form: `guard ==> (lhs == rhs)` with
        // identical lhs/rhs, which is trivially true regardless of the guard.
        //
        // Only applied when there are no user-provided triggers, to avoid
        // skipping trigger variable declarations that tests/callers expect.
        if effective_triggers.is_empty() && is_reflexive_equality(innermost_body) {
            return Ok(self.solver.bool_const(true));
        }

        // Infer bound-variable Bool sort from both body and trigger patterns.
        // Trigger-only Bool usage (e.g., {:pattern not(b)} with body=true)
        // must not default the quantified variable to Int.
        let mut bool_names = HashSet::new();
        let mut fn_names = HashSet::new();
        // Quantifier bodies are formulas. Include top-level bare vars
        // (e.g., `forall b. b`) in addition to contextual Bool scans.
        collect_names_as_bool(innermost_body, &mut bool_names, &mut fn_names);
        collect_bool_hints(innermost_body, &mut bool_names, &mut fn_names);
        for pattern in effective_triggers {
            for trigger_expr in pattern {
                collect_bool_hints(trigger_expr, &mut bool_names, &mut fn_names);
            }
        }

        // Per-variable elimination (#1065, #1198): filter out variables that
        // are vacuous in the quantifier. Works for both single-variable and
        // multi-variable quantifiers (after trigger synthesis collapsing).
        //
        // 1. Unit-sorted variables: `()` has exactly one inhabitant, so
        //    quantification over it is vacuous.
        // 2. Unused variables: `forall<x: T> P` ≡ `P` when `x` does not
        //    appear free in `P` and `T` is inhabited (all Rust types are).
        //
        // If all variables are eliminated, return the body directly.
        let quantified_var_names: Vec<String> = vars_collected
            .iter()
            .map(|(name, _)| name.clone())
            .collect();
        let quantified_var_usage =
            collect_quantified_var_usage(&quantified_var_names, innermost_body);
        vars_collected.retain(|(v, v_sort)| {
            // Eliminate Unit-sorted variables
            if *v_sort == Some(trust_wp_core::formula::ExprSort::Unit) {
                return false;
            }
            // Eliminate unused variables
            if !quantified_var_usage.mentions(v) {
                return false;
            }
            true
        });
        let retained_var_names: Vec<String> = vars_collected
            .iter()
            .map(|(name, _)| name.clone())
            .collect();
        let effective_triggers = filter_triggers_for_retained_vars(
            effective_triggers,
            &quantified_var_names,
            &retained_var_names,
        );
        let allow_invalid_trigger_fallback = synthesized_trigger_vars.is_some()
            || trigger_patterns_mention_vars(&effective_triggers, &quantified_var_names);
        if vars_collected.is_empty() {
            if let Some(info) = detect_constructor_eq(self, kind, innermost_body, &[]) {
                return self.eliminate_constructor_eq_quantifier(
                    kind,
                    innermost_body,
                    &info,
                    prefix,
                );
            }
            return self.encode_pure_impl(innermost_body, prefix);
        }

        // Constructor equality quantifier elimination (#1752, #1765):
        //   exists<v...> scrutinee == Constructor(v...)  →  is_ctor(scrutinee)
        //   forall<v...> scrutinee == Constructor(v...) ==> P(v...)
        //     →  is_ctor(scrutinee) ==> P[vi := sel_i(scrutinee)]
        //
        // Replaces quantifiers with quantifier-free datatype tester/selector
        // operations. Handles both single-variable (#1752) and multi-variable
        // (#1765) patterns. All constructor arguments must be distinct
        // quantifier variables for the elimination to fire.
        {
            let qvar_names: Vec<&str> = vars_collected.iter().map(|(v, _)| v.as_str()).collect();
            // Pre-declare stdlib datatypes needed for nested constructor
            // elimination. Without this, `detect_constructor_eq` cannot
            // recognize nested patterns like `OwnResult::Ok(Some(t))` because
            // the inner constructor's datatype (OptionInt) may not have been
            // declared yet — the body match only declares the outer datatype
            // (OwnResult). Missing the nested elimination forces a ay forall
            // quantifier requiring multi-round E-matching, which ay-dpll
            // cannot handle, producing the `self=Err(0), result=None`
            // counterexample on transpose. (#1296)
            self.ensure_nested_ctor_stdlib_datatypes(kind, innermost_body, &qvar_names);
            if let Some(info) = detect_constructor_eq(self, kind, innermost_body, &qvar_names) {
                // For nested constructor patterns like OwnResult::Ok(Some(t)),
                // the outer var_field_map is empty (its arg is the inner ctor,
                // not a qvar) and the actual qvar bindings live in inner_ctor.
                // Account for both levels when checking coverage. (#1296)
                let mapped_var_count = info.var_field_map.len()
                    + info
                        .inner_ctor
                        .as_ref()
                        .map_or(0, |ic| ic.var_field_map.len());
                if mapped_var_count == vars_collected.len() {
                    let var_list: Vec<&str> = info.var_field_map.iter().map(|(v, _)| *v).collect();
                    let inner_info = info
                        .inner_ctor
                        .as_ref()
                        .map(|ic| format!("({}({}))", ic.ctor_name, ic.var_field_map.len()))
                        .unwrap_or_default();
                    debug!(
                        "[trust-wp-ay] constructor equality elimination for {kind:?}<{}> \
                             with constructor {}{inner_info} on datatype {}",
                        var_list.join(", "),
                        info.ctor_name,
                        info.datatype.name,
                    );

                    return self.eliminate_constructor_eq_quantifier(
                        kind,
                        innermost_body,
                        &info,
                        prefix,
                    );
                }
            }
        }

        // Batch pre-compute expensive per-variable tree walks (#2346):
        // 1. Constructor arg sorts: single O(T) walk instead of O(V*T).
        // 2. Method-call usage sorts: single O(T) walk for receiver/key usage.
        // 3. postcondition_mut receiver sort: single O(T) walk, same result
        //    for all variables (it returns the closure env sort, not per-var).
        let batch_var_names: Vec<&str> = vars_collected.iter().map(|(v, _)| v.as_str()).collect();
        let batch_ctor_sorts =
            infer_constructor_arg_sorts_batch(self, innermost_body, &batch_var_names);
        let batch_usage_sorts =
            infer_method_call_usage_sorts_batch(innermost_body, &batch_var_names);
        // Cache the postcondition_mut receiver sort. This walks O(T) per
        // probe. The sort is the same for all variables that appear as
        // postcondition_mut state args (it's the closure environment sort),
        // so we probe each variable until one succeeds and cache that result
        // for all. This avoids the previous O(V*T) pattern where only the
        // first variable was probed — if it wasn't a postcondition_mut arg,
        // the cache was None and every subsequent resolve_quantifier_var_sort
        // would fall through to the per-variable tree walk. (#2346)
        let batch_pcm_sort: Option<Sort> = batch_var_names.iter().find_map(|var_name| {
            self.find_postcondition_mut_receiver_sort(var_name, innermost_body)
        });

        // Bool quantifier expansion (#1027, #1134, #1197): for Bool-sorted
        // variables, expand to case splits instead of creating a ay quantifier.
        // ay's quantifier engine doesn't enumerate Bool domains, causing
        // trivially decidable formulas to return Unknown.
        //
        // Case-split expansion is always complete for Bool (finite 2-element
        // domain), so it is preferred over triggered E-matching even when
        // triggers are available (#1197). Partial triggers that cover only
        // some Bool variables would block expansion without this change.
        //
        // Handles both single-variable (#1027) and multi-variable (#1134)
        // cases. Capped at 4 Bool variables (16 branches) to bound the
        // cartesian product expansion.
        if vars_collected.len() <= 4 {
            let mut all_bool = true;
            let mut bool_var_names = Vec::with_capacity(vars_collected.len());
            for (v, v_sort) in &vars_collected {
                let precomputed_ctor = batch_ctor_sorts.get(v.as_str());
                let qvar_sort = self.resolve_quantifier_var_sort_with_precomputed(
                    v,
                    v_sort.as_ref(),
                    &bool_names,
                    innermost_body,
                    precomputed_ctor,
                    batch_usage_sorts.get(v.as_str()),
                    batch_pcm_sort.as_ref(),
                );
                if qvar_sort != Sort::Bool {
                    all_bool = false;
                    break;
                }
                bool_var_names.push(v.as_str());
            }
            if all_bool && !bool_var_names.is_empty() {
                return self.encode_pure_multi_bool_expansion(
                    kind,
                    &bool_var_names,
                    innermost_body,
                    prefix,
                );
            }
        }

        // Create bound variables and bind them in scope
        let mut bound_vars = Vec::with_capacity(vars_collected.len());
        let mut bound_var_sorts = Vec::with_capacity(vars_collected.len());
        let mut all_old_bindings: Vec<Vec<(String, Option<Term>)>> = Vec::new();
        let mut all_old_sort_bindings: Vec<Vec<(String, Option<Sort>)>> = Vec::new();

        for (v, v_sort) in &vars_collected {
            let qvar_id = self.next_quantifier_var_id();

            let precomputed_ctor = batch_ctor_sorts.get(v.as_str());
            let qvar_sort = self.resolve_quantifier_var_sort_with_precomputed(
                v,
                v_sort.as_ref(),
                &bool_names,
                innermost_body,
                precomputed_ctor,
                batch_usage_sorts.get(v.as_str()),
                batch_pcm_sort.as_ref(),
            );
            let bound_var = self
                .solver
                .fresh_var(&format!("qvar_{v}_{qvar_id}"), qvar_sort.clone());
            bound_vars.push(bound_var);
            bound_var_sorts.push(qvar_sort.clone());

            // Temporarily bind the quantified variable under all name variants
            // that encoding sub-expressions might look up:
            //
            // 1. Base name `v` — used by direct Var("v") references.
            // 2. `old_v` — used when the body contains `Old(expr_with_v)`,
            //    which sets prefix=Some(Old) during recursive encoding (#2634).
            // 3. `prefix+v` — used when the quantifier itself is inside a
            //    prefixed context (e.g., `old(forall<v> ...)`).
            //
            // Without (2), `forall<i> old(v.get(i)) > 0` creates a free
            // `old_i` variable instead of using the quantifier-bound term,
            // disconnecting the trigger from the body and breaking E-matching.
            let mut bound_names = vec![v.clone()];
            // Always bind old_-prefixed name for Old(expr) inside body (#2634)
            let old_prefixed = DerivedKind::Old.format_name(v);
            if old_prefixed != *v {
                bound_names.push(old_prefixed);
            }
            if let Some(kind) = prefix {
                let prefixed = kind.format_name(v);
                if prefixed != *v && !bound_names.contains(&prefixed) {
                    bound_names.push(prefixed);
                }
            }
            let old_bindings: Vec<(String, Option<Term>)> = bound_names
                .iter()
                .cloned()
                .map(|name| {
                    let old = self.insert_var(name.clone(), bound_var);
                    (name, old)
                })
                .collect();
            all_old_bindings.push(old_bindings);
            let old_sort_bindings: Vec<(String, Option<Sort>)> = bound_names
                .into_iter()
                .map(|name| {
                    let old = self.insert_var_sort(name.clone(), qvar_sort.clone());
                    (name, old)
                })
                .collect();
            all_old_sort_bindings.push(old_sort_bindings);

            // Track this variable as quantifier-bound so that View(Var(v))
            // collapses to the bound variable instead of creating v_view. (#579)
            // Uses depth counter so nested quantifiers with the same name don't
            // prematurely remove the outer binding. (#579 audit)
            self.bind_quantifier_var(v.clone());
        }

        // Increment quantifier_depth so that inner LogicFnCall applications
        // are NOT registered with the ground pool — their arguments are bound
        // variables, not ground terms. (#1965, Lane 5)
        self.quantifier_state.inc_quantifier_depth();
        // Track exists depth for invariant body inlining (#726): only inline
        // inside exists scopes where ay-dpll's E-matching can't help.
        if kind == QuantifierKind::Exists {
            self.quantifier_state.inc_exists_quantifier_depth();
        }
        let body_result = self.encode_pure_impl(innermost_body, prefix);

        // Encode triggers with the same prefix (still inside quantifier scope)
        let encoded_triggers: Result<Vec<Vec<Term>>, EncodingError> = effective_triggers
            .iter()
            .map(|pattern| {
                pattern
                    .iter()
                    .map(|expr| self.encode_pure_impl(expr, prefix))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect();
        if kind == QuantifierKind::Exists {
            self.quantifier_state.dec_exists_quantifier_depth();
        }
        self.quantifier_state.dec_quantifier_depth();

        // Restore old bindings and quantifier-bound tracking (in reverse order)
        for (((v, _sort), old_bindings), old_sort_bindings) in vars_collected
            .iter()
            .zip(all_old_bindings.into_iter())
            .zip(all_old_sort_bindings.into_iter())
            .rev()
        {
            self.unbind_quantifier_var(v.as_str());
            for (name, old) in old_bindings {
                self.restore_var(&name, old);
            }
            for (name, old) in old_sort_bindings {
                self.restore_var_sort(&name, old);
            }
        }

        let body_term = body_result?;
        let trigger_patterns = encoded_triggers?;
        if let Some(vars) = &synthesized_trigger_vars {
            self.record_synthesized_triggers(vars, &synthesized_triggers);
        }

        // Ground sub-expression registration (#2696): walk the quantifier body
        // to find LogicFnCall/MethodCall nodes that are completely ground (don't
        // mention any bound variable). Re-encode them at quantifier_depth == 0
        // so they are registered in the ground pool for E-matching support.
        //
        // Example: in `forall<i> 0 <= i && i < v.len() ==> f(v.get(i))`,
        // the sub-expression `v.len()` is ground. Having it in the ground pool
        // allows axioms about `seq_len` to be instantiated, providing the solver
        // with facts like `seq_len(v) >= 0` that help close the obligation.
        //
        // Only perform this at the outermost quantifier (quantifier_depth == 0)
        // to avoid re-encoding inside nested quantifier scopes. The re-encoding
        // happens at depth 0 which naturally registers in the ground pool.
        if self.quantifier_state.quantifier_depth() == 0 {
            let all_bound_var_names: Vec<String> = vars_collected
                .iter()
                .map(|(name, _)| name.clone())
                .collect();
            let ground_subexprs = collect_ground_subexprs(innermost_body, &all_bound_var_names);
            for ground_expr in &ground_subexprs {
                // Re-encode at depth 0 — this will trigger ground pool registration
                // in the logic_fn dispatch path (which checks quantifier_depth == 0).
                // Errors are silently ignored: ground sub-expression encoding may
                // fail for expressions that rely on bindings from the quantifier
                // scope (e.g., if our ground analysis missed a dependency). This
                // is a best-effort optimization.
                let _ = self.encode_pure_impl(ground_expr, prefix);
            }
        }

        // Constant body optimization (#1296): if the encoded body is a boolean
        // constant, the quantifier is trivially decidable. This handles cases
        // like `forall<x> x.trivial_invariant()` where the invariant inlines
        // to `true` during encoding but was not detectable at the PureExpr level.
        // forall<x> true = true, forall<x> false = false,
        // exists<x> true = true, exists<x> false = false (inhabited domain).
        let true_term = self.solver.bool_const(true);
        let false_term = self.solver.bool_const(false);
        if body_term == true_term || body_term == false_term {
            return Ok(body_term);
        }

        // Witness-based existential elimination (#726): for exists quantifiers
        // over Int-sorted variables with non-constant bodies, try substituting
        // candidate witnesses at the PureExpr level.
        //
        // If P(c) encodes to `true` for any witness c, the existential is
        // trivially satisfied → return `true`.
        //
        // The witness pool is the small literal baseline `{0, 1, -1}` *plus*
        // ground index terms derived from the body structure (gap
        // existential-witness-probe-too-narrow). For the canonical membership
        // shape `0 <= i && i < L && P(self.get(i))` the satisfying witness is
        // almost never a small literal — it is a Seq index such as `L - 1`, a
        // loop counter, or another ground term already in scope. We harvest
        // those ground terms from the body (see
        // [`collect_ground_int_witness_candidates`]) and probe them ahead of the
        // literals. For multi-variable exists we try a bounded cartesian product
        // over the candidate pool instead of only the same-value-for-all
        // diagonal.
        //
        // This handles cases like `exists x. x > 0` (after type invariant
        // body inlining) where the body is decidable for specific values
        // but ay-dpll cannot decide the quantified version due to the lack
        // of E-matching triggers on pure arithmetic, as well as
        // `contains`-style existentials over a Seq (slices/01, hillel) whose
        // witness is `L - 1` / a loop counter.
        //
        // Sound because: P(c) = true → exists x. P(x) = true (existential
        // introduction). Every candidate is ground w.r.t. the bound variables,
        // so substitution never re-introduces a quantified variable, and
        // failing to find a witness only leaves the result Unknown — it can
        // never report a true existential as false.
        //
        // Not applied to forall: ay-dpll handles forall falsification via
        // Skolemization of the negated postcondition + E-matching, which
        // works even with quantified body axioms present. The witness
        // approach for forall interacts badly with quantified type invariant
        // axioms (ay-dpll returns Unknown instead of SAT).
        if kind == QuantifierKind::Exists
            && vars_collected.len() <= MAX_WITNESS_PROBE_VARS
            && bound_var_sorts.iter().all(|sort| *sort == Sort::Int)
        {
            let bound_var_names: Vec<String> =
                vars_collected.iter().map(|(v, _)| v.clone()).collect();
            // Per-variable witness pool: ground index terms harvested from the
            // body (loop counters, `L`, `L - 1`, other in-scope ground ints)
            // followed by the small literal baseline. All entries are ground
            // w.r.t. the bound variables.
            let mut witnesses: Vec<PureExpr> =
                collect_ground_int_witness_candidates(innermost_body, &bound_var_names);
            for lit in [0_i64, 1, -1] {
                let cand = PureExpr::Int(lit);
                if !witnesses.contains(&cand) {
                    witnesses.push(cand);
                }
            }
            witnesses.truncate(MAX_WITNESS_CANDIDATES);

            let found = 'witness: {
                // Bounded cartesian product over the witness pool. Each
                // assignment maps every bound variable to one (independent)
                // candidate; the diagonal (same candidate for all variables) is
                // tried first to preserve the legacy `{0,1,-1}` behaviour.
                for assignment in
                    witness_assignments(bound_var_names.len(), &witnesses, MAX_WITNESS_ASSIGNMENTS)
                {
                    let mut subs = std::collections::HashMap::new();
                    for (v, cand) in bound_var_names.iter().zip(assignment.iter()) {
                        subs.insert(v.clone(), cand.clone());
                    }
                    let witness_body = innermost_body.substitute(&subs);
                    // Re-encode under a synthetic existential scope so the
                    // same invariant-body inlining used by the original
                    // quantifier body also applies to witness probes.
                    self.quantifier_state.inc_quantifier_depth();
                    self.quantifier_state.inc_exists_quantifier_depth();
                    // tract19: the substitution above erased the binder, so a
                    // body mentioning `^x` now reads `Final(Int(c))`. Mark the
                    // scope so the encoder still applies the Phase-1
                    // bound-variable rule to it instead of the
                    // borrowed-place refusal. Every bound sort here is
                    // `Sort::Int`, so no prophecy carrier is involved.
                    self.quantifier_state.inc_binder_substitution_depth();
                    let witness_result = self.encode_pure_impl(&witness_body, prefix);
                    self.quantifier_state.dec_binder_substitution_depth();
                    self.quantifier_state.dec_exists_quantifier_depth();
                    self.quantifier_state.dec_quantifier_depth();
                    if let Ok(witness_term) = witness_result {
                        if witness_term == true_term {
                            break 'witness true;
                        }
                    }
                }
                false
            };
            if found {
                return Ok(true_term);
            }
        }

        // Create the quantifier with triggers if present
        if trigger_patterns.is_empty() {
            kind.apply_simple(&mut self.solver, &bound_vars, body_term)
                .map_err(|err| EncodingError::solver_error(err.to_string()))
        } else {
            let trigger_refs: Vec<&[Term]> = trigger_patterns.iter().map(Vec::as_slice).collect();
            match kind.apply_with_optional_invalid_trigger_fallback(
                &mut self.solver,
                &bound_vars,
                body_term,
                &trigger_refs,
                allow_invalid_trigger_fallback,
            ) {
                Ok((term, fell_back)) => {
                    if fell_back {
                        debug!(
                            "[trust-wp-ay] synthesized trigger rejected for {kind:?}<{}>; \
                             falling back to triggerless quantifier",
                            vars_collected
                                .iter()
                                .map(|(name, _)| name.as_str())
                                .collect::<Vec<_>>()
                                .join(", "),
                        );
                    }
                    Ok(term)
                }
                Err(err) => Err(EncodingError::solver_error(err.to_string())),
            }
        }
    }
}

/// Maximum number of bound variables an existential witness probe will handle.
///
/// Raised from the historical hard-coded `2` to `3` so common three-index
/// membership/permutation existentials are reachable, while still bounding the
/// cartesian product below (`MAX_WITNESS_ASSIGNMENTS`).
/// (gap existential-witness-probe-too-narrow)
const MAX_WITNESS_PROBE_VARS: usize = 3;

/// Maximum number of distinct candidate witnesses kept per variable. The pool
/// is `derived ground terms ++ {0, 1, -1}`; this clamp keeps the per-variable
/// branching factor small.
const MAX_WITNESS_CANDIDATES: usize = 8;

/// Maximum number of *derived* (body-harvested) candidates collected before the
/// `{0, 1, -1}` literal baseline is appended. Reserving room for the three
/// literals guarantees the legacy baseline survives the final `truncate`, so a
/// candidate-rich body never regresses a case the old `{0,1,-1}` probe solved.
const MAX_DERIVED_WITNESS_CANDIDATES: usize = MAX_WITNESS_CANDIDATES - 3;

/// Hard cap on the total number of (multi-variable) witness assignments probed.
/// Bounds the cartesian product so a 3-var × 8-candidate body probes at most
/// this many re-encodings.
const MAX_WITNESS_ASSIGNMENTS: usize = 24;

/// Yield up to `cap` witness assignments: a `Vec` of length `n_vars`, each entry
/// drawn (independently) from `candidates`. The diagonal assignments (same
/// candidate for every variable) are emitted first because they cover the
/// common single-shared-index case and the legacy `{0,1,-1}` behaviour; the
/// remaining cartesian-product assignments follow until the cap is hit.
///
/// With `candidates` clamped to `MAX_WITNESS_CANDIDATES` and
/// `n_vars <= MAX_WITNESS_PROBE_VARS` the full product is small; `cap` is a
/// belt-and-braces bound for the largest configurations.
fn witness_assignments(n_vars: usize, candidates: &[PureExpr], cap: usize) -> Vec<Vec<PureExpr>> {
    if n_vars == 0 || candidates.is_empty() || cap == 0 {
        return Vec::new();
    }
    let mut out: Vec<Vec<PureExpr>> = Vec::new();
    // Diagonal first (legacy + dominant single-index case).
    for cand in candidates {
        out.push(vec![cand.clone(); n_vars]);
        if out.len() >= cap {
            return out;
        }
    }
    if n_vars == 1 {
        // Single variable: the diagonal already enumerated every candidate.
        return out;
    }
    // Remaining cartesian product (skip the diagonal entries already emitted).
    let mut indices = vec![0usize; n_vars];
    loop {
        let is_diagonal = indices.iter().all(|&i| i == indices[0]);
        if !is_diagonal {
            out.push(indices.iter().map(|&i| candidates[i].clone()).collect());
            if out.len() >= cap {
                return out;
            }
        }
        // Increment the mixed-radix counter (least-significant position last).
        let mut pos = n_vars;
        loop {
            if pos == 0 {
                return out;
            }
            pos -= 1;
            indices[pos] += 1;
            if indices[pos] < candidates.len() {
                break;
            }
            indices[pos] = 0;
        }
    }
}

/// Harvest ground integer-sorted terms from an existential body to use as
/// witness candidates.
///
/// The target pattern is the canonical bounded-membership existential, e.g.
/// `0 <= i && i < seq.len() && seq[i] == elem` (slices/01, hillel `contains`),
/// whose satisfying witness is a Seq index — typically `seq.len() - 1`, a loop
/// counter like `*c` / `produced.len()`, or another ground index already in
/// scope. The historical `{0, 1, -1}` pool can never hit these, leaving the
/// existential Unknown.
///
/// Strategy:
///   1. Scan the body for comparison `BinOp`s involving a bound variable
///      (`i < L`, `L > i`, `i <= L`, …). The non-bound side `L`, when ground,
///      yields the upper-bound candidates `L` and `L - 1` (right-open vs
///      right-closed bounds; `L - 1` is the dominant `contains` witness).
///   2. Collect ground `.len()` method-call results (and `len - 1`) found
///      anywhere in the body as additional candidates.
///
/// Every returned candidate is **ground w.r.t. the bound variables** — it is
/// rejected if it mentions any bound name — so substituting it can never
/// re-introduce a quantified variable, and the substituted body remains a
/// closed instance whose truth soundly witnesses the existential.
///
/// This is a heuristic *candidate generator*: extra or irrelevant candidates
/// only cost extra (bounded) re-encodings; missing the right candidate merely
/// leaves the result Unknown (the legacy behaviour). It can never make a true
/// existential look false.
fn collect_ground_int_witness_candidates(body: &PureExpr, bound_vars: &[String]) -> Vec<PureExpr> {
    use trust_wp_core::formula::BinOp;

    fn is_ground(expr: &PureExpr, bound_vars: &[String]) -> bool {
        !crate::encoder::trigger::expr_mentions_any_var(expr, bound_vars)
    }

    fn mentions_bound(expr: &PureExpr, bound_vars: &[String]) -> bool {
        crate::encoder::trigger::expr_mentions_any_var(expr, bound_vars)
    }

    fn sub_one(expr: &PureExpr) -> PureExpr {
        PureExpr::BinOp(
            std::sync::Arc::new(expr.clone()),
            BinOp::Sub,
            std::sync::Arc::new(PureExpr::Int(1)),
        )
    }

    fn push(cand: PureExpr, bound_vars: &[String], out: &mut Vec<PureExpr>) {
        if out.len() < MAX_DERIVED_WITNESS_CANDIDATES
            && is_ground(&cand, bound_vars)
            && !out.contains(&cand)
        {
            out.push(cand);
        }
    }

    fn walk(expr: &PureExpr, bound_vars: &[String], depth: usize, out: &mut Vec<PureExpr>) {
        use trust_wp_core::formula::BinOp;
        if depth > crate::encoder::MAX_ENCODING_DEPTH || out.len() >= MAX_DERIVED_WITNESS_CANDIDATES
        {
            return;
        }
        match expr {
            // Comparison: extract the ground bound when one side is bound.
            PureExpr::BinOp(l, op, r)
                if matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) =>
            {
                // `i < L` / `i <= L`: ground RHS is the upper bound.
                if mentions_bound(l, bound_vars) && is_ground(r, bound_vars) {
                    push((**r).clone(), bound_vars, out);
                    push(sub_one(r), bound_vars, out);
                }
                // `L > i` / `L >= i`: ground LHS is the upper bound.
                if mentions_bound(r, bound_vars) && is_ground(l, bound_vars) {
                    push((**l).clone(), bound_vars, out);
                    push(sub_one(l), bound_vars, out);
                }
                walk(l, bound_vars, depth + 1, out);
                walk(r, bound_vars, depth + 1, out);
            }
            PureExpr::BinOp(l, _, r) => {
                walk(l, bound_vars, depth + 1, out);
                walk(r, bound_vars, depth + 1, out);
            }
            // Ground `.len()` calls are prime index-bound candidates; also
            // recurse to find them nested under View/args.
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                if method == "len" && is_ground(expr, bound_vars) {
                    push(expr.clone(), bound_vars, out);
                    push(sub_one(expr), bound_vars, out);
                }
                walk(receiver, bound_vars, depth + 1, out);
                for a in args {
                    walk(a, bound_vars, depth + 1, out);
                }
            }
            PureExpr::UnOp(_, inner)
            | PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => {
                walk(inner, bound_vars, depth + 1, out);
            }
            PureExpr::Ite(c, t, e) => {
                walk(c, bound_vars, depth + 1, out);
                walk(t, bound_vars, depth + 1, out);
                walk(e, bound_vars, depth + 1, out);
            }
            PureExpr::LogicFnCall { args, .. } => {
                for a in args {
                    walk(a, bound_vars, depth + 1, out);
                }
            }
            // Do not descend into nested binders: their bodies bind further
            // variables not in `bound_vars`, so candidates harvested there are
            // not necessarily ground at this scope.
            _ => {}
        }
    }

    let mut out: Vec<PureExpr> = Vec::new();
    walk(body, bound_vars, 0, &mut out);
    out
}

fn filter_triggers_for_retained_vars<'a>(
    triggers: &'a [Vec<PureExpr>],
    original_vars: &[String],
    retained_vars: &[String],
) -> Vec<Vec<PureExpr>> {
    if triggers.is_empty() || original_vars == retained_vars {
        return triggers.to_vec();
    }

    triggers
        .iter()
        .filter(|pattern| {
            let mentions_retained = pattern
                .iter()
                .any(|expr| crate::encoder::trigger::expr_mentions_any_var(expr, retained_vars));
            if mentions_retained {
                return true;
            }

            // Drop only patterns that were tied to variables eliminated from
            // this quantifier. Patterns that mention no quantified variable are
            // still genuine invalid explicit triggers and should reach the
            // solver's normal InvalidTrigger path.
            !pattern
                .iter()
                .any(|expr| crate::encoder::trigger::expr_mentions_any_var(expr, original_vars))
        })
        .cloned()
        .collect()
}

fn trigger_patterns_mention_vars(triggers: &[Vec<PureExpr>], vars: &[String]) -> bool {
    triggers
        .iter()
        .flatten()
        .any(|expr| crate::encoder::trigger::expr_mentions_any_var(expr, vars))
}

pub(super) fn peel_quantifier_ref_annotation(sort: &ExprSort) -> ExprSort {
    match sort {
        // Quantifier-bound immutable references peel to the referent/current
        // sort so `forall<y: &T> ...` shares the same carrier as the ground
        // expression path.
        ExprSort::Ref(inner) => peel_quantifier_ref_annotation(inner),
        // Mutable-reference quantifiers keep their wrapper carrier. The
        // generic_deref path threads `inv(y)` / `precondition(y)` through the
        // mutable-reference placeholder sort, so collapsing `&mut T` all the
        // way to `T` disconnects the quantified and ground UF signatures. (#717)
        ExprSort::MutRef(inner) => {
            ExprSort::MutRef(Box::new(peel_quantifier_ref_annotation(inner)))
        }
        other => other.clone(),
    }
}

/// Check whether a PureExpr is a reflexive equality (`lhs == rhs` where
/// `lhs` and `rhs` are structurally identical).
///
/// Also handles:
/// - Guarded form: `guard ==> (lhs == rhs)` where lhs == rhs structurally
/// - Nested implications: `g1 ==> (g2 ==> (lhs == rhs))`
/// - Conjunction of reflexive equalities: `(a == a) && (b == b)`
///
/// Uses sort-agnostic comparison (#2673): the driver may attach different
/// `ExprSort` annotations to syntactically identical expressions (e.g.,
/// `Var("a", Some(Datatype("A")))` vs `Var("a", None)`). Since sorts are
/// hints for the encoder and don't affect semantic identity, ignoring them
/// is sound.
///
/// Sound because `x == x` is always true in SMT for any well-sorted `x`.
pub(crate) fn is_reflexive_equality(body: &PureExpr) -> bool {
    use trust_wp_core::formula::BinOp;
    match body {
        PureExpr::Bool(true) => true,
        PureExpr::BinOp(lhs, BinOp::Eq, rhs) => is_sort_agnostic_equal(lhs, rhs),
        // guard ==> consequent: true if consequent is reflexive (true implies
        // anything is vacuously reduced, and anything implies true is true).
        PureExpr::BinOp(_, BinOp::Implies, consequent) => is_reflexive_equality(consequent),
        // conjunction: (P && Q) is reflexive if both P and Q are reflexive
        PureExpr::BinOp(left, BinOp::And, right) => {
            is_reflexive_equality(left) && is_reflexive_equality(right)
        }
        // Ite: if both branches are reflexive, the whole is reflexive
        PureExpr::Ite(_, then_br, else_br) => {
            is_reflexive_equality(then_br) && is_reflexive_equality(else_br)
        }
        // Quantified formulas preserve trivial truth when their body does.
        PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => {
            is_reflexive_equality(body)
        }
        // Assumptions only add context; a trivially true body stays trivial.
        PureExpr::LetAssume { body, .. } => is_reflexive_equality(body),
        // Obligations must also be trivially true, since they are conjoined.
        PureExpr::LetObligation { obligation, body } => {
            is_reflexive_equality(obligation) && is_reflexive_equality(body)
        }
        _ => false,
    }
}

/// Compare two PureExpr trees for structural equality, ignoring `ExprSort`
/// annotations on `Var` nodes.
///
/// The driver may produce syntactically identical expressions with different
/// sort annotations — for instance, `Var("a", Some(Datatype("A")))` on one
/// side and `Var("a", None)` on the other. These are semantically the same
/// variable reference and should be considered equal for reflexive equality
/// detection.
///
/// This recursive comparison matches every PureExpr variant structurally:
/// - `Var(name1, _) == Var(name2, _)` when `name1 == name2`
/// - All other variants use exact structural equality on sub-expressions
///   (recursively via `is_sort_agnostic_equal`), with non-Var leaf fields
///   compared by `PartialEq`
pub(crate) fn is_sort_agnostic_equal(a: &PureExpr, b: &PureExpr) -> bool {
    match (a, b) {
        // Var: compare name only, ignore sort annotation
        (PureExpr::Var(n1, _), PureExpr::Var(n2, _)) => n1 == n2,
        // Literals
        (PureExpr::Bool(x), PureExpr::Bool(y)) => x == y,
        (PureExpr::Int(x), PureExpr::Int(y)) => x == y,
        (PureExpr::Float(x), PureExpr::Float(y)) => x == y,
        // Binary operations
        (PureExpr::BinOp(l1, op1, r1), PureExpr::BinOp(l2, op2, r2)) => {
            op1 == op2 && is_sort_agnostic_equal(l1, l2) && is_sort_agnostic_equal(r1, r2)
        }
        // Unary operations
        (PureExpr::UnOp(op1, e1), PureExpr::UnOp(op2, e2)) => {
            op1 == op2 && is_sort_agnostic_equal(e1, e2)
        }
        // If-then-else
        (PureExpr::Ite(c1, t1, e1), PureExpr::Ite(c2, t2, e2)) => {
            is_sort_agnostic_equal(c1, c2)
                && is_sort_agnostic_equal(t1, t2)
                && is_sort_agnostic_equal(e1, e2)
        }
        // Reference wrappers
        (PureExpr::Old(e1), PureExpr::Old(e2))
        | (PureExpr::Deref(e1), PureExpr::Deref(e2))
        | (PureExpr::Final(e1), PureExpr::Final(e2))
        | (PureExpr::View(e1), PureExpr::View(e2)) => is_sort_agnostic_equal(e1, e2),
        // Method calls
        (
            PureExpr::MethodCall {
                receiver: r1,
                method: m1,
                args: a1,
            },
            PureExpr::MethodCall {
                receiver: r2,
                method: m2,
                args: a2,
            },
        ) => {
            m1 == m2
                && is_sort_agnostic_equal(r1, r2)
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(x, y)| is_sort_agnostic_equal(x, y))
        }
        // Logic function calls
        (
            PureExpr::LogicFnCall { name: n1, args: a1 },
            PureExpr::LogicFnCall { name: n2, args: a2 },
        ) => {
            n1 == n2
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(x, y)| is_sort_agnostic_equal(x, y))
        }
        // Quantifiers: compare structure ignoring sort annotations on binders
        (
            PureExpr::Forall {
                var: v1,
                body: b1,
                triggers: t1,
                ..
            },
            PureExpr::Forall {
                var: v2,
                body: b2,
                triggers: t2,
                ..
            },
        )
        | (
            PureExpr::Exists {
                var: v1,
                body: b1,
                triggers: t1,
                ..
            },
            PureExpr::Exists {
                var: v2,
                body: b2,
                triggers: t2,
                ..
            },
        ) => {
            v1 == v2
                && is_sort_agnostic_equal(b1, b2)
                && t1.len() == t2.len()
                && t1.iter().zip(t2.iter()).all(|(p1, p2)| {
                    p1.len() == p2.len()
                        && p1
                            .iter()
                            .zip(p2.iter())
                            .all(|(x, y)| is_sort_agnostic_equal(x, y))
                })
        }
        // Let bindings
        (
            PureExpr::Let {
                var: v1,
                value: val1,
                body: b1,
            },
            PureExpr::Let {
                var: v2,
                value: val2,
                body: b2,
            },
        ) => v1 == v2 && is_sort_agnostic_equal(val1, val2) && is_sort_agnostic_equal(b1, b2),
        // Match: compare scrutinee and arms
        (
            PureExpr::Match {
                scrutinee: s1,
                arms: a1,
            },
            PureExpr::Match {
                scrutinee: s2,
                arms: a2,
            },
        ) => {
            is_sort_agnostic_equal(s1, s2)
                && a1.len() == a2.len()
                && a1.iter().zip(a2.iter()).all(|(arm1, arm2)| {
                    arm1.pattern == arm2.pattern && is_sort_agnostic_equal(&arm1.body, &arm2.body)
                })
        }
        // LetAssume: assumption => body
        (
            PureExpr::LetAssume {
                assumption: a1,
                body: b1,
            },
            PureExpr::LetAssume {
                assumption: a2,
                body: b2,
            },
        ) => is_sort_agnostic_equal(a1, a2) && is_sort_agnostic_equal(b1, b2),
        // LetObligation: obligation AND body
        (
            PureExpr::LetObligation {
                obligation: o1,
                body: b1,
            },
            PureExpr::LetObligation {
                obligation: o2,
                body: b2,
            },
        ) => is_sort_agnostic_equal(o1, o2) && is_sort_agnostic_equal(b1, b2),
        // Closure: compare params (ignoring sort annotations) and body
        (
            PureExpr::Closure {
                params: p1,
                body: b1,
            },
            PureExpr::Closure {
                params: p2,
                body: b2,
            },
        ) => {
            p1.len() == p2.len()
                && p1
                    .iter()
                    .zip(p2.iter())
                    .all(|((name1, _), (name2, _))| name1 == name2)
                && is_sort_agnostic_equal(b1, b2)
        }
        // Fall through: different variants are not equal.
        // Use PartialEq as a safe catch-all for any variants not listed
        // above (e.g., future additions to PureExpr).
        _ => a == b,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, PureExpr};

    use super::{is_reflexive_equality, peel_quantifier_ref_annotation};

    fn reflexive_eq(name: &str) -> PureExpr {
        PureExpr::BinOp(
            Arc::new(PureExpr::Var(name.to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var(name.to_string(), None)),
        )
    }

    #[test]
    fn bool_true_is_reflexive_equality() {
        assert!(is_reflexive_equality(&PureExpr::Bool(true)));
        assert!(!is_reflexive_equality(&PureExpr::Bool(false)));
    }

    #[test]
    fn quantified_trivial_bodies_are_reflexive() {
        let forall = PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Bool(true)),
            triggers: vec![],
        };
        let exists = PureExpr::Exists {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(reflexive_eq("x")),
            triggers: vec![],
        };
        let non_trivial_forall = PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Bool(false)),
            triggers: vec![],
        };

        assert!(is_reflexive_equality(&forall));
        assert!(is_reflexive_equality(&exists));
        assert!(!is_reflexive_equality(&non_trivial_forall));
    }

    #[test]
    fn let_assume_uses_body_truth() {
        let trivially_true = PureExpr::LetAssume {
            assumption: Arc::new(PureExpr::Bool(false)),
            body: Arc::new(PureExpr::Bool(true)),
        };
        let non_trivial = PureExpr::LetAssume {
            assumption: Arc::new(PureExpr::Bool(true)),
            body: Arc::new(PureExpr::Bool(false)),
        };

        assert!(is_reflexive_equality(&trivially_true));
        assert!(!is_reflexive_equality(&non_trivial));
    }

    #[test]
    fn let_obligation_requires_trivial_obligation_and_body() {
        let trivially_true = PureExpr::LetObligation {
            obligation: Arc::new(PureExpr::Bool(true)),
            body: Arc::new(reflexive_eq("x")),
        };
        let false_obligation = PureExpr::LetObligation {
            obligation: Arc::new(PureExpr::Bool(false)),
            body: Arc::new(PureExpr::Bool(true)),
        };
        let false_body = PureExpr::LetObligation {
            obligation: Arc::new(PureExpr::Bool(true)),
            body: Arc::new(PureExpr::Bool(false)),
        };

        assert!(is_reflexive_equality(&trivially_true));
        assert!(!is_reflexive_equality(&false_obligation));
        assert!(!is_reflexive_equality(&false_body));
    }

    #[test]
    fn peel_quantifier_ref_annotation_strips_ref_but_preserves_mut_ref() {
        let t = ExprSort::TypeParam(intern_sort_name("T"));
        let mut_ref_t = ExprSort::MutRef(Box::new(t.clone()));
        let nested = ExprSort::Ref(Box::new(mut_ref_t.clone()));

        assert_eq!(peel_quantifier_ref_annotation(&t), t);
        assert_eq!(peel_quantifier_ref_annotation(&nested), mut_ref_t);
    }
}
