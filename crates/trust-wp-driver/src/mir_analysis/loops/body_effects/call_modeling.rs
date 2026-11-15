// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-site modeling: postcondition-based result constraint and Seq ghost mutations.

use std::{collections::HashMap, sync::Arc};

use rustc_middle::{
    mir::{BasicBlock, Local, Operand, Place},
    ty::TyKind,
};
use rustc_span::Spanned;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};
use trust_wp_driver::StdSpec;

use super::{
    super::{
        super::{
            call_resolve::{
                arg_names_for_def_id, extract_call_def_id, resolve_trait_method_def_id,
            },
            effects::CallEffects,
            extract::{callee_invariant_premises, machine_int_range_fact, stale_arguments},
            is_fallback_arg_placeholder,
            spec_apply::{
                apply_postconditions_for_loop_body_with_effects, apply_postconditions_with_effects,
                clause_read_as_written, collect_precondition_obligations, names_of_stale_arguments,
                reads_a_stale_argument, TranslatedArg,
            },
            translate::{translate_operand, ty_to_expr_sort, ty_to_expr_sort_enriched},
        },
        condition::base_var_name,
        CallSpecContext,
    },
    BodyExtractionCtx, BodyExtractionState, DroppedPremise,
};

/// What a loop-body call hands the loop VC beyond an effect a model already
/// recorded.
pub(super) enum CallPremise {
    /// Every postcondition clause is stated, as `facts` over `result`.
    Carried {
        result: Option<PureExpr>,
        facts: Vec<PureExpr>,
    },
    /// A postcondition the program supplies at this call is not stated.
    Dropped(DroppedPremise),
}

impl<'a, 'tcx> BodyExtractionCtx<'a, 'tcx> {
    /// Apply direct receiver updates for Seq ghost mutators.
    ///
    /// Recognizes:
    /// - `Seq::push_front_ghost(&mut self, x)` as `self' = self.push_front(x)`
    /// - `Seq::push_back_ghost(&mut self, x)` as `self' = self.push_back(x)`
    ///
    /// This is a targeted loop-extraction bridge for ghost for-loop invariants.
    /// Returns whether it recorded the call's effect.
    pub(super) fn apply_seq_ghost_mutation(
        &self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        state: &mut BodyExtractionState,
    ) -> bool {
        let Some(spec_ctx) = self.call_spec_ctx else {
            return false;
        };
        let Some(def_id) = extract_call_def_id(func) else {
            return false;
        };
        let path = spec_ctx.tcx.def_path_str(def_id);
        let is_front = path.ends_with("::push_front_ghost");
        let is_back = path.ends_with("::push_back_ghost");
        if !is_front && !is_back {
            return false;
        }
        if args.len() != 2 {
            return false;
        }

        let Some(receiver_expr) = translate_operand(&args[0].node, &state.working_exprs) else {
            return false;
        };
        let value_expr = translate_operand(&args[1].node, &state.working_exprs).or_else(|| {
            // Fallback: when the value operand can't be translated through
            // working_exprs (common in for-loops where the loop variable is
            // extracted via Option::Some downcast and the Iterator::next
            // result was havoced), resolve the local's debug name directly.
            match &args[1].node {
                Operand::Copy(place) | Operand::Move(place) => {
                    self.local_to_name.get(&place.local).map(|name| {
                        let sort = match self.call_spec_ctx {
                            Some(ref ctx) => ty_to_expr_sort_enriched(
                                ctx.tcx,
                                self.body.local_decls[place.local].ty,
                            ),
                            None => ty_to_expr_sort(self.body.local_decls[place.local].ty),
                        };
                        PureExpr::Var(name.clone(), sort)
                    })
                }
                Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
            }
        });
        let Some(value_expr) = value_expr else {
            return false;
        };
        let Some(receiver_name) = base_var_name(&receiver_expr) else {
            return false;
        };
        let receiver_name = receiver_name.to_string();
        // Receiver of push_back/concat is a Seq (ghost view of a collection).
        let receiver_var = PureExpr::Var(receiver_name.clone(), Some(ExprSort::Seq));

        let updated = if is_front {
            // Use push_front directly so the encoder produces seq_push_front(s, x),
            // which matches the R4 reverse axiom trigger. The previous encoding
            // seq(x).concat(s) produced seq_concat(seq_singleton(x), s) — a
            // structurally different SMT term that R4 could not fire on. (#2116)
            PureExpr::MethodCall {
                receiver: Arc::new(receiver_var.clone()),
                method: "push_front".to_string(),
                args: vec![value_expr],
            }
        } else {
            PureExpr::MethodCall {
                receiver: Arc::new(receiver_var.clone()),
                method: "push_back".to_string(),
                args: vec![value_expr],
            }
        };

        // Keep local_exprs and named effects in sync for all locals with this
        // debug name (handles shadowing conservatively).
        for (local, local_name) in self.local_to_name {
            if *local_name == receiver_name {
                state.working_exprs.insert(*local, updated.clone());
            }
        }
        state.effects.insert(receiver_name.clone(), updated);
        true
    }

    /// Record the post-state of a `&mut self` call as a deref body effect.
    ///
    /// A loop body call such as `v.push(x)`, `v.insert(i, x)`, or `v.swap(a, b)`
    /// mutates its receiver through `&mut self`. Its spec describes the new state
    /// with a `(^self)@`-shaped postcondition:
    ///
    /// - equational, e.g. `(^self)@ == self@.push_back(value)`
    /// - predicate, e.g. `(^self)@.exchange(self@, a@, b@)` (the swap spec)
    ///
    /// Without modeling, the call destination carries no `result == <expr>`
    /// postcondition, so `try_model_call_result` returns `None` and the receiver
    /// is havoced — the `(^self)@` post-state never reaches the loop VC, and the
    /// `swap -> exchange -> permutation_of` fact is lost.
    ///
    /// This records a *deref* effect `deref_effects[receiver] = <new-view>`,
    /// mirroring how `apply_indexed_write_effect` records a point write
    /// (`View(Deref(receiver)).set(i, x)`). The new view is expressed entirely in
    /// terms of the OLD view `View(Deref(receiver))` (= `self@`) and the call
    /// arguments, so the consumer's `build_prime_substitutions` constrains
    /// `receiver_prime_current = <new-view>` and the existing point-write /
    /// length-frame preservation machinery (#1295, 2c25f56) carries the
    /// `(^self)@` facts to the loop preservation VC.
    ///
    /// SOUND: only the closed-form new view that the spec *guarantees* is
    /// asserted. Calls whose `(^self)@` post-state we cannot express as a closed
    /// form are left to the existing havoc fallback (we record nothing and
    /// `apply_assignments` removes the receiver effect on the call's destination).
    ///
    /// Returns the index of the `ensures` clause the recorded post-state
    /// states, so the call's premise accounting knows that clause is carried.
    pub(super) fn apply_mut_self_post_state(
        &self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        state: &mut BodyExtractionState,
    ) -> Option<usize> {
        let spec_ctx = self.call_spec_ctx?;
        let def_id = extract_call_def_id(func)?;
        if args.is_empty() {
            return None;
        }

        // The receiver must be passed by mutable reference: a `&mut self` method.
        // Restricting to `&mut` receivers keeps this sound — a by-value or `&self`
        // receiver cannot have its caller-visible state mutated, so a `(^self)@`
        // clause there would not describe an in-place transition of a loop var.
        let self_ty = args[0].node.ty(&self.body.local_decls, spec_ctx.tcx);
        if !matches!(
            self_ty.kind(),
            TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
        ) {
            return None;
        }

        // Resolve the receiver's loop-visible base name. `self@` in the spec maps
        // to `View(Deref(receiver))` so the deref effect is expressed over the
        // OLD pointee view, exactly like `apply_indexed_write_effect`.
        let receiver_expr = translate_operand(&args[0].node, &state.working_exprs)?;
        let receiver_name = base_var_name(&receiver_expr)?.to_string();

        let spec = match lookup_callee_spec(spec_ctx, self.body, func, def_id) {
            Some(spec) if !spec.ensures.is_empty() => spec,
            _ => return None,
        };

        // Translate call arguments and resolve parameter names, mirroring
        // `try_model_call_result` so user/std specs share substitution behavior.
        let translated_args = self.translate_args(args, &state.working_exprs);
        let hir_param_names = arg_names_for_def_id(spec_ctx.tcx, def_id);
        let param_names = hir_param_names.or_else(|| spec.param_names.clone());
        let callee = crate::mir_analysis::call_signature(
            spec_ctx.tcx,
            def_id,
            param_names.as_deref(),
            Some(crate::mir_analysis::CallSite {
                body: self.body,
                func,
            }),
        );
        let stale = names_of_stale_arguments(&translated_args, param_names.as_deref());

        // `self@` resolves to the OLD pointee view `View(Deref(receiver))`.
        let old_view = PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            receiver_name.clone(),
            Some(ExprSort::Seq),
        )))));

        // Build the symbolic-name → expression substitution map.
        // `self` binds to `Deref(receiver)` so `self@` becomes the old view; the
        // positional/param names bind to the translated call arguments.
        let mut substitutions: HashMap<String, PureExpr> = HashMap::new();
        substitutions.insert(
            "self".to_string(),
            PureExpr::Deref(Arc::new(PureExpr::Var(
                receiver_name.clone(),
                Some(ExprSort::Seq),
            ))),
        );
        if let Some(names) = param_names.as_deref() {
            for (idx, name) in names.iter().enumerate() {
                if name == "self" || name == "result" {
                    continue;
                }
                if let Some(arg) = translated_args.get(idx) {
                    substitutions.insert(name.clone(), arg.expr.clone());
                }
            }
        }
        // Std-spec positional aliases (`value`, `rhs`, etc.) point at the first
        // non-self argument, matching `insert_std_symbolic_substitutions`.
        if let Some(first_value) = translated_args.get(1) {
            for alias in ["value", "default", "arg", "rhs"] {
                substitutions
                    .entry(alias.to_string())
                    .or_insert_with(|| first_value.expr.clone());
            }
        }

        let (clause_idx, new_view) =
            self.mut_self_new_view(&spec.ensures, &callee, &stale, &old_view, &substitutions)?;
        state.deref_effects.insert(receiver_name, new_view);
        Some(clause_idx)
    }

    /// Find the closed-form `(^self)@` new view from a callee's `ensures`.
    ///
    /// Recognizes two postcondition shapes, both expressed against `old_view`
    /// (`self@`) after `substitutions` are applied:
    ///
    /// - equational: `(^self)@ == <seqexpr>` (e.g. `push_back`, `concat`,
    ///   `insert` shapes) → the new view is `<seqexpr>`.
    /// - exchange predicate: `(^self)@.exchange(self@, i, j)` → the new view is
    ///   the closed-form transposition `old.set(i, old[j]).set(j, old[i])`. This
    ///   double-`set` feeds the existing point-write / length-frame machinery and
    ///   is recognized by the consumer as a swap (which re-derives the literal
    ///   `exchange` term for the permutation axioms). (2c25f56, swap->exchange)
    ///
    /// Returns `None` (havoc fallback) when no clause matches a closed form,
    /// and otherwise the matched clause's index beside the new view.
    ///
    /// A clause is read only as written: one the call's state elaboration
    /// reads otherwise ([`clause_read_as_written`]), or one reading an
    /// argument whose translation is stale at the call, is no fact here.
    fn mut_self_new_view(
        &self,
        ensures: &[String],
        callee: &trust_wp_core::formula::elaborate::Signature,
        stale: &std::collections::HashSet<String>,
        old_view: &PureExpr,
        substitutions: &HashMap<String, PureExpr>,
    ) -> Option<(usize, PureExpr)> {
        for (clause_idx, clause) in ensures.iter().enumerate() {
            let Some(parsed) = clause_read_as_written(clause, callee) else {
                continue;
            };
            if reads_a_stale_argument(&parsed, stale).is_some() {
                continue;
            }
            // Equational shape: `(^self)@ == <seqexpr>`.
            if let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = &parsed {
                if is_final_self_view(lhs) {
                    let new_view = rhs.as_ref().substitute(substitutions);
                    if !mentions_final_self(&new_view) {
                        return Some((clause_idx, new_view));
                    }
                }
                if is_final_self_view(rhs) {
                    let new_view = lhs.as_ref().substitute(substitutions);
                    if !mentions_final_self(&new_view) {
                        return Some((clause_idx, new_view));
                    }
                }
            }
            // Exchange predicate: `(^self)@.exchange(self@, i, j)`.
            if let PureExpr::MethodCall {
                receiver,
                method,
                args,
            } = &parsed
            {
                if method == "exchange" && args.len() == 3 && is_final_self_view(receiver) {
                    let i = args[1].substitute(substitutions);
                    let j = args[2].substitute(substitutions);
                    // Closed-form transposition over the old view:
                    //   old.set(i, old.index_logic(j)).set(j, old.index_logic(i))
                    let old_at_i = index_logic(old_view.clone(), i.clone());
                    let old_at_j = index_logic(old_view.clone(), j.clone());
                    let set_i = set_call(old_view.clone(), i, old_at_j);
                    let set_ij = set_call(set_i, j, old_at_i);
                    return Some((clause_idx, set_ij));
                }
            }
        }
        None
    }

    /// The callee's postcondition as premises of the loop VC.
    ///
    /// Each clause not already carried by an effect (`carried_clause`) is
    /// stated at `result` — the modeled value, or a symbol naming the value
    /// this call returns on this iteration — under the path condition reaching
    /// the call and the callee's own premises at these arguments:
    /// `guard ∧ requires ∧ inv ⇒ ensures`. That is the callee's verified
    /// contract and nothing more, so it holds whether or not any lane
    /// discharges the precondition: a path that does not make the call, or
    /// makes it outside its precondition, gains nothing from it.
    ///
    /// A clause that cannot be stated that way is reported as dropped rather
    /// than approximated, because a loop VC without it has models the program
    /// rules out (loop_body_call_postcondition_premise_control).
    #[allow(clippy::too_many_arguments)] // one call site; the walk state is threaded through
    pub(super) fn call_postcondition_premise(
        &self,
        bb: BasicBlock,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        modeled_result: Option<&PureExpr>,
        carried_clause: Option<usize>,
        state: &BodyExtractionState,
    ) -> CallPremise {
        let def_id = extract_call_def_id(func);
        let iterator_step = def_id.zip(self.call_spec_ctx).is_some_and(|(def_id, ctx)| {
            let method = resolve_trait_method_def_id(ctx.tcx, def_id).unwrap_or(def_id);
            ctx.tcx.def_path_str(method).ends_with("Iterator::next")
        });
        let dropped = |what: String| {
            CallPremise::Dropped(DroppedPremise {
                block: bb,
                what,
                iterator_step,
                only_about: None,
            })
        };
        let Some(spec_ctx) = self.call_spec_ctx else {
            return dropped("a call's contract, with no callee contracts in scope".to_string());
        };
        let Some(def_id) = def_id else {
            return dropped(
                "the contract of a call whose target is not a function item".to_string(),
            );
        };
        let tcx = spec_ctx.tcx;
        let callee = tcx.def_path_str(def_id);
        let Some(spec) = lookup_callee_spec(spec_ctx, self.body, func, def_id) else {
            return dropped(format!(
                "the behaviour of `{callee}`, which has no contract"
            ));
        };
        let clauses: Vec<&String> = spec
            .ensures
            .iter()
            .enumerate()
            .filter(|(idx, _)| Some(*idx) != carried_clause)
            .map(|(_, clause)| clause)
            .collect();
        // A minted symbol is a value of the destination's type, whatever the
        // contract says: its machine-integer range holds on every path.
        let (result, type_facts) = match modeled_result {
            Some(modeled) => (Some(modeled.clone()), Vec::new()),
            None => match self.call_result_symbol(bb, destination) {
                Some((symbol, range)) => (Some(symbol), range.into_iter().collect()),
                None => (None, Vec::new()),
            },
        };
        if clauses.is_empty() {
            return CallPremise::Carried {
                result,
                facts: type_facts,
            };
        }
        let Some(result) = result else {
            return dropped(format!(
                "the postcondition of `{callee}`, whose result has no name here"
            ));
        };
        if state.path_guard_opaque {
            return dropped(format!(
                "the postcondition of `{callee}`, called under a branch whose condition does not \
                 translate"
            ));
        }
        let translated_args = self.translate_args(args, &state.working_exprs);
        if translated_args.iter().any(|arg| arg.is_fallback) {
            return dropped(format!(
                "the postcondition of `{callee}`, an argument of which does not translate"
            ));
        }
        // A stale argument reads the pointee's entry value, not its value at
        // the call, so neither side of `requires ⇒ ensures` could be stated
        // over it: the precondition would be checked at the wrong value.
        if translated_args.iter().any(|arg| arg.stale) {
            return dropped(format!(
                "the postcondition of `{callee}`, an argument of which reads a pointee after a \
                 store its translation does not see"
            ));
        }
        let param_names = arg_names_for_def_id(tcx, def_id).or_else(|| spec.param_names.clone());
        let signature = crate::mir_analysis::call_signature(
            tcx,
            def_id,
            param_names.as_deref(),
            Some(crate::mir_analysis::CallSite {
                body: self.body,
                func,
            }),
        );

        let mut posts = Vec::with_capacity(clauses.len());
        for clause in clauses {
            let mut effects = CallEffects::new();
            apply_postconditions_with_effects(
                std::slice::from_ref(clause),
                &signature,
                &result,
                &translated_args,
                param_names.as_deref(),
                &mut effects,
                true,
            );
            if effects.dropped_spec_clauses > 0
                || effects.assumptions.is_empty()
                || effects
                    .assumptions
                    .iter()
                    .any(|fact| !is_statable_call_fact(fact))
            {
                return dropped(format!("the postcondition `{clause}` of `{callee}`"));
            }
            posts.extend(effects.assumptions);
        }

        let mut premises = state.path_guard.clone();
        let mut requires = CallEffects::new();
        collect_precondition_obligations(
            &spec.requires,
            &translated_args,
            param_names.as_deref(),
            &mut requires,
        );
        if requires.dropped_spec_clauses > 0
            || requires
                .obligations
                .iter()
                .any(|pre| !is_statable_call_fact(pre))
        {
            return dropped(format!(
                "the postcondition of `{callee}`, whose precondition does not translate here"
            ));
        }
        premises.extend(requires.obligations);
        let Some(invariants) = callee_invariant_premises(
            tcx,
            self.body,
            func,
            def_id,
            spec_ctx.user_specs,
            spec_ctx.trait_specs,
            &translated_args,
        ) else {
            return dropped(format!(
                "the postcondition of `{callee}`, whose parameter invariants cannot be stated here"
            ));
        };
        premises.extend(invariants);

        let antecedent = premises
            .into_iter()
            .reduce(|acc, premise| PureExpr::BinOp(Arc::new(acc), BinOp::And, Arc::new(premise)));
        let facts = type_facts
            .into_iter()
            .chain(posts.into_iter().map(|post| match &antecedent {
                Some(antecedent) => {
                    PureExpr::BinOp(Arc::new(antecedent.clone()), BinOp::Implies, Arc::new(post))
                }
                None => post,
            }))
            .collect();
        CallPremise::Carried {
            result: Some(result),
            facts,
        }
    }

    /// The symbol naming the value a call returns on one iteration, with the
    /// machine-integer range of its type when it has one.
    ///
    /// Only a whole local whose type holds no reference gets one: a referent's
    /// post-state is a prophecy this walk does not track, and a projected
    /// destination is not the value of any one name.
    fn call_result_symbol(
        &self,
        bb: BasicBlock,
        destination: &Place<'tcx>,
    ) -> Option<(PureExpr, Option<PureExpr>)> {
        let spec_ctx = self.call_spec_ctx?;
        if !destination.projection.is_empty() {
            return None;
        }
        let ty = self.body.local_decls[destination.local].ty;
        if ty.is_unit()
            || ty
                .walk()
                .filter_map(|arg| arg.as_type())
                .any(|t| matches!(t.kind(), TyKind::Ref(..) | TyKind::RawPtr(..)))
        {
            return None;
        }
        let symbol = PureExpr::Var(
            format!(
                "__trust_wp_loop_call_result_{}_{}",
                bb.as_u32(),
                destination.local.as_u32()
            ),
            ty_to_expr_sort_enriched(spec_ctx.tcx, ty),
        );
        let range = machine_int_range_fact(spec_ctx.tcx, ty, symbol.clone());
        Some((symbol, range))
    }

    /// Try to model a call result using callee postconditions.
    ///
    /// If a spec context is available and the callee has a `result == <expr>`
    /// postcondition, returns the constrained result expression with arguments
    /// substituted. Returns `None` if no spec is found, the spec has no
    /// `result == <expr>` postcondition, or no spec context is available.
    ///
    /// The spec lookup follows the same priority chain as
    /// `collect_guarded_obligations`: user_specs → trait_specs → extern_specs
    /// → trait method fallback. (#1463)
    pub(super) fn try_model_call_result(
        &self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        dest_local: Local,
        working_exprs: &HashMap<Local, PureExpr>,
    ) -> Option<PureExpr> {
        let spec_ctx = self.call_spec_ctx?;
        let def_id = extract_call_def_id(func)?;

        // Translate call arguments against current working expressions.
        let translated_args = self.translate_args(args, working_exprs);

        // Look up spec: user_specs → trait_specs → extern_specs → trait method fallback.
        // Phase C (#963): uses spec_ctx.extern_specs instead of EXTERN_SPECS thread-local.
        let spec = lookup_callee_spec(spec_ctx, self.body, func, def_id)?;

        if spec.ensures.is_empty() {
            return None;
        }

        let hir_param_names = arg_names_for_def_id(spec_ctx.tcx, def_id);
        let param_names = hir_param_names.or_else(|| spec.param_names.clone());

        // Create a result variable for postcondition substitution.
        let dest_sort =
            ty_to_expr_sort_enriched(spec_ctx.tcx, self.body.local_decls[dest_local].ty);
        let result_var = PureExpr::Var(format!("$call_{}", dest_local.as_u32()), dest_sort);

        // Apply postconditions for loop body extraction. This variant also matches
        // `result@ == <expr>` patterns (e.g., Vec::len: `result@ == self@.len()`)
        // where the view is transparent for primitive return types. (#1463)
        // Effects (assumptions/obligations) are collected but not consumed — loop
        // body extraction only needs the return expression. (#963)
        let mut call_effects = CallEffects::new();
        let result_expr = apply_postconditions_for_loop_body_with_effects(
            &spec.ensures,
            &crate::mir_analysis::call_signature(
                spec_ctx.tcx,
                def_id,
                param_names.as_deref(),
                Some(crate::mir_analysis::CallSite {
                    body: self.body,
                    func,
                }),
            ),
            &result_var,
            &translated_args,
            param_names.as_deref(),
            &mut call_effects,
        );
        let result_expr = collapse_loop_scalar_identity_views(result_expr);

        // If the result is still the plain variable, the spec had no
        // `result == <expr>` postcondition — fall back to havoc.
        if result_expr == result_var {
            return None;
        }

        Some(result_expr)
    }

    /// The call's arguments translated against `working_exprs`, each marked
    /// stale where it reads a pointee after a store the translation does not
    /// see ([`stale_arguments`]), as every call-site lane marks them.
    fn translate_args(
        &self,
        args: &[Spanned<Operand<'tcx>>],
        working_exprs: &HashMap<Local, PureExpr>,
    ) -> Vec<TranslatedArg> {
        let Some(spec_ctx) = self.call_spec_ctx else {
            return Vec::new();
        };
        let stale = stale_arguments(Some(spec_ctx.tcx), self.body, args);
        args.iter()
            .enumerate()
            .map(|(idx, arg)| {
                let mut translated = if let Some(expr) = translate_operand(&arg.node, working_exprs)
                {
                    TranslatedArg::new(expr)
                } else {
                    let sort = ty_to_expr_sort_enriched(
                        spec_ctx.tcx,
                        arg.node.ty(&self.body.local_decls, spec_ctx.tcx),
                    );
                    TranslatedArg::fallback(crate::mir_analysis::fresh_fallback_arg_var(idx, sort))
                };
                translated.stale = stale.get(idx).copied().unwrap_or(false);
                translated
            })
            .collect()
    }

    /// Model `Option` adapters and `Option::unwrap` in loop bodies so a
    /// call-chain tail advance like `l = l.1.as_mut().unwrap()` produces a
    /// ground body effect (`l' == (*l).1.unwrap()`) instead of a havoc.
    /// (#counter-cons-tail)
    ///
    /// - `as_mut`/`as_ref`: modeled as the IDENTITY on the collapsed logic view
    ///   of the receiver's referent. The adapter re-borrows the same payload,
    ///   so at the view level (where borrows collapse to referent values) the
    ///   result's Some-ness and payload coincide with `*self`. The identity
    ///   lives only in `working_exprs` substitution — no cross-sort equality is
    ///   ever asserted; downstream facts are emitted on the substituted-through
    ///   expression.
    /// - `unwrap`/`expect`: modeled as the spec-level payload selector
    ///   `receiver.unwrap()` (the callee spec is `Some(result) == *self`, i.e.
    ///   `result == unwrap(*self)` on the non-panic continuation; the panic
    ///   path has no post-state, so this is the standard partial-correctness
    ///   modeling).
    ///
    /// SOUND: both models are literal consequences of the Option semantics on
    /// the non-panic continuation; a wrong effect would risk a false accept,
    /// so this is deliberately restricted to `Option`'s own methods by def
    /// path.
    pub(super) fn try_model_option_adapter_result(
        &self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        working_exprs: &HashMap<Local, PureExpr>,
    ) -> Option<PureExpr> {
        let spec_ctx = self.call_spec_ctx?;
        let def_id = extract_call_def_id(func)?;
        // Provenance: a local `Option` lookalike prints `Option::..` too.
        let path = crate::provenance::builtin_def_path_str(spec_ctx.tcx, def_id)?;
        // Only Option's own methods (avoid unrelated `as_mut`s on user types).
        if !(path.starts_with("std::option::Option")
            || path.starts_with("core::option::Option")
            || path.starts_with("Option::"))
        {
            return None;
        }
        let self_arg = args.first()?;
        let self_expr = translate_operand(&self_arg.node, working_exprs)?;
        if path.ends_with("::as_mut") || path.ends_with("::as_ref") {
            return Some(self_expr);
        }
        if path.ends_with("::unwrap") || path.ends_with("::expect") {
            return Some(PureExpr::MethodCall {
                receiver: Arc::new(self_expr),
                method: "unwrap".to_string(),
                args: Vec::new(),
            });
        }
        None
    }
}

/// Look up a callee spec following the same priority chain as
/// `collect_guarded_obligations`: user_specs → trait_specs → extern_specs →
/// trait method fallback. (#1463)
fn lookup_callee_spec<'tcx>(
    spec_ctx: CallSpecContext<'_, 'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    func: &rustc_middle::mir::Operand<'tcx>,
    def_id: rustc_hir::def_id::DefId,
) -> Option<StdSpec> {
    // Spec provenance: a builtin table contract describes this call only when
    // the code that runs is library code (see `provenance::builtin_spec_admission`).
    let admission = crate::provenance::builtin_spec_admission_for_operand(
        spec_ctx.tcx,
        func,
        Some(body.source.def_id()),
    );
    let extern_opt = if spec_ctx.extern_specs.is_empty() {
        None
    } else {
        Some(spec_ctx.extern_specs)
    };
    spec_ctx
        .user_specs
        .get(&def_id)
        .or_else(|| spec_ctx.trait_specs.get(&def_id))
        .cloned()
        .map(|spec| {
            crate::logic::identity_typed::instantiate_generic_markers_for_call(
                spec_ctx.tcx,
                body,
                func,
                def_id,
                spec,
            )
        })
        .or_else(|| {
            let path = spec_ctx.tcx.def_path_str(def_id);
            crate::provenance::lookup_spec_for_def(
                spec_ctx.tcx,
                def_id,
                admission,
                extern_opt,
                &path,
                crate::provenance::CallSite::of_operand(func, Some(body.source.def_id())),
            )
        })
        .or_else(|| {
            let trait_method_id = resolve_trait_method_def_id(spec_ctx.tcx, def_id)?;
            let trait_path = spec_ctx.tcx.def_path_str(trait_method_id);
            crate::provenance::lookup_spec_for_def(
                spec_ctx.tcx,
                trait_method_id,
                admission,
                extern_opt,
                &trait_path,
                crate::provenance::CallSite::of_operand(func, Some(body.source.def_id())),
            )
        })
}

/// Whether a clause instantiated at a loop-body call states only values the
/// loop VC names: no prophecy or entry-state term (the walk tracks neither
/// across a call) and no placeholder for an argument that did not translate.
fn is_statable_call_fact(fact: &PureExpr) -> bool {
    let mut statable = true;
    fact.for_each_recursive(|node| match node {
        PureExpr::Final(_) | PureExpr::Old(_) => statable = false,
        PureExpr::Var(name, _) if is_fallback_arg_placeholder(name) => statable = false,
        _ => {}
    });
    statable
}

/// True for `(^self)@` — `View(Final(Var("self")))` — the post-state view term
/// that an `&mut self` mutator's postcondition uses for its resulting state.
fn is_final_self_view(expr: &PureExpr) -> bool {
    let PureExpr::View(inner) = expr else {
        return false;
    };
    let PureExpr::Final(final_inner) = inner.as_ref() else {
        return false;
    };
    matches!(final_inner.as_ref(), PureExpr::Var(name, _) if name == "self")
}

/// True if `expr` still mentions a `^self` (final/prophecy) term anywhere — used
/// to reject an RHS we cannot express purely over the old state.
fn mentions_final_self(expr: &PureExpr) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| {
        if let PureExpr::Final(inner) = node {
            if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "self") {
                found = true;
            }
        }
    });
    found
}

fn index_logic(receiver: PureExpr, index: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "index_logic".to_string(),
        args: vec![index],
    }
}

fn set_call(receiver: PureExpr, index: PureExpr, value: PureExpr) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "set".to_string(),
        args: vec![index, value],
    }
}

fn collapse_loop_scalar_identity_views(expr: PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::View(inner) if is_loop_scalar_identity_domain(inner.as_ref()) => {
            inner.as_ref().clone()
        }
        other => other,
    })
}

fn is_loop_scalar_identity_domain(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => true,
        PureExpr::Var(_, Some(sort)) => matches!(
            sort,
            ExprSort::Int | ExprSort::Bool | ExprSort::Float(_) | ExprSort::Unit
        ),
        _ => false,
    }
}
