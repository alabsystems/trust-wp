// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-site modeling: postcondition-based result constraint and Seq ghost mutations.

use std::{collections::HashMap, sync::Arc};

use rustc_middle::{
    mir::{Local, Operand},
    ty::TyKind,
};
use rustc_span::Spanned;
use trust_wp_core::formula::{ExprSort, PureExpr};
use trust_wp_driver::{lookup_spec_with_extern, StdSpec};

use super::{
    super::{
        super::{
            call_resolve::{
                arg_names_for_def_id, extract_call_def_id, resolve_trait_method_def_id,
            },
            effects::CallEffects,
            spec_apply::{apply_postconditions_for_loop_body_with_effects, TranslatedArg},
            translate::{translate_operand, ty_to_expr_sort, ty_to_expr_sort_enriched},
        },
        condition::base_var_name,
        CallSpecContext,
    },
    BodyExtractionCtx, BodyExtractionState,
};

impl<'a, 'tcx> BodyExtractionCtx<'a, 'tcx> {
    /// Apply direct receiver updates for Seq ghost mutators.
    ///
    /// Recognizes:
    /// - `Seq::push_front_ghost(&mut self, x)` as `self' = self.push_front(x)`
    /// - `Seq::push_back_ghost(&mut self, x)` as `self' = self.push_back(x)`
    ///
    /// This is a targeted loop-extraction bridge for ghost for-loop invariants.
    pub(super) fn apply_seq_ghost_mutation(
        &self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        state: &mut BodyExtractionState,
    ) {
        let Some(spec_ctx) = self.call_spec_ctx else {
            return;
        };
        let Some(def_id) = extract_call_def_id(func) else {
            return;
        };
        let path = spec_ctx.tcx.def_path_str(def_id);
        let is_front = path.ends_with("::push_front_ghost");
        let is_back = path.ends_with("::push_back_ghost");
        if !is_front && !is_back {
            return;
        }
        if args.len() != 2 {
            return;
        }

        let Some(receiver_expr) = translate_operand(&args[0].node, &state.working_exprs) else {
            return;
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
            return;
        };
        let Some(receiver_name) = base_var_name(&receiver_expr) else {
            return;
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
    pub(super) fn apply_mut_self_post_state(
        &self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        state: &mut BodyExtractionState,
    ) {
        let Some(spec_ctx) = self.call_spec_ctx else {
            return;
        };
        let Some(def_id) = extract_call_def_id(func) else {
            return;
        };
        if args.is_empty() {
            return;
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
            return;
        }

        // Resolve the receiver's loop-visible base name. `self@` in the spec maps
        // to `View(Deref(receiver))` so the deref effect is expressed over the
        // OLD pointee view, exactly like `apply_indexed_write_effect`.
        let Some(receiver_expr) = translate_operand(&args[0].node, &state.working_exprs) else {
            return;
        };
        let Some(receiver_name) = base_var_name(&receiver_expr) else {
            return;
        };
        let receiver_name = receiver_name.to_string();

        let spec = match lookup_callee_spec(spec_ctx, def_id) {
            Some(spec) if !spec.ensures.is_empty() => spec,
            _ => return,
        };

        // Translate call arguments and resolve parameter names, mirroring
        // `try_model_call_result` so user/std specs share substitution behavior.
        let translated_args: Vec<TranslatedArg> = args
            .iter()
            .enumerate()
            .map(|(idx, arg)| {
                if let Some(expr) = translate_operand(&arg.node, &state.working_exprs) {
                    TranslatedArg::new(expr)
                } else {
                    let sort = ty_to_expr_sort_enriched(
                        spec_ctx.tcx,
                        arg.node.ty(&self.body.local_decls, spec_ctx.tcx),
                    );
                    TranslatedArg::fallback(PureExpr::Var(format!("arg{idx}"), sort))
                }
            })
            .collect();
        let hir_param_names = arg_names_for_def_id(spec_ctx.tcx, def_id);
        let param_names = hir_param_names.or_else(|| spec.param_names.clone());

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

        if let Some(new_view) =
            self.mut_self_new_view(&spec.ensures, &old_view, &substitutions, &receiver_name)
        {
            // Keep working_exprs in sync for shadowing locals (defensive; the
            // receiver itself is the &mut reference, not the deref target).
            state.deref_effects.insert(receiver_name.clone(), new_view);
        }
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
    /// Returns `None` (havoc fallback) when no clause matches a closed form.
    fn mut_self_new_view(
        &self,
        ensures: &[String],
        old_view: &PureExpr,
        substitutions: &HashMap<String, PureExpr>,
        _receiver_name: &str,
    ) -> Option<PureExpr> {
        for clause in ensures {
            let Ok(parsed) = trust_wp_core::contract_parser::parse_contract(clause) else {
                continue;
            };
            // Equational shape: `(^self)@ == <seqexpr>`.
            if let PureExpr::BinOp(lhs, trust_wp_core::formula::BinOp::Eq, rhs) = &parsed {
                if is_final_self_view(lhs) {
                    let new_view = rhs.as_ref().substitute(substitutions);
                    if !mentions_final_self(&new_view) {
                        return Some(new_view);
                    }
                }
                if is_final_self_view(rhs) {
                    let new_view = lhs.as_ref().substitute(substitutions);
                    if !mentions_final_self(&new_view) {
                        return Some(new_view);
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
                    return Some(set_ij);
                }
            }
        }
        None
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
        let translated_args: Vec<TranslatedArg> = args
            .iter()
            .enumerate()
            .map(|(idx, arg)| {
                if let Some(expr) = translate_operand(&arg.node, working_exprs) {
                    TranslatedArg::new(expr)
                } else {
                    let sort = ty_to_expr_sort_enriched(
                        spec_ctx.tcx,
                        arg.node.ty(&self.body.local_decls, spec_ctx.tcx),
                    );
                    TranslatedArg::fallback(PureExpr::Var(format!("arg{idx}"), sort))
                }
            })
            .collect();

        // Look up spec: user_specs → trait_specs → extern_specs → trait method fallback.
        // Phase C (#963): uses spec_ctx.extern_specs instead of EXTERN_SPECS thread-local.
        let spec = lookup_callee_spec(spec_ctx, def_id)?;

        if spec.ensures.is_empty() {
            return None;
        }

        let hir_param_names = arg_names_for_def_id(spec_ctx.tcx, def_id);
        let param_names = hir_param_names.or_else(|| spec.param_names.clone());

        // Create a result variable for postcondition substitution.
        let dest_sort =
            ty_to_expr_sort_enriched(spec_ctx.tcx, self.body.local_decls[dest_local].ty);
        let result_var = PureExpr::Var(format!("call_{}", dest_local.as_u32()), dest_sort);

        // Apply postconditions for loop body extraction. This variant also matches
        // `result@ == <expr>` patterns (e.g., Vec::len: `result@ == self@.len()`)
        // where the view is transparent for primitive return types. (#1463)
        // Effects (assumptions/obligations) are collected but not consumed — loop
        // body extraction only needs the return expression. (#963)
        let mut call_effects = CallEffects::new();
        let result_expr = apply_postconditions_for_loop_body_with_effects(
            &spec.ensures,
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
        let path = spec_ctx.tcx.def_path_str(def_id);
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
fn lookup_callee_spec(
    spec_ctx: CallSpecContext<'_, '_>,
    def_id: rustc_hir::def_id::DefId,
) -> Option<StdSpec> {
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
        .or_else(|| {
            let path = spec_ctx.tcx.def_path_str(def_id);
            lookup_spec_with_extern(extern_opt, &path)
        })
        .or_else(|| {
            let trait_method_id = resolve_trait_method_def_id(spec_ctx.tcx, def_id)?;
            let trait_path = spec_ctx.tcx.def_path_str(trait_method_id);
            lookup_spec_with_extern(extern_opt, &trait_path)
        })
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
            ExprSort::Int | ExprSort::Bool | ExprSort::Float | ExprSort::Unit
        ),
        _ => false,
    }
}
