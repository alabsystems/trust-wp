// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure body inlining for simple closures (#2151 Phases 2-3).
//!
//! When the driver extracts a closure's MIR body as a `PureExpr`, this module
//! enables the encoder to replace `postcondition(env, args, result)` UF calls
//! with ground `result == body_expr` assertions. This eliminates quantifier
//! load from closure axioms — the primary cause of closure-related solver
//! timeouts (10/18 timeout failures per #1997).
//!
//! Phase 3 extends this to `postcondition_mut` with ensures: the body
//! substitution (return value) is conjoined with ensures (side effects on
//! mutable captures) to produce a complete ground assertion. This eliminates
//! the UF fallback that previously required the enrichment mechanism.
//!
//! ## Integration
//!
//! The driver populates `ClosureCaptureInfo::body_expr` during MIR extraction
//! for same-crate closures with ≤6 effective basic blocks. The verification
//! setup layer calls [`AYEncoder::register_closure_body`] to store the body.
//! When the pure encoding layer encounters a `postcondition(env, args, result)`
//! method call, [`AYEncoder::try_inline_closure_postcondition`] checks for an
//! available body and encodes it as a ground term.

mod substitution;

use std::{collections::HashSet, sync::Arc};

use ay_dpll::api::Term;
use substitution::{
    conjoin_with_ensures, extract_receiver_name, substitute_closure_body,
    substitute_closure_body_mut, substitute_closure_ensures, substitute_closure_requires,
    substitute_ensures_only, substitute_mutref_capture_currents,
};
use trust_wp_core::formula::PureExpr;

use super::AYEncoder;
use crate::{
    encoder::sort_context::{resolve_nameable_expr, resolve_view_var_name, DerivedKind},
    error::EncodingError,
    shared_types::ClosureCaptureInfo,
};

/// Stored body information for an inlineable closure.
#[derive(Debug, Clone)]
pub(crate) struct ClosureBodyInfo {
    /// Closure parameter/local name used at call sites, when known.
    pub(crate) param_name: Option<String>,
    /// The closure body as a `PureExpr` (return value expression), when extracted.
    pub(crate) body: Option<PureExpr>,
    /// Formal parameter names of the closure (not captures).
    pub(crate) param_names: Vec<String>,
    /// Capture field names, in order, for substitution.
    pub(crate) capture_names: Vec<String>,
    /// User-annotated or synthesized ensures expressions (#2151 Phase 3).
    ///
    /// When available, these are conjoined with the body substitution for
    /// `postcondition_once` and `postcondition_mut` inlining. The body only
    /// represents the return value; the ensures capture state changes to
    /// mutable captures (e.g., `x == old(x) + 1`).
    pub(crate) ensures_exprs: Option<Vec<PureExpr>>,
    /// User-annotated requires expressions (#2668).
    ///
    /// When available, enables `precondition` inlining: `precondition(env, args)`
    /// is replaced with the concrete requires expression, allowing the solver to
    /// evaluate precondition obligations at call sites of generic closure-accepting
    /// functions.
    pub(crate) requires_exprs: Option<Vec<PureExpr>>,
}

impl AYEncoder {
    /// Register a closure body for inline encoding.
    ///
    /// Called by the verification setup layer when `ClosureCaptureInfo` has a
    /// `body_expr` or `ensures_exprs`. After registration,
    /// `try_inline_closure_postcondition` can use the body (or ensures) to
    /// produce ground terms.
    pub(crate) fn register_closure_body(&mut self, info: &ClosureCaptureInfo) {
        // Need either a body, ensures, or requires expressions to be useful
        if info.body_expr().is_none()
            && info.ensures_exprs().is_none()
            && info.requires_exprs().is_none()
        {
            return;
        }
        let body = info.body_expr().cloned();
        let param_names = info.param_names().map_or_else(Vec::new, <[String]>::to_vec);
        let capture_names = info
            .captures()
            .iter()
            .map(|field| field.name().to_string())
            .collect();

        // Register param_name -> def_id mapping for multi-closure disambiguation.
        if let Some(param_name) = info.param_name() {
            self.closure_state
                .insert_param_mapping(param_name.to_string(), info.def_id().to_string());
        }

        self.closure_state.insert_body(
            info.def_id().to_string(),
            ClosureBodyInfo {
                param_name: info.param_name().map(str::to_string),
                body,
                param_names,
                capture_names,
                ensures_exprs: info.ensures_exprs().map(<[PureExpr]>::to_vec),
                requires_exprs: info.requires_exprs().map(<[PureExpr]>::to_vec),
            },
        );
    }

    /// Try to inline a closure postcondition call.
    ///
    /// If the closure has a registered body, substitutes capture references and
    /// formal parameters with the actual call arguments, then encodes the body
    /// as a ground term equivalent to `result == body_expr`.
    ///
    /// Supports three closure spec methods:
    /// - `postcondition(env, args..., result)` - Fn trait
    /// - `postcondition_once(env, args..., result)` - FnOnce trait (same arg layout)
    /// - `postcondition_mut(env, args..., final_state, result)` - FnMut trait
    ///   (extra `final_state` arg for post-call env)
    ///
    /// Returns `None` if the closure has no inlineable body (falls back to UF
    /// encoding).
    pub(crate) fn try_inline_closure_postcondition(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<Result<Term, EncodingError>> {
        // Inline for postcondition/postcondition_once/postcondition_mut and
        // precondition calls. Precondition inlining added in #2668.
        if !matches!(
            method,
            "postcondition" | "postcondition_once" | "postcondition_mut" | "precondition"
        ) {
            return None;
        }

        let body_info = self.find_body_for_receiver(receiver)?;

        // Precondition inlining (#2668): when a closure has registered requires
        // expressions, `precondition(env, args)` is replaced with the concrete
        // requires specification. This enables callers of generic functions like
        // `call_fnmut<F: FnMut()>` to prove precondition obligations.
        if method == "precondition" {
            let requires_exprs = body_info.requires_exprs.clone()?;
            let param_names = body_info.param_names.clone();
            let capture_names = body_info.capture_names.clone();
            let substituted =
                substitute_closure_requires(&requires_exprs, &capture_names, &param_names, args)?;
            // #closure-capture-carriers: a receiver field that is a minted
            // MutRef carrier makes the capture's call-entry value
            // definitionally `*carrier` — substitute it so the requires
            // obligation reads the carrier's current pointee instead of
            // colliding with the caller-scope binding of the same name
            // (which after a consuming call is the POST-state prophecy).
            let substituted =
                substitute_mutref_capture_currents(&substituted, &capture_names, receiver);
            return Some(self.encode_pure_impl(&substituted, prefix));
        }

        let body = body_info.body.clone();
        let param_names = body_info.param_names.clone();
        let capture_names = body_info.capture_names.clone();
        let ensures_exprs = body_info.ensures_exprs.clone();

        let substituted = if let Some(body) = body.as_ref() {
            let substituted = match method {
                // postcondition(env, args..., result) and postcondition_once(env, args..., result)
                // have the same argument layout: formal params map to args[0..N], result is last.
                "postcondition" | "postcondition_once" => {
                    substitute_closure_body(body, &capture_names, &param_names, args)
                }
                // postcondition_mut(env, args..., final_state, result): the final_state is
                // inserted before result. Strip it from the args passed to the body substitution
                // so param mapping stays correct, but also substitute Final(Var(capture)) -> the
                // final_state expression for captures that appear under Final wrappers.
                "postcondition_mut" => {
                    substitute_closure_body_mut(body, &capture_names, &param_names, args)
                }
                _ => unreachable!(),
            };

            // Phase 3/4 (#2151): For postcondition_once and postcondition_mut on
            // closures with ensures (synthesized from body effects or user-annotated),
            // conjoin the body substitution (return value) with the ensures (side
            // effects on mutable captures).
            //
            // Old() in ensures is handled by the encoder's old_ prefix mechanism.
            // Bare capture names resolve relative to the concrete receiver state so
            // sequential FnOnce/FnMut calls on the same closure thread capture state
            // through `c`, `^c`, `^^c`, etc.
            if matches!(method, "postcondition_once" | "postcondition_mut") {
                if let Some(ensures) = ensures_exprs.as_deref() {
                    let pre_state = receiver.clone();
                    let post_state = if method == "postcondition_mut" {
                        // `postcondition_mut(args_tuple, final_state, result)`: the
                        // closure final-state is the second-to-last argument. The
                        // leading element is the (possibly unit) closure args-tuple,
                        // so the final-state index is `args.len() - 2`, NOT
                        // `param_names.len()` — those coincide only when each formal
                        // param is passed as a separate arg, but contracts pass a
                        // single args-tuple. Using `param_names.len()` made a
                        // no-formal-param closure (e.g. `|| { x += 1; 5 }`) bind the
                        // post-captured state to the unit args-tuple `()`, aliasing
                        // every chained call's post-state to one canonical
                        // `tuple_get_0(())` term and falsely contradicting the
                        // existential chain for boxed receivers. (#closures/07)
                        args.len()
                            .checked_sub(2)
                            .and_then(|idx| args.get(idx))
                            .cloned()
                            .unwrap_or_else(|| {
                                PureExpr::Final(std::sync::Arc::new(receiver.clone()))
                            })
                    } else {
                        PureExpr::Final(std::sync::Arc::new(receiver.clone()))
                    };
                    let mut substituted_ensures = substitute_closure_ensures(
                        ensures,
                        &capture_names,
                        &pre_state,
                        &post_state,
                    );
                    if let Some(caller_ensures) = caller_state_closure_ensures(
                        receiver,
                        method,
                        args,
                        &param_names,
                        body_info.param_name.as_deref(),
                        ensures,
                        &capture_names,
                    ) {
                        substituted_ensures.extend(caller_ensures);
                    }
                    conjoin_with_ensures(&substituted, &substituted_ensures)
                } else {
                    substituted
                }
            } else {
                substituted
            }
        } else {
            // Ensures-only inlining is sound only when the contract constrains
            // the return value. Otherwise, fall back to the UF path so the
            // closure result remains opaque rather than fabricating a body.
            substitute_ensures_only(param_names.as_slice(), args, ensures_exprs.as_deref()?)?
        };

        Some(self.encode_pure_impl(&substituted, prefix))
    }

    /// Find the body for a closure receiver expression.
    ///
    /// Matches the receiver to a registered closure body by checking:
    /// 1. Direct param_name -> def_id lookup
    /// 2. Single-body shortcut (unambiguous when only one closure is registered)
    /// 3. Unique-ensures shortcut: when multiple closures are registered but only
    ///    one has ensures expressions (e.g., "real" closure + proof_assert lambda),
    ///    return the one with ensures. This enables inlining for Skolem constants
    ///    from `postcondition_mut` existentials in the presence of proof_assert
    ///    lambdas. (#2668)
    fn find_body_for_receiver(&self, receiver: &PureExpr) -> Option<ClosureBodyInfo> {
        if self.closure_state.is_empty() {
            return None;
        }

        // Try direct param_name -> def_id lookup using the receiver names the
        // driver actually emits. Preserve derived suffixes like `_view` and
        // `_current` before falling back to the bare base name. Some receiver
        // shapes nest `View` under `Deref`/`Final`, so also try a normalized
        // variant with `View` wrappers stripped first.
        let normalized_receiver = strip_view_wrappers_for_lookup(receiver);
        for lookup_receiver in [receiver, &normalized_receiver] {
            let receiver_names = [
                resolve_view_var_name(lookup_receiver, None),
                resolve_final_view_var_name(lookup_receiver),
                resolve_nameable_expr(lookup_receiver, None),
                extract_receiver_name_for_lookup(lookup_receiver).map(str::to_string),
            ];
            for name in receiver_names.into_iter().flatten() {
                for candidate in receiver_lookup_candidates(&name) {
                    if let Some(def_id) = self.closure_state.def_id_for_param(&candidate) {
                        if let Some(body_info) = self.closure_state.get_body(def_id) {
                            return Some(body_info.clone());
                        }
                    }
                }
            }
        }

        // Single-body shortcut: when only one closure is registered, it is
        // unambiguous and we can return it directly.
        if let Some(body) = self.closure_state.single_body() {
            return Some(body.clone());
        }

        // Unique-ensures shortcut (#2668): when multiple closures are registered
        // but only one has ensures (e.g., the main closure has ensures while a
        // proof_assert lambda does not), use the one with ensures. This is
        // critical for Skolem constants from postcondition_mut existentials:
        // the Skolem receiver (e.g., "sk_exists_st1_N") cannot be matched by
        // param_name, and single_body fails because proof_assert lambdas also
        // register bodies. The ensures-bearing closure is the only one that
        // postcondition_mut can meaningfully refer to.
        self.closure_state.unique_body_with_ensures().cloned()
    }
}

fn extract_receiver_name_for_lookup(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::View(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner) => extract_receiver_name_for_lookup(inner),
        _ => extract_receiver_name(expr),
    }
}

fn resolve_final_view_var_name(expr: &PureExpr) -> Option<String> {
    let PureExpr::Final(inner) = expr else {
        return None;
    };
    let PureExpr::View(view_inner) = inner.as_ref() else {
        return None;
    };
    let name = resolve_nameable_expr(view_inner, None)?;
    Some(DerivedKind::format_chain(
        &name,
        &[DerivedKind::FinalPrefix, DerivedKind::View],
    ))
}

fn strip_view_wrappers_for_lookup(expr: &PureExpr) -> PureExpr {
    match expr {
        PureExpr::View(inner) => strip_view_wrappers_for_lookup(inner),
        PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(strip_view_wrappers_for_lookup(inner))),
        PureExpr::Final(inner) => PureExpr::Final(Arc::new(strip_view_wrappers_for_lookup(inner))),
        PureExpr::Old(inner) => PureExpr::Old(Arc::new(strip_view_wrappers_for_lookup(inner))),
        _ => expr.clone(),
    }
}

fn receiver_lookup_candidates(name: &str) -> Vec<String> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    collect_receiver_lookup_candidates(name, &mut seen, &mut out);
    out
}

fn caller_state_closure_ensures(
    receiver: &PureExpr,
    method: &str,
    args: &[PureExpr],
    param_names: &[String],
    param_name: Option<&str>,
    ensures: &[PureExpr],
    capture_names: &[String],
) -> Option<Vec<PureExpr>> {
    let param_name = param_name?;
    let pre_depth = receiver_final_depth(receiver, param_name)?;
    let post_depth = match method {
        "postcondition" => pre_depth,
        "postcondition_once" => pre_depth + 1,
        "postcondition_mut" => args
            .get(param_names.len())
            .and_then(|post_state| receiver_final_depth(post_state, param_name))
            .unwrap_or(pre_depth + 1),
        _ => return None,
    };

    let mut caller_ensures =
        substitute_closure_ensures_for_caller_state(ensures, capture_names, pre_depth, post_depth);

    // Some verification paths use the RustHorn old-prefix convention for the
    // first closure call: `x` is the post-call value and `old(x)` is `old_x`.
    // Keep that ground fact alongside the final-depth fact so simple
    // call-site obligations do not need quantified closure axioms.
    if pre_depth == 0 && method != "postcondition" {
        caller_ensures.extend(ensures.iter().cloned());
    }

    Some(caller_ensures)
}

fn receiver_final_depth(expr: &PureExpr, param_name: &str) -> Option<usize> {
    match expr {
        PureExpr::Var(name, _) if name == param_name => Some(0),
        PureExpr::Deref(inner) | PureExpr::View(inner) => receiver_final_depth(inner, param_name),
        PureExpr::Final(inner) => receiver_final_depth(inner, param_name).map(|depth| depth + 1),
        _ => None,
    }
}

fn final_wrapped_capture(
    name: &str,
    sort: &Option<trust_wp_core::formula::ExprSort>,
    depth: usize,
) -> PureExpr {
    let mut expr = PureExpr::Var(name.to_string(), sort.clone());
    for _ in 0..depth {
        expr = PureExpr::Final(Arc::new(expr));
    }
    expr
}

fn substitute_closure_ensures_for_caller_state(
    ensures: &[PureExpr],
    capture_names: &[String],
    pre_depth: usize,
    post_depth: usize,
) -> Vec<PureExpr> {
    ensures
        .iter()
        .map(|ensure| {
            substitute_closure_ensure_for_caller_state(
                ensure,
                capture_names,
                pre_depth,
                post_depth,
                false,
            )
        })
        .collect()
}

fn substitute_closure_ensure_for_caller_state(
    expr: &PureExpr,
    capture_names: &[String],
    pre_depth: usize,
    post_depth: usize,
    inside_old: bool,
) -> PureExpr {
    match expr {
        PureExpr::Var(name, sort) if capture_names.iter().any(|capture| capture == name) => {
            let depth = if inside_old { pre_depth } else { post_depth };
            final_wrapped_capture(name, sort, depth)
        }
        PureExpr::Old(inner) => {
            let inner_has_capture = expr_mentions_capture(inner, capture_names);
            let transformed = substitute_closure_ensure_for_caller_state(
                inner,
                capture_names,
                pre_depth,
                post_depth,
                true,
            );
            if inner_has_capture {
                transformed
            } else if &transformed == inner.as_ref() {
                PureExpr::Old(Arc::new(transformed))
            } else {
                transformed
            }
        }
        PureExpr::Final(inner) => {
            PureExpr::Final(Arc::new(substitute_closure_ensure_for_caller_state(
                inner,
                capture_names,
                pre_depth,
                post_depth,
                inside_old,
            )))
        }
        PureExpr::Deref(inner) => {
            PureExpr::Deref(Arc::new(substitute_closure_ensure_for_caller_state(
                inner,
                capture_names,
                pre_depth,
                post_depth,
                inside_old,
            )))
        }
        PureExpr::View(inner) => {
            PureExpr::View(Arc::new(substitute_closure_ensure_for_caller_state(
                inner,
                capture_names,
                pre_depth,
                post_depth,
                inside_old,
            )))
        }
        PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
            Arc::new(substitute_closure_ensure_for_caller_state(
                left,
                capture_names,
                pre_depth,
                post_depth,
                inside_old,
            )),
            *op,
            Arc::new(substitute_closure_ensure_for_caller_state(
                right,
                capture_names,
                pre_depth,
                post_depth,
                inside_old,
            )),
        ),
        PureExpr::UnOp(op, inner) => PureExpr::UnOp(
            *op,
            Arc::new(substitute_closure_ensure_for_caller_state(
                inner,
                capture_names,
                pre_depth,
                post_depth,
                inside_old,
            )),
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            Arc::new(substitute_closure_ensure_for_caller_state(
                cond,
                capture_names,
                pre_depth,
                post_depth,
                inside_old,
            )),
            Arc::new(substitute_closure_ensure_for_caller_state(
                then_expr,
                capture_names,
                pre_depth,
                post_depth,
                inside_old,
            )),
            Arc::new(substitute_closure_ensure_for_caller_state(
                else_expr,
                capture_names,
                pre_depth,
                post_depth,
                inside_old,
            )),
        ),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => PureExpr::MethodCall {
            receiver: Arc::new(substitute_closure_ensure_for_caller_state(
                receiver,
                capture_names,
                pre_depth,
                post_depth,
                inside_old,
            )),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| {
                    substitute_closure_ensure_for_caller_state(
                        arg,
                        capture_names,
                        pre_depth,
                        post_depth,
                        inside_old,
                    )
                })
                .collect(),
        },
        PureExpr::LogicFnCall { name, args } => PureExpr::LogicFnCall {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| {
                    substitute_closure_ensure_for_caller_state(
                        arg,
                        capture_names,
                        pre_depth,
                        post_depth,
                        inside_old,
                    )
                })
                .collect(),
        },
        other => other.clone(),
    }
}

fn expr_mentions_capture(expr: &PureExpr, capture_names: &[String]) -> bool {
    match expr {
        PureExpr::Var(name, _) => capture_names.iter().any(|capture| capture == name),
        PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::Deref(inner)
        | PureExpr::View(inner)
        | PureExpr::UnOp(_, inner) => expr_mentions_capture(inner, capture_names),
        PureExpr::BinOp(left, _, right) => {
            expr_mentions_capture(left, capture_names)
                || expr_mentions_capture(right, capture_names)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_mentions_capture(cond, capture_names)
                || expr_mentions_capture(then_expr, capture_names)
                || expr_mentions_capture(else_expr, capture_names)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_mentions_capture(receiver, capture_names)
                || args
                    .iter()
                    .any(|arg| expr_mentions_capture(arg, capture_names))
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter()
            .any(|arg| expr_mentions_capture(arg, capture_names)),
        _ => false,
    }
}

fn collect_receiver_lookup_candidates(
    name: &str,
    seen: &mut HashSet<String>,
    out: &mut Vec<String>,
) {
    if !seen.insert(name.to_string()) {
        return;
    }
    out.push(name.to_string());

    if let Some(stripped) = DerivedKind::peel_final_view_prefix(name) {
        collect_receiver_lookup_candidates(&stripped, seen, out);
    }

    if let Some((DerivedKind::View, base)) = DerivedKind::strip_from(name) {
        collect_receiver_lookup_candidates(base, seen, out);
    }

    let mut suffix_base = name;
    while let Some((kind, stripped)) = DerivedKind::strip_from(suffix_base) {
        match kind {
            DerivedKind::Current | DerivedKind::Final | DerivedKind::Prime => {
                suffix_base = stripped;
                collect_receiver_lookup_candidates(suffix_base, seen, out);
            }
            _ => break,
        }
    }

    for stripped in DerivedKind::peel_old_prefixes(name) {
        collect_receiver_lookup_candidates(stripped, seen, out);
    }
}

#[cfg(test)]
mod tests;
