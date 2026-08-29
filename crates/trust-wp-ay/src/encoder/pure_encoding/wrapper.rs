// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use ay_dpll::api::{Sort, Term};
use trust_wp_core::formula::{ExprSort, MatchArm, PureExpr};

use super::super::{
    final_collapse_guard::expr_sort_is_post_state_container,
    sort_context::{
        apply_name_prefix, effective_expr_annotation, extract_base_var_name, resolve_nameable_expr,
        DerivedKind,
    },
    AYEncoder,
};
use crate::error::EncodingError;

/// Discriminates between `Deref` (current-value) and `Final` (prophecy-value)
/// wrapper kinds. Used by `encode_deref_or_final` to unify the near-identical
/// encoding logic for both wrappers. (#1397)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum WrapperKind {
    Deref,
    Final,
}

impl WrapperKind {
    fn label(self) -> &'static str {
        match self {
            Self::Deref => "deref",
            Self::Final => "final",
        }
    }
}

/// Peel nested wrappers of the given `kind` from `expr`, counting depth.
///
/// `expr` is the inside of an outer wrapper, so base depth starts at 1.
fn peel_wrapper_depth(mut expr: &PureExpr, kind: WrapperKind) -> (usize, &PureExpr) {
    let mut depth = 1;
    while let (WrapperKind::Deref, PureExpr::Deref(inner))
    | (WrapperKind::Final, PureExpr::Final(inner)) = (kind, expr)
    {
        depth += 1;
        expr = inner.as_ref();
    }
    (depth, expr)
}

/// Wrap `expr` in `depth` layers of the given wrapper `kind`.
fn wrap_with_kind(mut expr: PureExpr, kind: WrapperKind, depth: usize) -> PureExpr {
    for _ in 0..depth {
        expr = match kind {
            WrapperKind::Deref => PureExpr::Deref(Arc::new(expr)),
            WrapperKind::Final => PureExpr::Final(Arc::new(expr)),
        };
    }
    expr
}

/// Wrap an already-shared subtree without cloning its inner expression.
fn wrap_arc_with_kind(expr: &Arc<PureExpr>, kind: WrapperKind, depth: usize) -> PureExpr {
    if depth == 0 {
        return expr.as_ref().clone();
    }

    let mut wrapped = match kind {
        WrapperKind::Deref => PureExpr::Deref(Arc::clone(expr)),
        WrapperKind::Final => PureExpr::Final(Arc::clone(expr)),
    };
    for _ in 1..depth {
        wrapped = match kind {
            WrapperKind::Deref => PureExpr::Deref(Arc::new(wrapped)),
            WrapperKind::Final => PureExpr::Final(Arc::new(wrapped)),
        };
    }
    wrapped
}

/// Returns the `WrapperKind` opposite to the given one.
fn opposite_kind(kind: WrapperKind) -> WrapperKind {
    match kind {
        WrapperKind::Deref => WrapperKind::Final,
        WrapperKind::Final => WrapperKind::Deref,
    }
}

impl AYEncoder {
    /// Unified encoding for `Deref` and `Final` wrapper expressions. (#1397)
    ///
    /// Both wrappers follow the same three-phase structure:
    /// 1. Quantifier-bound variable collapse (bound vars have no temporal state)
    /// 2. Nameable expression resolution (via `resolve_nameable_expr`)
    /// 3. Structural rewriting (push wrapper into LogicFnCall/MethodCall/View args)
    ///
    /// The `kind` parameter selects which peeling/wrapping functions to use.
    /// `outer_expr` is the full `Deref(inner)` or `Final(inner)` expression
    /// (needed for `resolve_nameable_expr` which inspects the outer wrapper).
    pub(super) fn encode_deref_or_final(
        &mut self,
        outer_expr: &PureExpr,
        inner: &PureExpr,
        kind: WrapperKind,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Phase 1: Quantifier-bound variable collapse.
        // In a quantifier scope, bound variables are pure logical values without
        // temporal state. Deref(Var(v)) → v, Final(Var(v)) → v. Without this,
        // the wrapper would create a free variable disconnected from the
        // quantifier binding, making the formula vacuously satisfiable. (#717)
        //
        // #prophecy-slots (Fix B M1): a MutRef-SORTED MATCH BINDER is a REAL
        // prophecy carrier — `*v` and `^v` are the DEFINITIONAL accessor
        // applications (`mut_ref_current` / `mut_ref_final`,
        // `bind_whole_mut_ref`), never the carrier itself. Returning the raw
        // carrier for both directions (the retired `!is_mut_ref_sorted`
        // exemption) would reinstate `*v == ^v` at the carrier level with no
        // counter tracking it — the adjudicated take_first_mut inversion
        // relocated one sort up. This arm therefore lands in the SAME commit
        // as the lowering that first makes match binders MutRef-sorted
        // (Option<&mut T> payload fields at the record sort), and covers
        // BOTH wrapper directions: the Deref side had no guard at all.
        //
        // Scoped to MATCH BINDERS, deliberately: quantifier-bound LOGIC-FN
        // FORMALS keep the legacy collapse for both directions — the driver
        // splits current/final upstream and passes the value at the right
        // time AS the formal, so `^x`/`*x` on a formal denote the formal
        // itself; projecting a formal instead mints an unconstrained
        // accessor application and manufactures counterexamples (measured:
        // partially_opaque::g's `^x.invariant()` flipped from
        // proof-trusted-UNSAT to a spurious counterexample when this arm was
        // unscoped). No lowering in this commit makes a formal MutRef-sorted
        // where it was not before, so the formal lane's exposure is
        // unchanged; the M2 negative corpus must add a carrier-formal probe
        // if that class ever becomes constructible.
        //
        // Final-collapse audit Fix A guard (below the projection arm): the
        // Final collapse is exact only when the bound value is a PURE value.
        // For MATCH-ARM binders whose bound term is NOT a carrier (an
        // Int-collapsed destructor payload with no prophecy slot), when the
        // binder's sort embeds a mutable reference — or cannot be proven not
        // to (no annotation) — collapsing `^v` to the same term as `*v`/`v`
        // asserts the inversion `^v == *v` (the adjudicated take_first_mut
        // false accept). Refuse fail-closed instead.
        if let PureExpr::Var(name, ann) = inner {
            if self.is_quantifier_bound(name.as_str()) {
                let lookup = apply_name_prefix(name, prefix).into_owned();
                if let Some(term) = self.var_term(&lookup) {
                    if self.is_match_binder_var(name.as_str()) {
                        if self.is_mut_ref_sorted(term) {
                            if let Some(projected) =
                                self.mut_ref_component_projection(term, kind == WrapperKind::Final)?
                            {
                                return Ok(projected);
                            }
                            // Unreachable in practice (is_mut_ref_sorted
                            // implies the projection exists); fail closed
                            // rather than ever handing the raw carrier back
                            // for a wrapper.
                            return Err(self.refuse_final_collapse(name, ann.as_ref()));
                        }
                        if kind == WrapperKind::Final
                            && self.final_collapse_requires_prophecy(ann.as_ref())
                        {
                            return Err(self.refuse_final_collapse(name, ann.as_ref()));
                        }
                    }
                    return Ok(term);
                }
            }
        }

        // Phase 1b: Non-temporal variable collapse for plain value wrappers.
        //
        // `Deref` on a plain value is a no-op: specs like `*self` in consuming
        // method contracts (e.g., `Result::unwrap(self)`) produce
        // `Deref(Var("call_N", Datatype(..)))`, but the variable has no
        // temporal (current/final) state — it's a plain value. Without this
        // collapse, `Deref` creates a disconnected derived variable
        // (e.g., `call_N_current`) that has no constraint linking it to the
        // original `call_N`, causing verification failures. (#2675)
        //
        // Shared refs are also pure immutable reads, so `Deref(Var(_, Ref(T)))`
        // collapses to the referenced value rather than creating `*_current`.
        //
        // `Final` is temporal only for mutable/ghost state carriers. Plain
        // datatype and shared-reference values are call results or immutable
        // values, so `Final(Var(_, Datatype|Ref))` must collapse to the base
        // variable. Int/Bool/Seq/FMap carriers still keep a distinct final
        // variable because ghost locals and proof_assert snapshots use those
        // sorts for real post-state. (#2675, #2700)
        // Final-collapse audit Fix A guard (Phase 1b Final arm): collapsing
        // `Final(Var(_, Datatype|Ref))` to the base variable is exact only
        // when the sort embeds no mutable reference. `Option<&mut T>`,
        // `RefMut`-likes and ADT-embedded `&mut` payloads have no prophecy
        // slot — the collapse would invert `^x` premises onto the pre-state.
        // Refuse fail-closed (unknown/undeclared datatypes included).
        //
        // Value-model container carve-out (vacfix, cc/seq::f): the sentence
        // above — "Seq/FMap carriers still keep a distinct final variable
        // because ghost locals ... use those sorts for real post-state" — was
        // keyed on the `ExprSort` *variant* only, so it protected
        // `ExprSort::Seq`/`ExprSort::FMap` annotations but NOT the very same
        // carrier arriving as `ExprSort::Datatype(creusot_std::Seq)` (which is
        // how the driver annotates a ghost `Seq` local: the `&mut` is peeled
        // to the referent, so no `MutRef` annotation survives). Those fell
        // into this arm, `sort_embeds_mut_ref` returns false for every
        // value-model canonical name by construction, and the collapse then
        // asserted `^s == s` — flatly contradicting the mutation premise
        // `^s == s.push_front(v)` and manufacturing a contradictory base
        // (`cc/seq::f`, "vacuous proof: base assertions are UNSAT ..." with a
        // 4-assertion core `len(s) = 0 /\ len(s) = len(s)+1`).
        //
        // Declining the collapse falls through to the Phase-2 naming path,
        // which mints the distinct `s_final` carrier at the same sort — the
        // faithful encoding, and strictly WEAKER than the collapse (it drops
        // an equality, never adds one).
        if let PureExpr::Var(name, Some(ann)) = inner {
            match kind {
                WrapperKind::Deref if !matches!(ann, ExprSort::MutRef(_)) => {
                    return self.encode_pure_impl(inner, prefix);
                }
                WrapperKind::Final
                    if matches!(ann, ExprSort::Datatype(_) | ExprSort::Ref(_))
                        && !expr_sort_is_post_state_container(ann) =>
                {
                    if self.sort_embeds_mut_ref(ann) {
                        return Err(self.refuse_final_collapse(name, Some(ann)));
                    }
                    return self.encode_pure_impl(inner, prefix);
                }
                _ => {}
            }
        }

        // Phase 1c: Nested mut-ref scalar projection (FIX B,
        // #nested-mutref final/current projection).
        //
        // For nested references like `x: &mut &mut i32`, a doubly-wrapped
        // projection such as `^*x`/`^^x` (= `Final(Final(x))`) or `**x`
        // (= `Deref(Deref(x))`) denotes a *scalar* leaf value, but the
        // intermediate sub-expression (`Final(x)` / `Deref(x)`) encodes to a
        // `MutRef`-sorted carrier (the inner reference). The legacy Phase-2
        // naming path declares a fresh carrier (e.g. `x_final_final`) whose
        // sort is inherited from that inner reference (MutRef) rather than the
        // scalar leaf — so an equality like `^*x == 1i32` later sort-coerces
        // the `1` into a fresh unconstrained constant, making the goal
        // trivially satisfiable. (inferred_invariants::nested_borrows)
        //
        // When the peeled annotation is a non-reference scalar but the inner
        // sub-expression is `MutRef`-sorted, apply the *definitional* accessor
        // UF (`mut_ref_final` for `Final`, `mut_ref_current` for `Deref`) to
        // the inner carrier. SOUND: `mut_ref_final(r)` IS `^r` and
        // `mut_ref_current(r)` IS `*r` by construction (see
        // `bind_whole_mut_ref`), so this is exact — strictly more precise than
        // a fresh sort-mismatched variable, never an added assumption.
        // Scoped to the outer `Final` projection only: the `Deref`
        // (current-value) naming path (`x_current_current` = `**x`) is relied
        // on by loop-invariant machinery and must keep its legacy names. The
        // failing case is purely the final-state leaf `^*x`/`^^x`.
        let scalar_leaf = matches!(
            effective_expr_annotation(outer_expr),
            Some(ann) if !matches!(ann, ExprSort::MutRef(_) | ExprSort::Ref(_))
        );
        if kind == WrapperKind::Final && scalar_leaf && matches!(inner, PureExpr::Final(_)) {
            let inner_term = self.encode_pure_impl(inner, prefix)?;
            if self.is_mut_ref_sorted(inner_term) {
                if let Some(projected) =
                    self.mut_ref_component_projection(inner_term, /* want_final */ true)?
                {
                    return Ok(projected);
                }
            }
        }

        // Phase 1d: Box-collapsed reborrow leaf `*^x` / `**x`.
        //
        // For `x: &mut Box<T>` (`bug/final_borrows::box_reborrow_indirect`), the
        // driver collapses the `Box` indirection so the reborrow carrier is a
        // single-layer `Var("x", MutRef(T))` whose referent `T` is already the
        // scalar leaf. The postcondition `result == **x` lowers to
        // `Deref(Final(x))` (= `*^x`) or `Deref(Deref(x))` (= `**x`), retaining
        // an *extra* `Deref` from the collapsed `Box` layer. Because the carrier
        // has only one reference layer, the inner `Final(x)`/`Deref(x)` already
        // encodes to the scalar leaf (`x_final` / `x_current` at sort `T`), so the
        // outer `Deref` over that scalar value is the identity — the Box-layer
        // artifact. The general naming path (Phase 2 below) would instead mint a
        // fresh disconnected `x_final_current`/`x_current_current`, so the
        // postcondition cannot see `result`.
        //
        // Collapse the outer `Deref` to the inner projection whenever the inner is
        // a single `Deref`/`Final` of a `MutRef`-carrier whose referent is a
        // *non-reference scalar*. SOUND: `*v` of a scalar value `v` is `v`, and
        // the inner `Final`/`Deref` already names the exact final/current leaf.
        // Guarded on a scalar (non-reference) referent so genuine nested
        // references `x: &mut &mut T` — where the inner `Deref`/`Final` is itself
        // `MutRef`-sorted and the outer `Deref` is a real reference peel — keep
        // the legacy multi-layer naming.
        if kind == WrapperKind::Deref {
            let carrier = match inner {
                PureExpr::Final(c) | PureExpr::Deref(c) => Some(c.as_ref()),
                _ => None,
            };
            if let Some(PureExpr::Var(_, Some(ExprSort::MutRef(referent)))) = carrier {
                if !matches!(referent.as_ref(), ExprSort::MutRef(_) | ExprSort::Ref(_)) {
                    let inner_term = self.encode_pure_impl(inner, prefix)?;
                    // The inner term is the scalar leaf; dereferencing it again is
                    // the identity collapse of the Box layer. Only collapse when
                    // the inner is genuinely the scalar leaf (not a `MutRef`
                    // carrier), so we never silently drop a real reference peel.
                    if !self.is_mut_ref_sorted(inner_term) {
                        return Ok(inner_term);
                    }
                }
            }
        }

        // Phase 2: Nameable expression resolution.
        // Maps wrapper(expr) to a resolved variable name via the naming helper.
        // Supports nested chains like Deref(Deref(Var(v))) → v_current_current.
        if let Some(var_name) = resolve_nameable_expr(outer_expr, prefix) {
            // Annotation-aware sort fallback: use the effective peeled annotation
            // from the outer wrapper expression. For Deref(Var("x", MutRef(MutRef(Int)))),
            // effective_expr_annotation returns MutRef(Int) (not the raw MutRef(MutRef(Int))
            // from extract_inner_var_annotation). This ensures wrapper-derived names like
            // x_current get the correct sort for the peeled reference depth. (#2585, #2084, #1805)
            let effective_ann = effective_expr_annotation(outer_expr);
            let fallback = match effective_ann {
                Some(ann) => self.sort_from_expr_sort(ann.clone()),
                None => self.infer_expr_sort_with_context(inner, prefix),
            };
            let mut sort =
                self.resolve_decl_sort(&var_name, extract_base_var_name(inner), fallback);
            // Propagate Datatype sort from base variable (#967): when the base
            // variable was declared as a Datatype (e.g., OptionInt from a match
            // postcondition), the derived variable should inherit that sort.
            if sort == Sort::Int {
                if let Some(base) = extract_base_var_name(inner) {
                    let base_key = apply_name_prefix(base, prefix).into_owned();
                    if let Some(base_sort) = self.var_sort(&base_key) {
                        if matches!(base_sort, Sort::Datatype(_)) {
                            sort = base_sort.clone();
                        }
                    }
                }
            }
            return self.get_or_declare_var(&var_name, sort);
        }

        // Phase 1e: `*` / `^` over a PROJECTION of a prophecy carrier.
        // (#prophecy-slots, Fix B M2.)
        //
        // The driver's substitution pipeline replaces a match binder over an
        // `Option<&mut T>` / `Option<(&mut T, ..)>` call result with the
        // PROJECTION CHAIN that reaches it — e.g. `first` becomes
        // `tuple_get_0(option_some_value(call_2))`. `^first` therefore arrives
        // here as `Final(LogicFnCall{..})`, and Phase 3 below would DISTRIBUTE
        // the wrapper into the call's arguments (Creusot's projection rule
        // `^(s[i]) == (^s)[i]`). That rule is exactly wrong for a carrier
        // projection: it lands `^` on the `Option` CARRIER ITSELF, which has
        // no prophecy — the blueprint's `GET_MUT_GENERIC` defect, structurally.
        //
        // When the projection's own term IS the mutref record carrier, `*` and
        // `^` are its DEFINITIONAL accessors (`bind_whole_mut_ref`), so the
        // projection is exact — never an added assumption.
        //
        // Gated syntactically on an operand that carries a prophecy-carrier
        // annotation, so no expression outside this new class is pre-encoded
        // and the passing corpus keeps byte-identical symbol minting.
        if matches!(
            inner,
            PureExpr::LogicFnCall { .. } | PureExpr::MethodCall { .. }
        ) && Self::expr_mentions_prophecy_carrier_annotation(inner)
        {
            let inner_term = self.encode_pure_impl(inner, prefix)?;
            if self.is_mut_ref_sorted(inner_term) {
                if let Some(projected) =
                    self.mut_ref_component_projection(inner_term, kind == WrapperKind::Final)?
                {
                    return Ok(projected);
                }
            }
        }

        // Phase 3: Structural rewriting — peel nested same-kind wrappers,
        // then push the wrapper into the base expression's args/receiver.
        let (depth, base) = peel_wrapper_depth(inner, kind);
        self.encode_wrapper_rewrite(outer_expr, base, kind, depth, prefix)
    }

    /// #prophecy-slots (Fix B M2): does this expression mention a variable
    /// annotated with one of the instantiation-aware prophecy-carrier sort
    /// names (`Option<&mut ..>` family, or the carrier tuple)?
    ///
    /// Deliberately name-based and narrow: those names exist only because the
    /// driver minted them for a `&mut`-embedding instantiation, so a hit means
    /// "a projection of this expression may BE a carrier". Everything else
    /// keeps the legacy lane untouched.
    fn expr_mentions_prophecy_carrier_annotation(expr: &PureExpr) -> bool {
        use crate::encoder::sort_context::sort_mapping::{
            parse_mutref_carrier_tuple, parse_mutref_instantiated_option,
        };
        let mut found = false;
        expr.for_each_recursive(|node| {
            if found {
                return;
            }
            if let PureExpr::Var(_, Some(ExprSort::Datatype(id))) = node {
                let name = trust_wp_core::formula::resolve_sort_name(*id);
                if parse_mutref_instantiated_option(&name).is_some()
                    || parse_mutref_carrier_tuple(&name).is_some()
                {
                    found = true;
                }
            }
        });
        found
    }

    /// Phase 3 of deref/final encoding: structural rewriting of the peeled base.
    ///
    /// Pushes the wrapper `kind` (at `depth`) into LogicFnCall/MethodCall/View
    /// args, handles cross-wrapper cases, literals, and Ite distribution.
    fn encode_wrapper_rewrite(
        &mut self,
        outer_expr: &PureExpr,
        base: &PureExpr,
        kind: WrapperKind,
        depth: usize,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        match base {
            PureExpr::LogicFnCall { name, args } => {
                let rewritten = PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: args
                        .iter()
                        .map(|arg| wrap_with_kind(arg.clone(), kind, depth))
                        .collect(),
                };
                self.encode_pure_impl(&rewritten, prefix)
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                // `Final` does NOT distribute into GROUND-CONSTANT arguments
                // (#124, tract19 follow-up). A `Final(MethodCall(..))` in
                // wrapper position is typically the driver's substituted image
                // of `^<place>` where the place is a projection chain
                // (`^((*x)[2])` from a reborrow like `&mut (*x)[2].0`): the
                // index/key was evaluated when the place was formed and has no
                // temporal state — Creusot's projection rule is
                // `^(s[i]) = (^s)[i]`. Wrapping a constant argument minted
                // `^<literal>` (`(^x)[^2]`), which the Fix A constant-carrier
                // guard refuses — turning e.g. `lang/logic_vcgen::f`'s
                // instantiated `(^x)@ == 2` premise into a whole-function
                // encoding error.
                //
                // VARIABLE arguments keep the legacy full distribution: the
                // closure lanes deliberately produce matched pairs like
                // `postcondition_mut(^f, ^result)` on both sides
                // (eager_instantiation_audit), and a `Final(Var)` still has a
                // faithful per-variable final carrier. `Deref` likewise keeps
                // the legacy full distribution — `*<literal>` is faithful, so
                // no refusal route exists there.
                let wrap_final_arg = |arg: &PureExpr| -> PureExpr {
                    fn is_ground_constant_tree(expr: &PureExpr) -> bool {
                        match expr {
                            PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => true,
                            PureExpr::UnOp(_, inner) => is_ground_constant_tree(inner),
                            PureExpr::BinOp(lhs, _, rhs) => {
                                is_ground_constant_tree(lhs) && is_ground_constant_tree(rhs)
                            }
                            _ => false,
                        }
                    }
                    if is_ground_constant_tree(arg) {
                        arg.clone()
                    } else {
                        wrap_with_kind(arg.clone(), WrapperKind::Final, depth)
                    }
                };
                let rewritten = PureExpr::MethodCall {
                    receiver: Arc::new(wrap_arc_with_kind(receiver, kind, depth)),
                    method: method.clone(),
                    args: match kind {
                        WrapperKind::Final => args.iter().map(wrap_final_arg).collect(),
                        WrapperKind::Deref => args
                            .iter()
                            .map(|arg| wrap_with_kind(arg.clone(), kind, depth))
                            .collect(),
                    },
                };
                self.encode_pure_impl(&rewritten, prefix)
            }
            PureExpr::View(inner_view) => {
                let rewritten =
                    PureExpr::View(Arc::new(wrap_arc_with_kind(inner_view, kind, depth)));
                self.encode_pure_impl(&rewritten, prefix)
            }
            // Cross-wrapper: Deref(Final(e)) or Final(Deref(e)). (#1191)
            PureExpr::Deref(cross_inner) if kind == WrapperKind::Final => {
                let opp = opposite_kind(kind);
                self.encode_cross_wrapper(outer_expr, cross_inner, kind, opp, depth, prefix)
            }
            PureExpr::Final(cross_inner) if kind == WrapperKind::Deref => {
                let opp = opposite_kind(kind);
                self.encode_cross_wrapper(outer_expr, cross_inner, kind, opp, depth, prefix)
            }
            // Distribute wrapper into BinOp operands. (#2700)
            PureExpr::BinOp(lhs, op, rhs) => {
                let rewritten = PureExpr::BinOp(
                    Arc::new(wrap_arc_with_kind(lhs, kind, depth)),
                    *op,
                    Arc::new(wrap_arc_with_kind(rhs, kind, depth)),
                );
                self.encode_pure_impl(&rewritten, prefix)
            }
            // Distribute wrapper into UnOp operand. (#2700)
            PureExpr::UnOp(op, operand) => {
                let rewritten =
                    PureExpr::UnOp(*op, Arc::new(wrap_arc_with_kind(operand, kind, depth)));
                self.encode_pure_impl(&rewritten, prefix)
            }
            // Distribute wrapper into Old inner expression. (#2700)
            PureExpr::Old(inner_old) => {
                let rewritten = PureExpr::Old(Arc::new(wrap_arc_with_kind(inner_old, kind, depth)));
                self.encode_pure_impl(&rewritten, prefix)
            }
            // `Deref` is a no-op on literals. (#1075)
            //
            // Final-collapse audit Fix A, constant-carrier arm (tract19):
            // `Final` is NOT. A literal reaching a wrapper position is the
            // driver's substituted *value* of the borrowed place at the
            // CURRENT state; `^p` names the value the borrow holds when it
            // EXPIRES. `*3 == 3` is faithful; `^3 == 3` is the same inversion
            // `^p == *p` that the sort guard above refuses for
            // mut-ref-embedding carriers — reached here through a constant
            // carrier rather than through a sort, so `sort_embeds_mut_ref`
            // never sees it (a literal's sort is `Int`/`Bool`/`Float`, all
            // "pure value" ⇒ collapse permitted).
            //
            // This was a LIVE FALSE ACCEPT, not a latent one:
            //
            //     #[ensures((^r)@ >= 0)] fn touch(r: &mut i32) { *r = 99; }
            //     #[ensures(result@ == 3)]
            //     pub fn evil() -> i32 {
            //         let mut x = 3i32; let r = &mut x; touch(r); return x
            //     }
            //
            // The driver advances the base local through the borrow chain as
            // `Final(<its value expression>)`
            // (`mir_analysis/extract/substitution/visitor.rs`, #1581), so `x`
            // lowers to `Final(Int(3))` and the return expression IS
            // `Final(Int(3))`. This arm folded it to `3`, the postcondition
            // `result@ == 3` became `3 == 3`, its negation encoded to literal
            // `false`, and `evil` verified with `decisions=0` — although it
            // returns 99. The premise stays satisfiable (`3 >= 0`), so the
            // vacuity guard never fires either.
            //
            // Refuse fail-closed. A prophecy over a carrier with no identity
            // is not representable in this encoding, and an unrepresentable
            // prophecy must demote, never prove. The faithful repair is
            // driver-side: mint a per-borrow prophecy carrier for
            // locally-rooted borrows instead of one shared
            // `Final(base_expr)`.
            //
            // ONE carve-out: BINDER-ERASING SUBSTITUTION scopes (the
            // existential witness probe and recursive logic-fn ground
            // unfolding) substitute a ground value for a logically BOUND
            // variable at the PureExpr level before re-encoding, so a body
            // mentioning `^x` reaches here as `Final(Int(c))` with the binder
            // already erased. There the wrapper is the substituted image of
            // Phase 1's "bound variables and logic-fn formals are pure logical
            // values without temporal state" rule, which already collapses
            // `Final(Var(v))`; refusing changes no soundness property and only
            // breaks those lanes. See
            // `QuantifierState::binder_substitution_depth` — note it is a scope
            // marker, NOT ambient quantifier depth, so a user postcondition
            // wrapped in `forall<i> ...` stays refused.
            PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => {
                if kind == WrapperKind::Final && !self.quantifier_state.in_binder_substitution() {
                    return Err(self.refuse_prophecy_over_constant(base));
                }
                self.encode_pure_impl(base, prefix)
            }
            // Distribute wrapper into Ite branches.
            PureExpr::Ite(cond, then_br, else_br) => {
                let rewritten = PureExpr::Ite(
                    cond.clone(),
                    Arc::new(wrap_arc_with_kind(then_br, kind, depth)),
                    Arc::new(wrap_arc_with_kind(else_br, kind, depth)),
                );
                self.encode_pure_impl(&rewritten, prefix)
            }
            // Distribute wrapper into Match arms, mirroring the Ite case:
            // `*(match s { P => b, .. }) → match s { P => *b, .. }`. The
            // scrutinee is the matched value (not a temporal read), so it is
            // left untouched; only each arm body carries the wrapper.
            PureExpr::Match { scrutinee, arms } => {
                let rewritten = PureExpr::Match {
                    scrutinee: Arc::clone(scrutinee),
                    arms: arms
                        .iter()
                        .map(|arm| MatchArm {
                            pattern: arm.pattern.clone(),
                            body: wrap_with_kind(arm.body.clone(), kind, depth),
                        })
                        .collect(),
                };
                self.encode_pure_impl(&rewritten, prefix)
            }
            _ => Err(EncodingError::unsupported(format!(
                "complex {} expression: {outer_expr:?}",
                kind.label(),
            ))),
        }
    }

    /// Handles the cross-wrapper case: one kind wrapping the opposite kind.
    ///
    /// E.g., Deref(Final(f(x))) → f(Deref(Final(x))) or
    /// Final(Deref(f(x))) → f(Final(Deref(x))). Wraps each arg with both
    /// the outer kind (at `depth`) and inner opposite kind (at depth 1). (#1191)
    fn encode_cross_wrapper(
        &mut self,
        outer_expr: &PureExpr,
        cross_inner: &PureExpr,
        outer_kind: WrapperKind,
        inner_kind: WrapperKind,
        outer_depth: usize,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let wrap_both_owned = |arg: PureExpr| -> PureExpr {
            wrap_with_kind(wrap_with_kind(arg, inner_kind, 1), outer_kind, outer_depth)
        };
        let wrap_both_arc = |arg: &Arc<PureExpr>| -> PureExpr {
            wrap_with_kind(
                wrap_arc_with_kind(arg, inner_kind, 1),
                outer_kind,
                outer_depth,
            )
        };
        match cross_inner {
            PureExpr::LogicFnCall { name, args } => {
                let rewritten = PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: args.iter().map(|a| wrap_both_owned(a.clone())).collect(),
                };
                self.encode_pure_impl(&rewritten, prefix)
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let rewritten = PureExpr::MethodCall {
                    receiver: Arc::new(wrap_both_arc(receiver)),
                    method: method.clone(),
                    args: args.iter().map(|a| wrap_both_owned(a.clone())).collect(),
                };
                self.encode_pure_impl(&rewritten, prefix)
            }
            PureExpr::View(v) => {
                let rewritten = PureExpr::View(Arc::new(wrap_both_arc(v)));
                self.encode_pure_impl(&rewritten, prefix)
            }
            // Distribute both wrappers into BinOp operands. (#2700)
            PureExpr::BinOp(lhs, op, rhs) => {
                let rewritten = PureExpr::BinOp(
                    Arc::new(wrap_both_arc(lhs)),
                    *op,
                    Arc::new(wrap_both_arc(rhs)),
                );
                self.encode_pure_impl(&rewritten, prefix)
            }
            // Distribute both wrappers into UnOp operand. (#2700)
            PureExpr::UnOp(op, operand) => {
                let rewritten = PureExpr::UnOp(*op, Arc::new(wrap_both_arc(operand)));
                self.encode_pure_impl(&rewritten, prefix)
            }
            // Distribute both wrappers into Old inner expression. (#2700)
            PureExpr::Old(inner_old) => {
                let rewritten = PureExpr::Old(Arc::new(wrap_both_arc(inner_old)));
                self.encode_pure_impl(&rewritten, prefix)
            }
            // Both wrappers are no-ops on constants.
            PureExpr::Int(_) | PureExpr::Bool(_) | PureExpr::Float(_) => {
                self.encode_pure_impl(cross_inner, prefix)
            }
            // Distribute both wrappers into Ite branches.
            PureExpr::Ite(cond, then_br, else_br) => {
                let rewritten = PureExpr::Ite(
                    cond.clone(),
                    Arc::new(wrap_both_arc(then_br)),
                    Arc::new(wrap_both_arc(else_br)),
                );
                self.encode_pure_impl(&rewritten, prefix)
            }
            // Distribute both wrappers into Match arms, mirroring the Ite case.
            // The scrutinee stays untouched; each arm body carries both wrappers.
            PureExpr::Match { scrutinee, arms } => {
                let rewritten = PureExpr::Match {
                    scrutinee: Arc::clone(scrutinee),
                    arms: arms
                        .iter()
                        .map(|arm| MatchArm {
                            pattern: arm.pattern.clone(),
                            body: wrap_both_owned(arm.body.clone()),
                        })
                        .collect(),
                };
                self.encode_pure_impl(&rewritten, prefix)
            }
            _ => Err(EncodingError::unsupported(format!(
                "complex {}({}) expression: {outer_expr:?}",
                outer_kind.label(),
                inner_kind.label(),
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use ntest::timeout;

    use super::*;

    #[test]
    #[timeout(5000)]
    fn wrap_arc_with_kind_reuses_inner_arc() {
        let shared = Arc::new(PureExpr::Var("value".to_string(), None));

        let wrapped = wrap_arc_with_kind(&shared, WrapperKind::Final, 2);

        match wrapped {
            PureExpr::Final(outer) => match outer.as_ref() {
                PureExpr::Final(inner) => {
                    assert!(
                        Arc::ptr_eq(inner, &shared),
                        "wrapping an Arc subtree should preserve the original inner Arc"
                    );
                }
                other => panic!("expected nested final wrapper, got: {other:?}"),
            },
            other => panic!("expected final wrapper, got: {other:?}"),
        }
    }
}
