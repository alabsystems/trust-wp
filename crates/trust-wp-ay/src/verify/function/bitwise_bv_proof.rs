// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pure QF_BV proof path for `#[bitwise_proof]` popcount-style obligations.
//!
//! The general encoder models Rust integers as the unbounded SMT `Int` sort and
//! lowers bitwise operators through an `int2bv`/`bv2int` BRIDGE. For the
//! popcount obligation `result@ == count8_log(n)` (where the function body is a
//! SWAR bit-twiddle and `count8_log` is a per-bit ITE sum) the combined VC mixes
//! `Int` arithmetic with per-operator `int2bv`/`bv2int` round-trips. On the
//! current `ay`, that mixed LIA+BV query churns in the combined theory and times
//! out (the bitblaster is never reached).
//!
//! This module recognises exactly that obligation shape and discharges it as a
//! self-contained, NATIVE QF_BV query on a fresh solver: the function's integer
//! variables are declared as `BitVec(W)` (W = the type width recovered from the
//! injected range preconditions), every operator is a native BV operator
//! (`bvand`/`bvlshr`/`bvadd`/`bvsub`/`bvule`/`bveq`/…), and the whole VC routes
//! straight to ay's bitblaster (sound + complete on QF_BV).
//!
//! ## Soundness
//!
//! The obligation has the shape `result_selector <cmp> spec`. Substituting
//! `result := return_expr` makes the result-selector side the *Rust function
//! body* (`return_expr`). BOTH sides are interpreted over the driver's exact
//! mathematical-`Int` model: a plain `-`/`+`/`*` is unbounded integer
//! arithmetic (overflow is a separate obligation), never a wrap at 2^W. The
//! width W is recovered from RANGE preconditions, not from the Rust type, so it
//! can be narrower than the type: an `i32` guarded by `x >= 0` recovers W = 31.
//! A `BitVec(W)` operator therefore does NOT equal its source operator in
//! general — `x - 1` at `x = 0` is `-1` in the model and `2^31 - 1` as a
//! 31-bit `bvsub`, which made `ensures(result >= 0)` a BV tautology and minted
//! a fully checked certificate for a false contract.
//!
//! The encoder is therefore EXACTNESS-GUARDED: every variable ranges over the
//! window `[0, 2^W)` its premises force; literals must lie in the window; and
//! every node whose source value could leave the window (`+`, `-`, `*`, `<<`,
//! unary `-`, unless the conservative interval analysis certifies the node in
//! the window) contributes a BV-decidable WRAP condition — the exact test that
//! the W-bit result differs from the integer result given exact operands.
//! `&`, `|`, `^`, `>>`, `ite`, and the unsigned comparisons are exact on exact
//! in-window operands; `~` (whose integer value `-a-1` is negative) is refused.
//! The query is `H ∧ (¬goal ∨ wrap_1 ∨ … ∨ wrap_k)`:
//!   * UNSAT ⇒ for every input in the window, no node wraps (so every BV value
//!     equals its integer value) and the goal holds ⇒ Verified.
//!   * SAT ⇒ reported Failed only when NO wrap condition was emitted, no
//!     hypothesis was dropped, and the func side provably fits the window
//!     (the model is then a genuine counterexample); otherwise BAIL.
//! Hypotheses whose encoding would itself need a wrap guard are DROPPED
//! (weakening the premise side only strengthens what UNSAT proves).
//! Anything else (non-uniform/unknown width, signed operands, an unsupported
//! node, an unbounded spec, a solver timeout/Unknown) makes this path BAIL
//! (`None`), falling back to the general encoder. It can never accept a wrong
//! spec — a corrupted `result@ == count8_log(n) + 1` stays in-range, is encoded
//! exactly, and is reported SAT/Failed.

use std::collections::HashMap;

use ay_dpll::api::{Logic, Solver, Term};
use trust_wp_core::{
    formula::{BinOp, PureExpr, UnOp},
    logic::{LogicFnDef, LogicMode},
};

use super::super::{solver_tail::ObligationSliceContext, VerificationResult};

/// Maximum BV width this path will encode at. Width recovery constant-folds
/// `unsigned_max_expr` bounds exactly (including the symbolic `2^64 - 1` tree
/// emitted for `u64`), so this cap is the operative guard: any recovered width
/// above it bails to the general path, bounding the bitblaster size.
const MAX_BV_WIDTH: u32 = 64;

/// Wall-clock budget for the isolated QF_BV solve. The popcount queries close in
/// well under a second; the cap only guards against a pathological blow-up, in
/// which case we BAIL to the general path.
const BV_SOLVE_TIMEOUT_SECS: u64 = 20;

/// Attempt to discharge `ensure` as a native QF_BV popcount-style obligation.
///
/// Returns `Some(Verified)` / `Some(Failed)` on a definitive native-BV result,
/// or `None` to fall through to the general encoder (the obligation shape did
/// not match, the width/soundness side-conditions did not hold, or the solver
/// was inconclusive).
pub(super) fn try_prove_bitwise_bv_obligation(
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> Option<VerificationResult> {
    let return_expr = ctx.return_expr?;
    let logic_fns = ctx.logic_fns?;

    // The obligation must be a single comparison `a <cmp> b`.
    let PureExpr::BinOp(lhs, op, rhs) = ensure else {
        return None;
    };
    let cmp = *op;
    if !is_comparison(cmp) {
        return None;
    }

    // Exactly one side is the result selector (`result`, possibly under
    // `@`/`*`). That side is the Rust function value; the other is the spec.
    let (spec_side, result_is_lhs) = if is_result_selector(lhs) {
        (rhs.as_ref(), true)
    } else if is_result_selector(rhs) {
        (lhs.as_ref(), false)
    } else {
        return None;
    };

    // SCOPE GUARD: the spec side must reference a visible logic-fn call OR be a
    // plain integer literal (a range obligation like `result@ <= 16`). Range
    // obligations over SWAR bitwise chains are exactly what the general path
    // times out on (mixed-domain conflict churn on popcount's count16/32/64,
    // 22.6s envelope expiry) while this native QF_BV path proves each in
    // ~100ms. Every acceptance still requires UNSAT of the negation under the
    // exact-width encoding + the interval side-conditions below, and every
    // unencodable shape still falls through to the general path (fail-closed),
    // so the relaxation cannot admit a false accept. (#route-100 r3)
    if !contains_visible_logic_fn_call(spec_side, logic_fns)
        && !matches!(spec_side, PureExpr::Int(_))
    {
        return None;
    }

    // Bind `result := return_expr` and inline every visible (non-opaque,
    // non-recursive, requires-free) logic fn on both sides.
    let mut subst = HashMap::new();
    subst.insert("result".to_string(), return_expr.clone());
    let bound = ensure.substitute(&subst);
    let bound = inline_visible_logic_fns(&bound, logic_fns);

    let PureExpr::BinOp(bound_lhs, bound_op, bound_rhs) = &bound else {
        return None;
    };
    if *bound_op != cmp {
        return None;
    }
    let (func_side, spec_side_bound) = if result_is_lhs {
        (bound_lhs.as_ref(), bound_rhs.as_ref())
    } else {
        (bound_rhs.as_ref(), bound_lhs.as_ref())
    };

    // The return expression is wrapped in `LetAssume`/`LetObligation` scopes
    // (call postconditions / shift-in-range obligations). Strip them down to the
    // value `body`; `LetAssume` assumptions become sound hypotheses (they are
    // proven at the call site), `LetObligation` obligations are verified
    // independently so dropping them only strengthens our goal (sound for a
    // Verified result).
    let mut hypotheses: Vec<PureExpr> = Vec::new();
    let func_expr = unwrap_lets(func_side, &mut hypotheses);
    let spec_expr = unwrap_lets(spec_side_bound, &mut hypotheses);

    // Recover an unsigned bit width for every free variable from the injected
    // range preconditions. All free vars must share one width W.
    let widths = recover_unsigned_widths(&bound, ctx.requires)?;
    let width = uniform_width(&widths)?;
    if width == 0 || width > MAX_BV_WIDTH {
        return None;
    }
    let modulus: i128 = 1i128 << width;

    // The spec side must provably stay in [0, 2^W). (Wrapping does NOT "only
    // add behaviors": it REPLACES a value by its residue mod 2^W, so an
    // unguarded wrapping encoding can turn a false goal into a BV tautology —
    // `x - 1 >= 0` at W = 31 — with a genuine UNSAT certificate. Exactness of
    // the func side is enforced per node by the wrap guards `encode_bv`
    // collects; see the module docs.)
    let (lo, hi) = interval(&spec_expr, &widths)?;
    if lo < 0 || hi >= modulus {
        return None;
    }
    // Whether the function side provably stays in [0, 2^W) — required before a
    // SAT verdict may be reported as a COUNTEREXAMPLE. The old claim — "the
    // function side is exact at BitVec(W) by Rust wrapping semantics" — only
    // holds when W is the variable's own Rust width and the source operation
    // actually wraps. Neither is guaranteed: the width is recovered from RANGE
    // preconditions, so an `i32` guarded by `x >= 0` recovers W = 31, and the
    // driver's model for a plain `+` is exact mathematical Int with a separate
    // overflow obligation — it never wraps at 2^W. Encoding such a `+` as
    // `bvadd` manufactured a spurious counterexample at `x = 2^31 - 1` for
    // `ensures(result > 0)` over `return x + 1` (StrongerPost::refine, the
    // trait-refinement e2e red) once the #route-100 r3 relaxation admitted
    // integer-literal spec sides. A SAT model may be exactly such a wrapped
    // spurious behavior, so without provable containment a SAT verdict falls
    // through to the general path instead of minting a Failed. Verified
    // acceptance is guarded per node instead (the wrap conditions below), which
    // keeps the masked SWAR chains this lane exists for — whose `Sub` steps
    // the conservative interval cannot bound below zero, but whose no-borrow
    // guard the bitblaster discharges — proving natively.
    let func_side_provably_in_range = interval(&func_expr, &widths)
        .is_some_and(|(func_lo, func_hi)| func_lo >= 0 && func_hi < modulus);

    // Build the native QF_BV query on a fresh solver.
    let mut solver = Solver::new(Logic::QfBv);
    solver.set_timeout(Some(std::time::Duration::from_secs(BV_SOLVE_TIMEOUT_SECS)));
    solver.set_produce_proofs(true);
    if solver
        .try_set_option(":check-proofs-strict", "true")
        .is_err()
    {
        return None;
    }

    let mut var_terms: HashMap<String, Term> = HashMap::new();
    for (name, &w) in &widths {
        if w != width {
            return None;
        }
        let term = solver.bv_var(name, width);
        var_terms.insert(name.clone(), term);
    }

    let enc = BvEnc {
        width,
        modulus,
        widths: &widths,
        var_terms: &var_terms,
    };
    let mut goal_wraps: Vec<Term> = Vec::new();
    let func_term = encode_bv(&mut solver, &func_expr, &enc, &mut goal_wraps)?;
    let spec_term = encode_bv(&mut solver, &spec_expr, &enc, &mut goal_wraps)?;
    // The comparison keeps the ensures' operand order. `result` may sit on
    // either side, and `<`/`<=`/`>`/`>=` are not symmetric: `spec <= result`
    // encoded as `func <= spec` checks the opposite inequality, so a false
    // `five() <= result@` over `x & 0` read as the true `0 <= 5`.
    let goal = if result_is_lhs {
        encode_cmp(&mut solver, cmp, func_term, spec_term)
    } else {
        encode_cmp(&mut solver, cmp, spec_term, func_term)
    };

    // Assert  H1 & ... & Hk & (not(goal) | wrap_1 | ... | wrap_m): UNSAT means
    // that under the hypotheses no goal node leaves the window (every BV value
    // equals its integer value) AND the goal holds.
    let not_goal = solver.not(goal);
    let mut refutation = not_goal;
    for wrap in &goal_wraps {
        refutation = solver.or(refutation, *wrap);
    }
    let mut assertion = refutation;
    let mut hypothesis_dropped = false;
    for hyp in &hypotheses {
        let mut hyp_wraps: Vec<Term> = Vec::new();
        let hyp_term = encode_bool(&mut solver, hyp, &enc, &mut hyp_wraps)?;
        if !hyp_wraps.is_empty() {
            // Its BV value may differ from its integer value: drop it. A weaker
            // premise side only strengthens what UNSAT proves, but taints SAT.
            hypothesis_dropped = true;
            continue;
        }
        assertion = solver.and(assertion, hyp_term);
    }
    let encoding_exact = goal_wraps.is_empty() && !hypothesis_dropped;
    solver.assert_term(assertion);

    let verdict = solver.check_sat_with_details();
    if verdict.result.is_unsat() {
        let Some(summary) = crate::verify::extract_proof_summary(&solver) else {
            crate::verify::authority_trace(|| {
                "bitwise BV UNSAT: no proof summary extracted".to_string()
            });
            return None;
        };
        if !summary.is_fully_verified() {
            crate::verify::authority_trace(|| {
                crate::verify::authority_result_tag(&VerificationResult::Verified(Some(
                    summary.clone(),
                )))
            });
            return None;
        }
        let replay = solver
            .export_native_replay_artifact(
                ay_dpll::api::NativeReplayMetadata::default(),
                Some(&verdict),
            )
            .to_pretty_json();
        if !crate::verify::solver_tail::record_isolated_strict_unsat_diagnostics(
            &verdict,
            Some(replay),
        ) {
            return None;
        }
        Some(VerificationResult::verified_with_proof(summary))
    } else if verdict.result.is_sat()
        && verdict.accept_for_consumer().is_ok()
        && func_side_provably_in_range
        && encoding_exact
    {
        // The isolated BV solver validated this SAT model: carry it (with the
        // solve envelope) as the refutation witness so the `Failed` is backed
        // by a validated counterexample rather than withheld.
        let model = solver.model().map(ay_dpll::VerifiedModel::into_inner);
        let replay = solver
            .export_native_replay_artifact(
                ay_dpll::api::NativeReplayMetadata::default(),
                Some(&verdict),
            )
            .to_pretty_json();
        crate::verify::solver_tail::record_isolated_refutation_witness(
            &verdict,
            model,
            Some(replay),
        )
        .map(VerificationResult::Failed)
    } else {
        // Unknown / timeout — or a SAT model that may only witness a wrapped
        // behavior the exact math-Int model does not have: fall back to the
        // general path.
        None
    }
}

fn is_comparison(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    )
}

/// Recognise the result selector: a bare `result` variable under any number of
/// `@` (`View`) / `*` (`Deref`) / `old` / `^` (`Final`) wrappers.
fn is_result_selector(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(name, _) => name == "result",
        PureExpr::View(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner) => is_result_selector(inner),
        _ => false,
    }
}

fn logic_fn_body_visible(logic_fn: &LogicFnDef) -> bool {
    !logic_fn.is_opaque() && !logic_fn.is_recursive() && logic_fn.mode() != LogicMode::Default
}

fn contains_visible_logic_fn_call(expr: &PureExpr, logic_fns: &[LogicFnDef]) -> bool {
    expr.any_recursive(|node| {
        let PureExpr::LogicFnCall { name, args } = node else {
            return false;
        };
        logic_fns.iter().any(|f| {
            f.name() == name
                && f.params().len() == args.len()
                && logic_fn_body_visible(f)
                && f.requires().is_empty()
        })
    })
}

/// Inline every visible, non-recursive, requires-free logic-fn call by
/// substituting parameters with the (recursively-inlined) call arguments.
pub(super) fn inline_visible_logic_fns(expr: &PureExpr, logic_fns: &[LogicFnDef]) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::LogicFnCall { name, args } => {
            let matching = logic_fns.iter().find(|f| {
                f.name() == name
                    && f.params().len() == args.len()
                    && logic_fn_body_visible(f)
                    && f.requires().is_empty()
            });
            match matching {
                Some(f) => {
                    let subst: HashMap<String, PureExpr> = f
                        .params()
                        .iter()
                        .cloned()
                        .zip(args.iter().cloned())
                        .collect();
                    // Body may itself reference other visible logic fns; the
                    // bottom-up rewrite already inlined the args, and a second
                    // pass handles any calls inside the substituted body.
                    let inlined_body = f.body().substitute(&subst);
                    inline_visible_logic_fns(&inlined_body, logic_fns)
                }
                None => PureExpr::LogicFnCall { name, args },
            }
        }
        other => other,
    })
}

/// Strip top-level `LetAssume`/`LetObligation` scopes down to the value `body`,
/// collecting each `LetAssume` assumption as a sound hypothesis. `LetObligation`
/// obligations are verified independently, so they are dropped here (which only
/// strengthens the resulting goal — sound for a Verified result).
fn unwrap_lets(expr: &PureExpr, hypotheses: &mut Vec<PureExpr>) -> PureExpr {
    match expr {
        PureExpr::LetAssume { assumption, body } => {
            hypotheses.push(assumption.as_ref().clone());
            unwrap_lets(body, hypotheses)
        }
        PureExpr::LetObligation { body, .. } => unwrap_lets(body, hypotheses),
        other => other.clone(),
    }
}

/// Strip selector wrappers (`@`/`*`/`old`/`^`) to find a bare variable name.
fn selector_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::View(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner) => selector_var_name(inner),
        _ => None,
    }
}

/// Exactly constant-fold a literal integer expression: `Int` literals combined
/// with `+`/`-`/`*` (checked, overflow ⇒ `None`) and unary negation. This is
/// precisely the vocabulary of `unsigned_max_expr`, whose `> 63`-bit bounds are
/// emitted as the symbolic repeated-squaring tree `2^W - 1` (e.g. `u64`'s
/// `(2*2)*(2*2)*… - 1`) rather than a plain `Int` literal. Returns `None` for
/// any non-constant node, so nothing is ever approximated.
fn const_int_value(expr: &PureExpr) -> Option<i128> {
    match expr {
        PureExpr::Int(c) => Some(i128::from(*c)),
        PureExpr::UnOp(UnOp::Neg, inner) => const_int_value(inner)?.checked_neg(),
        PureExpr::BinOp(l, op, r) => {
            let l = const_int_value(l)?;
            let r = const_int_value(r)?;
            match op {
                BinOp::Add => l.checked_add(r),
                BinOp::Sub => l.checked_sub(r),
                BinOp::Mul => l.checked_mul(r),
                _ => None,
            }
        }
        _ => None,
    }
}

/// If `value` is `2^W - 1` for some `W >= 1`, return `W`. (Widths above
/// `MAX_BV_WIDTH` are rejected by the caller's cap check.)
pub(super) fn width_from_unsigned_max(value: i128) -> Option<u32> {
    if value <= 0 {
        return None;
    }
    let plus_one = u128::try_from(value).ok()?.checked_add(1)?;
    if plus_one.is_power_of_two() {
        Some(plus_one.trailing_zeros())
    } else {
        None
    }
}

/// Recover an unsigned bit width for every free variable of `expr` from the
/// injected range preconditions (`v@ >= 0` and `v@ <= 2^W - 1`).
///
/// Returns `None` if any free variable lacks both an unsigned lower bound and a
/// power-of-two upper bound (i.e. its width or signedness is not recoverable).
fn recover_unsigned_widths(expr: &PureExpr, requires: &[PureExpr]) -> Option<HashMap<String, u32>> {
    let mut free_vars: Vec<String> = Vec::new();
    expr.for_each_free_var(|name, _sort| {
        if !free_vars.iter().any(|n| n == name) {
            free_vars.push(name.to_string());
        }
    });

    let mut widths = HashMap::new();
    for var in free_vars {
        let mut width: Option<u32> = None;
        let mut has_nonneg_lower = false;
        for require in requires {
            let PureExpr::BinOp(lhs, op, rhs) = require else {
                continue;
            };
            // `v@ <= 2^W - 1` — the bound is a plain `Int` literal for
            // widths <= 63 and the symbolic `pow2_expr(W) - 1` constant tree
            // for wider types (u64); both fold exactly via `const_int_value`.
            let width_bound =
                if matches!(op, BinOp::Le) && selector_var_name(lhs) == Some(var.as_str()) {
                    const_int_value(rhs).and_then(width_from_unsigned_max)
                } else {
                    None
                };
            if let Some(width_bound) = width_bound {
                width = Some(width_bound);
            }
            // `v@ >= 0` (unsigned non-negativity)
            if matches!(op, BinOp::Ge)
                && selector_var_name(lhs) == Some(var.as_str())
                && matches!(rhs.as_ref(), PureExpr::Int(0))
            {
                has_nonneg_lower = true;
            }
        }
        match width {
            Some(w) if has_nonneg_lower => {
                widths.insert(var, w);
            }
            // Either no recoverable width or a signed variable: bail.
            _ => return None,
        }
    }
    Some(widths)
}

fn uniform_width(widths: &HashMap<String, u32>) -> Option<u32> {
    let mut iter = widths.values().copied();
    let first = iter.next()?;
    if iter.all(|w| w == first) {
        Some(first)
    } else {
        None
    }
}

/// Conservative integer interval over-approximation for a finite-enumerable
/// expression, given each free variable's unsigned range `[0, 2^W - 1]`.
///
/// Returns `None` for any node it cannot soundly bound (forcing the caller to
/// BAIL rather than risk an unsound spec encoding).
fn interval(expr: &PureExpr, widths: &HashMap<String, u32>) -> Option<(i128, i128)> {
    match expr {
        PureExpr::Int(c) => Some((i128::from(*c), i128::from(*c))),
        PureExpr::Bool(_) => None,
        PureExpr::Var(name, _) => {
            let w = *widths.get(name.as_str())?;
            // The width comes from a map this function does not own. `1i128 << w`
            // is undefined for w >= 128, and at w == 127 it wraps to i128::MIN,
            // which would hand back a NEGATIVE upper bound for an unsigned range
            // and poison every interval computed from it. checked_shl rejects the
            // first case and checked_sub the second.
            let upper = 1i128.checked_shl(w)?.checked_sub(1)?;
            Some((0, upper))
        }
        PureExpr::View(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::LetAssume { body: inner, .. }
        | PureExpr::LetObligation { body: inner, .. } => interval(inner, widths),
        PureExpr::UnOp(UnOp::Neg, inner) => {
            let (lo, hi) = interval(inner, widths)?;
            // i128::MIN has no negation; every other operator here is already
            // checked, so this was the one arm that could still wrap.
            Some((hi.checked_neg()?, lo.checked_neg()?))
        }
        PureExpr::Ite(_, then_br, else_br) => {
            let (lo1, hi1) = interval(then_br, widths)?;
            let (lo2, hi2) = interval(else_br, widths)?;
            Some((lo1.min(lo2), hi1.max(hi2)))
        }
        PureExpr::LogicFnCall { name, args } => {
            let (bits, signed) = crate::encoder::parse_int_bitop_name(name)?;
            let [inner] = args.as_slice() else {
                return None;
            };
            machine_bitop_interval(inner, bits, signed, widths)
        }
        PureExpr::BinOp(l, op, r) => {
            let (lo1, hi1) = interval(l, widths)?;
            let (lo2, hi2) = interval(r, widths)?;
            match op {
                BinOp::Add => Some((lo1.checked_add(lo2)?, hi1.checked_add(hi2)?)),
                BinOp::Sub => Some((lo1.checked_sub(hi2)?, hi1.checked_sub(lo2)?)),
                BinOp::Mul => {
                    let corners = [
                        lo1.checked_mul(lo2)?,
                        lo1.checked_mul(hi2)?,
                        hi1.checked_mul(lo2)?,
                        hi1.checked_mul(hi2)?,
                    ];
                    let lo = *corners.iter().min()?;
                    let hi = *corners.iter().max()?;
                    Some((lo, hi))
                }
                // AND with non-negative operands cannot exceed either operand.
                BinOp::BitAnd if lo1 >= 0 && lo2 >= 0 => Some((0, hi1.min(hi2))),
                // OR/XOR with non-negative operands: bounded by the all-ones
                // value covering the wider operand.
                BinOp::BitOr | BinOp::BitXor if lo1 >= 0 && lo2 >= 0 => {
                    Some((0, all_ones_cover(hi1.max(hi2))?))
                }
                // Logical right shift only shrinks a non-negative value.
                BinOp::Shr if lo1 >= 0 && lo2 >= 0 => Some((0, hi1)),
                // Left shift by a bounded non-negative amount: `a << s` is
                // `a * 2^s`, so the bound is the PRODUCT `hi1 * 2^hi2`,
                // checked for value overflow. `i128::checked_shl` checks
                // only the shift count (`(2^64 - 1).checked_shl(64)` is
                // `Some(-2^64)`, a negative "upper bound" that certified the
                // node in the window and skipped its wrap guard).
                BinOp::Shl if lo1 >= 0 && lo2 >= 0 => {
                    let factor = 2i128.checked_pow(u32::try_from(hi2).ok()?)?;
                    Some((0, hi1.checked_mul(factor)?))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Interval of the machine bit operation `inner` at its type (`bits` wide,
/// `signed`), the `__trust_wp_int_bitop_*` marker (D-242). The Rust value is
/// the operation's mathematical value reduced into the type; when the
/// mathematical interval lies in the type's non-negative range nothing is
/// reduced. Otherwise an unsigned result lies in `[0, 2^bits)`, and `!` of an
/// unsigned operand in `[lo, hi]` is `2^bits - 1 - a`.
fn machine_bitop_interval(
    inner: &PureExpr,
    bits: u32,
    signed: bool,
    widths: &HashMap<String, u32>,
) -> Option<(i128, i128)> {
    let nonneg_bits = if signed { bits.checked_sub(1)? } else { bits };
    let type_hi = 1i128.checked_shl(nonneg_bits)?.checked_sub(1)?;
    if let PureExpr::UnOp(UnOp::BitNot, operand) = inner {
        if signed {
            return None;
        }
        let (lo, hi) = interval(operand, widths)?;
        if lo < 0 || hi > type_hi {
            return None;
        }
        return Some((type_hi.checked_sub(hi)?, type_hi.checked_sub(lo)?));
    }
    let math = interval(inner, widths);
    if let Some((lo, hi)) = math {
        if lo >= 0 && hi <= type_hi {
            return Some((lo, hi));
        }
    }
    (!signed).then_some((0, type_hi))
}

/// Smallest `2^k - 1` that is `>= value` (for a non-negative `value`).
///
/// Exact for every non-negative `i128`: `2^k - 1` with `k` the bit length of
/// `value` never exceeds `i128::MAX`. (The earlier loop stopped at
/// `2^101 - 1`, an UNDER-approximation for a larger `value`.)
fn all_ones_cover(value: i128) -> Option<i128> {
    if value <= 0 {
        return Some(0);
    }
    let bits = 128 - value.leading_zeros();
    1i128
        .checked_shl(bits)?
        .checked_sub(1)
        .filter(|cover| *cover >= value)
}

/// Shared encoding context: the uniform width, its modulus `2^W`, each free
/// variable's recovered width (for the interval analysis) and BV term.
struct BvEnc<'a> {
    width: u32,
    modulus: i128,
    widths: &'a HashMap<String, u32>,
    var_terms: &'a HashMap<String, Term>,
}

impl BvEnc<'_> {
    /// Whether the conservative interval analysis certifies `expr`'s integer
    /// value inside the window `[0, 2^W)` for every input in the window.
    fn certified_in_window(&self, expr: &PureExpr) -> bool {
        interval(expr, self.widths).is_some_and(|(lo, hi)| lo >= 0 && hi < self.modulus)
    }
}

/// OR together a list of Bool terms (`false` when empty).
fn disjunction(solver: &mut Solver, terms: &[Term]) -> Term {
    let mut acc = solver.bool_const(false);
    for term in terms {
        acc = solver.or(acc, *term);
    }
    acc
}

/// Encode a value-typed finite-enumerable expression as a `BitVec(width)` term
/// that equals the expression's mathematical-`Int` value whenever none of the
/// WRAP conditions pushed onto `wraps` holds (see the module docs). Returns
/// `None` on any unsupported node or out-of-window literal.
///
/// Invariant (induction on the expression): for every assignment of the free
/// variables inside the window, if every condition in `wraps` is false then
/// the returned term's unsigned value equals the node's integer value (which
/// therefore lies in `[0, 2^W)`).
fn encode_bv(
    solver: &mut Solver,
    expr: &PureExpr,
    enc: &BvEnc<'_>,
    wraps: &mut Vec<Term>,
) -> Option<Term> {
    let width = enc.width;
    match expr {
        PureExpr::Int(c) => {
            if *c < 0 || (i128::from(*c) >= enc.modulus) {
                return None;
            }
            Some(solver.bv_const_u64(*c as u64, width))
        }
        PureExpr::Var(name, _) => enc.var_terms.get(name.as_str()).copied(),
        PureExpr::View(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::LetAssume { body: inner, .. }
        | PureExpr::LetObligation { body: inner, .. } => encode_bv(solver, inner, enc, wraps),
        PureExpr::UnOp(op, inner) => {
            let t = encode_bv(solver, inner, enc, wraps)?;
            match op {
                // `-a` is in the window only at `a = 0`; elsewhere `bvneg`
                // returns `2^W - a`, not the negative integer.
                UnOp::Neg => {
                    if !enc.certified_in_window(expr) {
                        let zero = solver.bv_const_u64(0, width);
                        let is_zero = solver.eq(t, zero);
                        wraps.push(solver.not(is_zero));
                    }
                    Some(solver.bvneg(t))
                }
                // `~a = -a - 1` is negative for every in-window `a`: never
                // exact in an unsigned window. Refuse.
                _ => None,
            }
        }
        PureExpr::LogicFnCall { name, args } => {
            let (bits, signed) = crate::encoder::parse_int_bitop_name(name)?;
            let [inner] = args.as_slice() else {
                return None;
            };
            encode_machine_bitop(solver, inner, bits, signed, enc, wraps)
        }
        PureExpr::Ite(cond, then_br, else_br) => {
            let c = encode_bool(solver, cond, enc, wraps)?;
            // A branch must be exact only where it is selected.
            let mut then_wraps = Vec::new();
            let t = encode_bv(solver, then_br, enc, &mut then_wraps)?;
            let mut else_wraps = Vec::new();
            let e = encode_bv(solver, else_br, enc, &mut else_wraps)?;
            if !then_wraps.is_empty() {
                let any = disjunction(solver, &then_wraps);
                wraps.push(solver.and(c, any));
            }
            if !else_wraps.is_empty() {
                let any = disjunction(solver, &else_wraps);
                let not_c = solver.not(c);
                wraps.push(solver.and(not_c, any));
            }
            Some(solver.ite(c, t, e))
        }
        PureExpr::BinOp(l, op, r) => {
            let lt = encode_bv(solver, l, enc, wraps)?;
            let rt = encode_bv(solver, r, enc, wraps)?;
            let in_window = enc.certified_in_window(expr);
            match op {
                BinOp::Add => {
                    if !in_window {
                        let fits = solver.try_bvadd_no_overflow(lt, rt, false).ok()?;
                        wraps.push(solver.not(fits));
                    }
                    Some(solver.bvadd(lt, rt))
                }
                BinOp::Sub => {
                    if !in_window {
                        // Unsigned borrow: the integer difference is negative.
                        wraps.push(solver.bvult(lt, rt));
                    }
                    Some(solver.bvsub(lt, rt))
                }
                BinOp::Mul => {
                    if !in_window {
                        let fits = solver.try_bvmul_no_overflow(lt, rt, false).ok()?;
                        wraps.push(solver.not(fits));
                    }
                    Some(solver.bvmul(lt, rt))
                }
                BinOp::Shl => {
                    let shifted = solver.bvshl(lt, rt);
                    if !in_window {
                        // `a << s = a * 2^s`. At `s >= W` the BV result is 0;
                        // below it, the shift lost bits iff shifting back
                        // does not recover `a`.
                        let w_const = solver.bv_const_u64(u64::from(width), width);
                        let too_far = solver.bvuge(rt, w_const);
                        let back = solver.bvlshr(shifted, rt);
                        let same = solver.eq(back, lt);
                        let lost = solver.not(same);
                        wraps.push(solver.or(too_far, lost));
                    }
                    Some(shifted)
                }
                // Exact on exact, in-window (non-negative) operands: bitwise
                // ops act on the binary digits, and `bvlshr` is
                // `floor(a / 2^s)` (both 0 once `s >= W`).
                BinOp::BitAnd => Some(solver.bvand(lt, rt)),
                BinOp::BitOr => Some(solver.bvor(lt, rt)),
                BinOp::BitXor => Some(solver.bvxor(lt, rt)),
                BinOp::Shr => Some(solver.bvlshr(lt, rt)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Encode the machine bit operation `inner` AT ITS TYPE (`bits` wide,
/// `signed`; the `__trust_wp_int_bitop_*` marker, D-242) under the same
/// invariant as [`encode_bv`]: the term equals the operation's Rust value
/// whenever no wrap condition holds, for every execution in which the
/// type's values are in range.
///
/// * `&`, `|`, `^`, `>>` of exact non-negative operands never leave the type:
///   the Rust value is the mathematical one, encoded as [`encode_bv`] does.
/// * Unsigned `a << s` is `a * 2^s mod 2^bits`. At `bits <= W` that is
///   `bvshl` at W masked to `bits` bits (`bvshl` at W already reduces mod
///   `2^W`), exact with no guard. Above W the shift must lose no bit at W
///   (the guarded mathematical shift), so nothing reaches bit `bits` either.
///   A signed `<<` is read the same way only below its sign bit; above it the
///   result may be negative, outside the window: refused.
/// * Unsigned `!a` is `2^bits - 1 - a`: `bvxor` with the type's mask at
///   `bits <= W`; above W it leaves the window. A signed `!a = -a - 1` is
///   negative: refused.
fn encode_machine_bitop(
    solver: &mut Solver,
    inner: &PureExpr,
    bits: u32,
    signed: bool,
    enc: &BvEnc<'_>,
    wraps: &mut Vec<Term>,
) -> Option<Term> {
    let width = enc.width;
    let nonneg_bits = if signed { bits.checked_sub(1)? } else { bits };
    let type_mask = |solver: &mut Solver| -> Option<Term> {
        let mask = 1u64.checked_shl(bits).map_or(u64::MAX, |m| m - 1);
        (bits <= width).then(|| solver.bv_const_u64(mask, width))
    };
    match inner {
        PureExpr::BinOp(_, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shr, _) => {
            encode_bv(solver, inner, enc, wraps)
        }
        PureExpr::BinOp(l, BinOp::Shl, r) => {
            if !signed && bits <= width {
                let lt = encode_bv(solver, l, enc, wraps)?;
                let rt = encode_bv(solver, r, enc, wraps)?;
                let shifted = solver.bvshl(lt, rt);
                if bits == width {
                    return Some(shifted);
                }
                let mask = type_mask(solver)?;
                return Some(solver.bvand(shifted, mask));
            }
            if width > nonneg_bits {
                return None;
            }
            encode_bv(solver, inner, enc, wraps)
        }
        PureExpr::UnOp(UnOp::BitNot, operand) => {
            if signed || bits > width {
                return None;
            }
            let t = encode_bv(solver, operand, enc, wraps)?;
            let mask = type_mask(solver)?;
            Some(solver.bvxor(t, mask))
        }
        _ => None,
    }
}

/// Encode a Bool-typed finite-enumerable guard/comparison as a Bool term,
/// exact under the same wrap discipline as [`encode_bv`].
fn encode_bool(
    solver: &mut Solver,
    expr: &PureExpr,
    enc: &BvEnc<'_>,
    wraps: &mut Vec<Term>,
) -> Option<Term> {
    match expr {
        PureExpr::Bool(b) => Some(solver.bool_const(*b)),
        PureExpr::View(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::LetAssume { body: inner, .. }
        | PureExpr::LetObligation { body: inner, .. } => encode_bool(solver, inner, enc, wraps),
        PureExpr::UnOp(UnOp::Not, inner) => {
            let t = encode_bool(solver, inner, enc, wraps)?;
            Some(solver.not(t))
        }
        PureExpr::BinOp(l, op, r) => match op {
            BinOp::And => {
                let lt = encode_bool(solver, l, enc, wraps)?;
                let rt = encode_bool(solver, r, enc, wraps)?;
                Some(solver.and(lt, rt))
            }
            BinOp::Or => {
                let lt = encode_bool(solver, l, enc, wraps)?;
                let rt = encode_bool(solver, r, enc, wraps)?;
                Some(solver.or(lt, rt))
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                // Both operands exact and in-window: the unsigned comparison
                // agrees with the integer comparison.
                let lt = encode_bv(solver, l, enc, wraps)?;
                let rt = encode_bv(solver, r, enc, wraps)?;
                Some(encode_cmp(solver, *op, lt, rt))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Encode an (unsigned) BV comparison as a Bool term.
fn encode_cmp(solver: &mut Solver, op: BinOp, lhs: Term, rhs: Term) -> Term {
    match op {
        BinOp::Eq => solver.eq(lhs, rhs),
        BinOp::Ne => {
            let eq = solver.eq(lhs, rhs);
            solver.not(eq)
        }
        BinOp::Lt => solver.bvult(lhs, rhs),
        BinOp::Le => solver.bvule(lhs, rhs),
        BinOp::Gt => solver.bvugt(lhs, rhs),
        BinOp::Ge => solver.bvuge(lhs, rhs),
        // `encode_cmp` is only called with a comparison op (guarded by callers).
        _ => solver.bool_const(false),
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, sync::Arc};

    use ay_dpll::api::{Logic, Solver};
    use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

    use super::{encode_bv, encode_cmp, interval, BvEnc};

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }
    fn int(v: i64) -> PureExpr {
        PureExpr::Int(v)
    }
    fn bin(l: PureExpr, op: BinOp, r: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(l), op, Arc::new(r))
    }
    fn ite(c: PureExpr, t: PureExpr, e: PureExpr) -> PureExpr {
        PureExpr::Ite(Arc::new(c), Arc::new(t), Arc::new(e))
    }

    /// The SWAR body of `count8` as a `PureExpr` over `n` (mirrors the driver's
    /// lowering of the function body).
    fn count8_swar() -> PureExpr {
        let n = || var("n");
        // x1 = n - ((n >> 1) & 0x55)
        let x1 = bin(
            n(),
            BinOp::Sub,
            bin(bin(n(), BinOp::Shr, int(1)), BinOp::BitAnd, int(0x55)),
        );
        // x2 = (x1 & 0x33) + ((x1 >> 2) & 0x33)
        let x2 = bin(
            bin(x1.clone(), BinOp::BitAnd, int(0x33)),
            BinOp::Add,
            bin(bin(x1, BinOp::Shr, int(2)), BinOp::BitAnd, int(0x33)),
        );
        // x3 = (x2 + (x2 >> 4)) & 0x0F
        bin(
            bin(x2.clone(), BinOp::Add, bin(x2, BinOp::Shr, int(4))),
            BinOp::BitAnd,
            int(0x0F),
        )
    }

    /// `count8_log(n)` body: the per-bit ITE sum.
    fn count8_log() -> PureExpr {
        let bit = |mask: i64| {
            ite(
                bin(bin(var("n"), BinOp::BitAnd, int(mask)), BinOp::Eq, int(0)),
                int(0),
                int(1),
            )
        };
        let mut sum = bit(1);
        for mask in [2, 4, 8, 0x10, 0x20, 0x40, 0x80] {
            sum = bin(sum, BinOp::Add, bit(mask));
        }
        sum
    }

    fn widths_n8() -> HashMap<String, u32> {
        let mut w = HashMap::new();
        w.insert("n".to_string(), 8u32);
        w
    }

    /// Encode `func <op> spec` natively in QF_BV (width 8) and return whether the
    /// negated goal is UNSAT — i.e. whether the obligation holds for all `n`.
    fn obligation_holds(func: &PureExpr, op: BinOp, spec: &PureExpr) -> bool {
        let widths = widths_n8();
        let mut solver = Solver::new(Logic::QfBv);
        let n = solver.bv_var("n", 8);
        let mut vt = HashMap::new();
        vt.insert("n".to_string(), n);
        let enc = BvEnc {
            width: 8,
            modulus: 256,
            widths: &widths,
            var_terms: &vt,
        };
        let mut wraps = Vec::new();
        let ft = encode_bv(&mut solver, func, &enc, &mut wraps).expect("encode func");
        let st = encode_bv(&mut solver, spec, &enc, &mut wraps).expect("encode spec");
        let goal = encode_cmp(&mut solver, op, ft, st);
        let mut refutation = solver.not(goal);
        for wrap in &wraps {
            refutation = solver.or(refutation, *wrap);
        }
        solver.assert_term(refutation);
        solver.check_sat().is_unsat()
    }

    #[test]
    fn count8_swar_equals_popcount_is_unsat_negation() {
        // result@ == count8_log(n)  holds for all n  =>  negation UNSAT.
        assert!(obligation_holds(&count8_swar(), BinOp::Eq, &count8_log()));
    }

    #[test]
    fn count8_swar_le_8_holds() {
        assert!(obligation_holds(&count8_swar(), BinOp::Le, &int(8)));
    }

    #[test]
    fn corrupted_plus_one_is_not_provable() {
        // result@ == count8_log(n) + 1  must NOT hold (counterexample exists),
        // i.e. the negated goal is SAT, not UNSAT. (cardinal no-false-accept)
        let corrupt = bin(count8_log(), BinOp::Add, int(1));
        assert!(!obligation_holds(&count8_swar(), BinOp::Eq, &corrupt));
    }

    #[test]
    fn corrupted_minus_one_is_not_provable() {
        let corrupt = bin(count8_log(), BinOp::Sub, int(1));
        assert!(!obligation_holds(&count8_swar(), BinOp::Eq, &corrupt));
    }

    #[test]
    fn count8_log_interval_stays_in_byte_range() {
        // The soundness side-condition: count8_log(n) in [0, 8] ⊆ [0, 2^8).
        let (lo, hi) = interval(&count8_log(), &widths_n8()).expect("bounded");
        assert_eq!(lo, 0);
        assert!((8..256).contains(&hi), "hi={hi}");
    }

    /// Regression (trait-refinement e2e, StrongerPost::refine): once the
    /// #route-100 r3 relaxation admitted integer-literal spec sides, a plain
    /// signed-arithmetic obligation — `ensures(result > 0)` over `return
    /// x + 1` with `x: i32` guarded by `x >= 0` — recovered unsigned width 31
    /// from the range preconditions and got its `+` encoded as a WRAPPING
    /// `bvadd`, minting a spurious counterexample at `x = 2^31 - 1`. The lane
    /// must bail (fall through to the general path) instead of reporting
    /// `Failed`: the func side `x + 1` provably exceeds `[0, 2^31)`, so a SAT
    /// model may only witness a wrapped behavior the driver's exact math-Int
    /// model does not have.
    #[test]
    fn signed_arith_over_range_recovered_width_must_not_mint_counterexample() {
        use super::{
            super::super::solver_tail::ObligationSliceContext, try_prove_bitwise_bv_obligation,
        };

        let ensure = bin(var("result"), BinOp::Gt, int(0));
        let return_expr = bin(var("x"), BinOp::Add, int(1));
        let requires = vec![
            bin(var("x"), BinOp::Ge, int(0)),
            bin(
                PureExpr::View(Arc::new(var("x"))),
                BinOp::Ge,
                int(-2_147_483_648),
            ),
            bin(
                PureExpr::View(Arc::new(var("x"))),
                BinOp::Le,
                int(2_147_483_647),
            ),
        ];
        let ensures = vec![ensure.clone()];
        let ctx = ObligationSliceContext {
            all_ensures: &ensures,
            requires: &requires,
            logic_fns: Some(&[]),
            mode_overrides: None,
            type_invariants: None,
            return_expr: Some(&return_expr),
            mut_borrow_final_values: None,
            mutation_continued_params: None,
            body_div_obligations: &[],
            fresh_base_recheck: None,
            literal_false_base_recheck: None,
            slice_length_stable_vars: None,
            base_recheck_pathology: std::cell::Cell::new(false),
        };
        let result = try_prove_bitwise_bv_obligation(&ensure, &ctx);
        assert!(
            result.is_none(),
            "the BV fast path must bail on an out-of-range func side, \
             never mint a wrapped-model counterexample: {result:?}"
        );
        // The mechanism: `x + 1` at recovered width 31 exceeds the modulus.
        let mut widths = HashMap::new();
        widths.insert("x".to_string(), 31u32);
        let (lo, hi) = interval(&bin(var("x"), BinOp::Add, int(1)), &widths).expect("bounded");
        assert_eq!(lo, 1);
        assert_eq!(hi, 1i128 << 31, "x+1 reaches the modulus, so it can wrap");
    }

    #[test]
    fn width_recovery_folds_symbolic_u64_bound() {
        // The driver injects u64 range preconditions with the SYMBOLIC
        // `pow2_expr(64) - 1` tree (2^64 - 1 does not fit `PureExpr::Int`'s
        // i64). Width recovery must constant-fold it to W = 64 exactly.
        let requires = vec![
            bin(PureExpr::View(Arc::new(var("n"))), BinOp::Ge, int(0)),
            bin(
                PureExpr::View(Arc::new(var("n"))),
                BinOp::Le,
                trust_wp_core::formula::int_bounds::unsigned_max_expr(64),
            ),
        ];
        let widths =
            super::recover_unsigned_widths(&var("n"), &requires).expect("u64 width recovered");
        assert_eq!(widths.get("n"), Some(&64u32));
    }

    #[test]
    fn width_recovery_rejects_non_power_of_two_and_u128_bounds() {
        // A `<= 100` bound is not `2^W - 1`: no width, must bail.
        let requires_100 = vec![
            bin(PureExpr::View(Arc::new(var("n"))), BinOp::Ge, int(0)),
            bin(PureExpr::View(Arc::new(var("n"))), BinOp::Le, int(100)),
        ];
        assert!(super::recover_unsigned_widths(&var("n"), &requires_100).is_none());
        // u128's symbolic bound overflows the exact i128 fold: must bail
        // (fail-closed), never approximate.
        let requires_u128 = vec![
            bin(PureExpr::View(Arc::new(var("n"))), BinOp::Ge, int(0)),
            bin(
                PureExpr::View(Arc::new(var("n"))),
                BinOp::Le,
                trust_wp_core::formula::int_bounds::unsigned_max_expr(128),
            ),
        ];
        assert!(super::recover_unsigned_widths(&var("n"), &requires_u128).is_none());
    }

    #[test]
    fn unop_neg_guarded_and_bitnot_refused() {
        // `-n` encodes with a wrap guard (exact only at n = 0); `~n` has the
        // negative integer value `-n - 1` and is refused outright.
        let widths = widths_n8();
        assert!(interval(&PureExpr::UnOp(UnOp::Neg, Arc::new(int(3))), &widths).is_some());
        let mut solver = Solver::new(Logic::QfBv);
        let n = solver.bv_var("n", 8);
        let mut vt = HashMap::new();
        vt.insert("n".to_string(), n);
        let enc = BvEnc {
            width: 8,
            modulus: 256,
            widths: &widths,
            var_terms: &vt,
        };
        let mut wraps = Vec::new();
        let neg = PureExpr::UnOp(UnOp::Neg, Arc::new(var("n")));
        assert!(encode_bv(&mut solver, &neg, &enc, &mut wraps).is_some());
        assert_eq!(wraps.len(), 1, "unary minus must carry a wrap guard");
        let not = PureExpr::UnOp(UnOp::BitNot, Arc::new(var("n")));
        assert!(encode_bv(&mut solver, &not, &enc, &mut Vec::new()).is_none());
    }

    fn i32_nonneg_requires(name: &str) -> Vec<PureExpr> {
        vec![
            bin(var(name), BinOp::Ge, int(0)),
            bin(
                PureExpr::View(Arc::new(var(name))),
                BinOp::Ge,
                int(-2_147_483_648),
            ),
            bin(
                PureExpr::View(Arc::new(var(name))),
                BinOp::Le,
                int(2_147_483_647),
            ),
        ]
    }

    fn run_lane(
        ensure: &PureExpr,
        return_expr: &PureExpr,
        requires: &[PureExpr],
        logic_fns: &[trust_wp_core::logic::LogicFnDef],
    ) -> Option<super::super::super::VerificationResult> {
        use super::{
            super::super::solver_tail::ObligationSliceContext, try_prove_bitwise_bv_obligation,
        };
        let ensures = vec![ensure.clone()];
        let ctx = ObligationSliceContext {
            all_ensures: &ensures,
            requires,
            logic_fns: Some(logic_fns),
            mode_overrides: None,
            type_invariants: None,
            return_expr: Some(return_expr),
            mut_borrow_final_values: None,
            mutation_continued_params: None,
            body_div_obligations: &[],
            fresh_base_recheck: None,
            literal_false_base_recheck: None,
            slice_length_stable_vars: None,
            base_recheck_pathology: std::cell::Cell::new(false),
        };
        try_prove_bitwise_bv_obligation(ensure, &ctx)
    }

    /// Regression (r29 false Verified): `#[requires(x >= 0)]
    /// #[ensures(result >= 0)] fn pred(x: i32) -> i32 { x - 1 }` is FALSE at
    /// `x = 0` (returns -1, no i32 overflow). Width recovery narrows the i32 to
    /// W = 31 from `x >= 0` and `x@ <= 2^31 - 1`, and an unguarded 31-bit
    /// `bvsub` makes `bvuge(x - 1, 0)` a tautology, so the lane minted a fully
    /// checked UNSAT certificate (`Verified(Some{strict_verified: true})`).
    /// The lane must never return Verified here.
    #[test]
    fn narrowed_width_sub_underflow_must_not_verify() {
        let ensure = bin(var("result"), BinOp::Ge, int(0));
        let return_expr = bin(var("x"), BinOp::Sub, int(1));
        let result = run_lane(&ensure, &return_expr, &i32_nonneg_requires("x"), &[]);
        assert!(
            !matches!(
                result,
                Some(super::super::super::VerificationResult::Verified(_))
            ),
            "x - 1 >= 0 is false at x = 0; the BV lane must not accept it: {result:?}"
        );
        // And the same shape at the type's own unsigned width (u8, `x - 1`
        // underflows at x = 0 in the driver's exact Int model).
        let requires_u8 = vec![
            bin(PureExpr::View(Arc::new(var("x"))), BinOp::Ge, int(0)),
            bin(PureExpr::View(Arc::new(var("x"))), BinOp::Le, int(255)),
        ];
        let result = run_lane(&ensure, &return_expr, &requires_u8, &[]);
        assert!(
            !matches!(
                result,
                Some(super::super::super::VerificationResult::Verified(_))
            ),
            "u8 x - 1 >= 0 must not verify through the wrapping encoding: {result:?}"
        );
    }

    /// The other wrapping operators at the narrowed width W = 31. Each goal is
    /// FALSE in the driver's exact Int model (witness in the comment) yet a
    /// tautology under an unguarded 31-bit encoding, whose values all lie in
    /// `[0, 2^31)`.
    #[test]
    fn narrowed_width_add_mul_shl_neg_must_not_verify() {
        let reqs = i32_nonneg_requires("x");
        let not_verified = |ensure: PureExpr, ret: PureExpr| {
            let result = run_lane(&ensure, &ret, &reqs, &[]);
            assert!(
                !matches!(
                    result,
                    Some(super::super::super::VerificationResult::Verified(_))
                ),
                "false obligation accepted: {ensure:?} over {ret:?}: {result:?}"
            );
        };
        let max31 = (1i64 << 31) - 1;
        // x + 2^30 <= 2^31 - 1 is FALSE at x = 2^30 (= 2^31).
        not_verified(
            bin(var("result"), BinOp::Le, int(max31)),
            bin(var("x"), BinOp::Add, int(1 << 30)),
        );
        // x * 2 <= 2^31 - 1 is FALSE at x = 2^30 (= 2^31).
        not_verified(
            bin(var("result"), BinOp::Le, int(max31)),
            bin(var("x"), BinOp::Mul, int(2)),
        );
        // x << 1 <= 2^31 - 1 is FALSE at x = 2^30 in the Int model (a * 2^k).
        not_verified(
            bin(var("result"), BinOp::Le, int(max31)),
            bin(var("x"), BinOp::Shl, int(1)),
        );
        // -x >= 0 is FALSE at x = 1.
        not_verified(
            bin(var("result"), BinOp::Ge, int(0)),
            PureExpr::UnOp(UnOp::Neg, Arc::new(var("x"))),
        );
    }

    fn u8_requires(name: &str) -> Vec<PureExpr> {
        vec![
            bin(PureExpr::View(Arc::new(var(name))), BinOp::Ge, int(0)),
            bin(PureExpr::View(Arc::new(var(name))), BinOp::Le, int(255)),
        ]
    }

    fn is_verified(result: &Option<super::super::super::VerificationResult>) -> bool {
        matches!(
            result,
            Some(super::super::super::VerificationResult::Verified(_))
        )
    }

    fn view_result() -> PureExpr {
        PureExpr::View(Arc::new(var("result")))
    }

    /// Regression (r30): with `result` on the RIGHT of the ensures the lane
    /// compared `func <cmp> spec`, so `5 <= result@` over `x & 0` was checked
    /// as the true `0 <= 5`. The operand order is kept now: the false
    /// contracts do not verify and the true mirrored ones do.
    #[test]
    fn spec_on_the_left_keeps_the_comparison_direction() {
        let reqs = u8_requires("x");
        let and0 = bin(var("x"), BinOp::BitAnd, int(0));
        let shr6 = bin(var("x"), BinOp::Shr, int(6));
        for (ensure, ret) in [
            (bin(int(5), BinOp::Le, view_result()), and0.clone()),
            (bin(int(5), BinOp::Lt, view_result()), shr6.clone()),
            (
                bin(int(1), BinOp::Lt, view_result()),
                bin(var("x"), BinOp::Shr, int(7)),
            ),
            (
                bin(int(100), BinOp::Ge, view_result()),
                bin(var("x"), BinOp::BitOr, int(0)),
            ),
        ] {
            let result = run_lane(&ensure, &ret, &reqs, &[]);
            assert!(!is_verified(&result), "{ensure:?} over {ret:?}: {result:?}");
        }
        for (ensure, ret) in [
            (
                bin(int(5), BinOp::Ge, view_result()),
                bin(var("x"), BinOp::BitAnd, int(3)),
            ),
            (bin(int(4), BinOp::Gt, view_result()), shr6),
            (
                bin(int(255), BinOp::Ge, view_result()),
                bin(var("x"), BinOp::BitOr, int(0)),
            ),
            (bin(int(0), BinOp::Le, view_result()), and0),
        ] {
            let result = run_lane(&ensure, &ret, &reqs, &[]);
            assert!(is_verified(&result), "{ensure:?} over {ret:?}: {result:?}");
        }
    }

    /// Regression (r30): `interval` bounded `a << s` with
    /// `hi1.checked_shl(hi2)`, which checks only the shift COUNT:
    /// `(2^64 - 1) << 64` came back as `Some(-2^64)`, certified the node in
    /// the 64-bit window and skipped its wrap guard, so `x << 64 == 0` was
    /// proved for an `i128`/`u128` `x <= 2^64 - 1` (`f(1) == 2^64`).
    #[test]
    fn shl_interval_checks_the_value_not_only_the_count() {
        let mut widths = HashMap::new();
        widths.insert("x".to_string(), 64u32);
        let shl64 = bin(var("x"), BinOp::Shl, int(64));
        assert_eq!(
            interval(&shl64, &widths),
            None,
            "(2^64 - 1) * 2^64 overflows i128"
        );
        widths.insert("x".to_string(), 8u32);
        let shl4 = bin(var("x"), BinOp::Shl, int(4));
        assert_eq!(interval(&shl4, &widths), Some((0, 255 * 16)));

        let requires = vec![
            bin(var("x"), BinOp::Ge, int(0)),
            bin(
                PureExpr::View(Arc::new(var("x"))),
                BinOp::Le,
                trust_wp_core::formula::int_bounds::unsigned_max_expr(64),
            ),
        ];
        let ensure = bin(view_result(), BinOp::Eq, int(0));
        for signed in [true, false] {
            let marked = machine_bitop(signed, 128, shl64.clone());
            for ret in [shl64.clone(), marked] {
                let result = run_lane(&ensure, &ret, &requires, &[]);
                assert!(
                    !is_verified(&result),
                    "x << 64 == 0 accepted for {ret:?}: {result:?}"
                );
            }
        }
    }

    fn machine_bitop(signed: bool, bits: u32, inner: PureExpr) -> PureExpr {
        PureExpr::LogicFnCall {
            name: trust_wp_core::formula::internal::machine_bitop::name(signed, bits),
            args: vec![inner],
        }
    }

    /// A `u8` `<<` reaches the lane as the machine operation at its type
    /// (D-242): the bits shifted out are dropped. At the type's own width
    /// the lane encodes it exactly (no guard), and at a WIDER recovered
    /// window (a `x@ <= 65535` premise) it masks to 8 bits instead of reading
    /// `x * 16`: `x << 4 <= 240` holds, `x << 4 == x * 16` does not.
    #[test]
    fn machine_shl_drops_the_bits_above_its_type() {
        let shl4 = machine_bitop(false, 8, bin(var("x"), BinOp::Shl, int(4)));
        let reqs8 = u8_requires("x");
        let le240 = bin(view_result(), BinOp::Le, int(240));
        assert!(is_verified(&run_lane(&le240, &shl4, &reqs8, &[])));
        let le239 = bin(view_result(), BinOp::Le, int(239));
        assert!(!is_verified(&run_lane(&le239, &shl4, &reqs8, &[])));

        let reqs16 = vec![
            bin(PureExpr::View(Arc::new(var("x"))), BinOp::Ge, int(0)),
            bin(PureExpr::View(Arc::new(var("x"))), BinOp::Le, int(65535)),
        ];
        assert!(is_verified(&run_lane(&le240, &shl4, &reqs16, &[])));
        assert!(!is_verified(&run_lane(&le239, &shl4, &reqs16, &[])));
        let mut widths = HashMap::new();
        widths.insert("x".to_string(), 16u32);
        assert_eq!(interval(&shl4, &widths), Some((0, 255)));
    }

    /// `!x` on a `u8` is `255 - x` at its type; a signed `!` (negative) and
    /// a signed `<<` that may reach the sign bit are refused.
    #[test]
    fn machine_not_and_signed_shl() {
        let reqs8 = u8_requires("x");
        let not8 = machine_bitop(false, 8, PureExpr::UnOp(UnOp::BitNot, Arc::new(var("x"))));
        assert!(is_verified(&run_lane(
            &bin(view_result(), BinOp::Le, int(255)),
            &not8,
            &reqs8,
            &[]
        )));
        assert!(!is_verified(&run_lane(
            &bin(view_result(), BinOp::Le, int(254)),
            &not8,
            &reqs8,
            &[]
        )));
        let signed_not = machine_bitop(true, 8, PureExpr::UnOp(UnOp::BitNot, Arc::new(var("x"))));
        assert!(run_lane(
            &bin(view_result(), BinOp::Le, int(255)),
            &signed_not,
            &reqs8,
            &[]
        )
        .is_none());
        // i8 `x << 1` over x in [0, 255]: the sign bit is reachable.
        let signed_shl = machine_bitop(true, 8, bin(var("x"), BinOp::Shl, int(1)));
        assert!(run_lane(
            &bin(view_result(), BinOp::Le, int(255)),
            &signed_shl,
            &reqs8,
            &[]
        )
        .is_none());
    }

    /// The lane's purpose survives the guards: the u8 SWAR popcount still
    /// proves `result@ <= 8` natively (its `Sub` no-borrow guard is
    /// discharged by the bitblaster).
    #[test]
    fn swar_popcount_range_still_verifies_natively() {
        let requires_u8 = vec![
            bin(PureExpr::View(Arc::new(var("n"))), BinOp::Ge, int(0)),
            bin(PureExpr::View(Arc::new(var("n"))), BinOp::Le, int(255)),
        ];
        let ensure = bin(PureExpr::View(Arc::new(var("result"))), BinOp::Le, int(8));
        let result = run_lane(&ensure, &count8_swar(), &requires_u8, &[]);
        assert!(
            matches!(
                result,
                Some(super::super::super::VerificationResult::Verified(Some(_)))
            ),
            "the SWAR popcount range must still verify natively: {result:?}"
        );
    }
}
