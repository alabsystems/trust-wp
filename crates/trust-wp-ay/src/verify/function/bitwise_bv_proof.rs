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
//! body* (`return_expr`), whose `BitVec(W)` encoding is EXACT by Rust's wrapping
//! semantics (W is the function's integer width). The `spec` side is a
//! mathematical-`Int` expression; encoding it in `BitVec(W)` is exact only while
//! its value stays in `[0, 2^W)`. We therefore require — via a CONSERVATIVE
//! interval over-approximation — that the spec side cannot leave `[0, 2^W)` for
//! any input. When that holds, both sides' BV encodings equal their true values
//! and the (unsigned) BV comparison is equivalent to the source comparison, so:
//!   * UNSAT of the negated goal ⇒ the obligation holds for ALL inputs ⇒ Verified.
//!   * SAT ⇒ a genuine counterexample ⇒ Failed.
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

use super::super::{solver_tail::ObligationSliceContext, Counterexample, VerificationResult};

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

    // SOUNDNESS side-condition: the spec side must provably stay in [0, 2^W).
    // (The function side needs no interval bound for the VERIFIED direction:
    // BV wrapping only ADDS behaviors relative to the driver's exact math-Int
    // model, so UNSAT of the negation under wrapping is conservative. The
    // FAILED direction is the opposite — see `func_side_provably_in_range`
    // below.)
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
    // acceptance is unaffected (conservative per the asymmetry above), which
    // keeps the masked SWAR chains this lane exists for — whose `Sub` steps
    // the conservative interval cannot bound below zero — proving natively.
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

    let func_term = encode_bv(&mut solver, &func_expr, width, &var_terms)?;
    let spec_term = encode_bv(&mut solver, &spec_expr, width, &var_terms)?;
    let goal = encode_cmp(&mut solver, cmp, func_term, spec_term);

    // Assert  H1 & ... & Hk & not(goal)  — the negation of  (H1 & ... & Hk) => goal.
    let not_goal = solver.not(goal);
    let mut assertion = not_goal;
    for hyp in &hypotheses {
        let hyp_term = encode_bool(&mut solver, hyp, width, &var_terms)?;
        assertion = solver.and(assertion, hyp_term);
    }
    solver.assert_term(assertion);

    let verdict = solver.check_sat_with_details();
    if verdict.result.is_unsat() {
        let summary = crate::verify::extract_proof_summary(&solver)?;
        if !summary.is_fully_verified() {
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
    {
        Some(VerificationResult::Failed(Counterexample::empty()))
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
            Some((0, (1i128 << w) - 1))
        }
        PureExpr::View(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::LetAssume { body: inner, .. }
        | PureExpr::LetObligation { body: inner, .. } => interval(inner, widths),
        PureExpr::UnOp(UnOp::Neg, inner) => {
            let (lo, hi) = interval(inner, widths)?;
            Some((-hi, -lo))
        }
        PureExpr::Ite(_, then_br, else_br) => {
            let (lo1, hi1) = interval(then_br, widths)?;
            let (lo2, hi2) = interval(else_br, widths)?;
            Some((lo1.min(lo2), hi1.max(hi2)))
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
                    Some((0, all_ones_cover(hi1.max(hi2))))
                }
                // Logical right shift only shrinks a non-negative value.
                BinOp::Shr if lo1 >= 0 && lo2 >= 0 => Some((0, hi1)),
                // Left shift by a bounded non-negative amount.
                BinOp::Shl if lo1 >= 0 && lo2 >= 0 && hi2 <= 64 => {
                    let shifted = hi1.checked_shl(u32::try_from(hi2).ok()?)?;
                    Some((0, shifted))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Smallest `2^k - 1` that is `>= value` (for a non-negative `value`).
fn all_ones_cover(value: i128) -> i128 {
    if value <= 0 {
        return 0;
    }
    let mut cover: i128 = 1;
    // cover = 2^k - 1, growing until it covers `value` (capped to avoid overflow).
    while cover < value && cover < (1i128 << 100) {
        cover = (cover << 1) | 1;
    }
    cover
}

/// Encode a value-typed finite-enumerable expression as a `BitVec(width)` term.
/// Returns `None` on any unsupported node or out-of-range literal.
fn encode_bv(
    solver: &mut Solver,
    expr: &PureExpr,
    width: u32,
    var_terms: &HashMap<String, Term>,
) -> Option<Term> {
    match expr {
        PureExpr::Int(c) => {
            if *c < 0 || (i128::from(*c) >= (1i128 << width)) {
                return None;
            }
            Some(solver.bv_const_u64(*c as u64, width))
        }
        PureExpr::Var(name, _) => var_terms.get(name.as_str()).copied(),
        PureExpr::View(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::LetAssume { body: inner, .. }
        | PureExpr::LetObligation { body: inner, .. } => encode_bv(solver, inner, width, var_terms),
        PureExpr::UnOp(op, inner) => {
            let t = encode_bv(solver, inner, width, var_terms)?;
            match op {
                UnOp::Neg => Some(solver.bvneg(t)),
                UnOp::BitNot => Some(solver.bvnot(t)),
                _ => None,
            }
        }
        PureExpr::Ite(cond, then_br, else_br) => {
            let c = encode_bool(solver, cond, width, var_terms)?;
            let t = encode_bv(solver, then_br, width, var_terms)?;
            let e = encode_bv(solver, else_br, width, var_terms)?;
            Some(solver.ite(c, t, e))
        }
        PureExpr::BinOp(l, op, r) => {
            let lt = encode_bv(solver, l, width, var_terms)?;
            let rt = encode_bv(solver, r, width, var_terms)?;
            match op {
                BinOp::Add => Some(solver.bvadd(lt, rt)),
                BinOp::Sub => Some(solver.bvsub(lt, rt)),
                BinOp::Mul => Some(solver.bvmul(lt, rt)),
                BinOp::BitAnd => Some(solver.bvand(lt, rt)),
                BinOp::BitOr => Some(solver.bvor(lt, rt)),
                BinOp::BitXor => Some(solver.bvxor(lt, rt)),
                BinOp::Shl => Some(solver.bvshl(lt, rt)),
                BinOp::Shr => Some(solver.bvlshr(lt, rt)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Encode a Bool-typed finite-enumerable guard/comparison as a Bool term.
fn encode_bool(
    solver: &mut Solver,
    expr: &PureExpr,
    width: u32,
    var_terms: &HashMap<String, Term>,
) -> Option<Term> {
    match expr {
        PureExpr::Bool(b) => Some(solver.bool_const(*b)),
        PureExpr::View(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::LetAssume { body: inner, .. }
        | PureExpr::LetObligation { body: inner, .. } => {
            encode_bool(solver, inner, width, var_terms)
        }
        PureExpr::UnOp(UnOp::Not, inner) => {
            let t = encode_bool(solver, inner, width, var_terms)?;
            Some(solver.not(t))
        }
        PureExpr::BinOp(l, op, r) => match op {
            BinOp::And => {
                let lt = encode_bool(solver, l, width, var_terms)?;
                let rt = encode_bool(solver, r, width, var_terms)?;
                Some(solver.and(lt, rt))
            }
            BinOp::Or => {
                let lt = encode_bool(solver, l, width, var_terms)?;
                let rt = encode_bool(solver, r, width, var_terms)?;
                Some(solver.or(lt, rt))
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let lt = encode_bv(solver, l, width, var_terms)?;
                let rt = encode_bv(solver, r, width, var_terms)?;
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

    use super::{encode_bv, encode_cmp, interval};

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
        let ft = encode_bv(&mut solver, func, 8, &vt).expect("encode func");
        let st = encode_bv(&mut solver, spec, 8, &vt).expect("encode spec");
        let goal = encode_cmp(&mut solver, op, ft, st);
        let neg = solver.not(goal);
        solver.assert_term(neg);
        let _ = widths; // documents the recovered width used for encoding
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
    fn unop_neg_and_bitnot_encode() {
        // Exercise the unary BV ops so the encoder paths stay covered.
        let e = PureExpr::UnOp(UnOp::BitNot, Arc::new(var("n")));
        let widths = widths_n8();
        assert!(interval(&PureExpr::UnOp(UnOp::Neg, Arc::new(int(3))), &widths).is_some());
        let mut solver = Solver::new(Logic::QfBv);
        let n = solver.bv_var("n", 8);
        let mut vt = HashMap::new();
        vt.insert("n".to_string(), n);
        assert!(encode_bv(&mut solver, &e, 8, &vt).is_some());
    }
}
