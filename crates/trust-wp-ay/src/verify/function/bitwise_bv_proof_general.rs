// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generalized native QF_BV fast path: SIGNED widths + boolean obligation
//! structure (#route-100 rightmostbit).
//!
//! [`super::bitwise_bv_proof`] (tier 1) discharges the popcount shape: a
//! single unsigned comparison. This module (tier 2) generalizes the same
//! native-bitblast idea to the `bitvectors/rightmostbit.rs` family:
//!
//! * SIGNED variable domains recovered from paired premises
//!   `-2^(W-1) <= v@ <= 2^(W-1)-1` (and unsigned domains from `0 <= v@ <=
//!   2^W-1`), with `bvslt`/`bvsle`/... for signed comparisons;
//! * BOOLEAN obligation structure: `==>`, `&&`, `||`, `!`, `==`/`!=` on
//!   boolean operands (iff/xor), and the bounded `forall<i>` in positive
//!   polarity — anything else bails (`None`) to the general encoder;
//! * `wrapping_neg`-style call results: the driver injects the std wrapping
//!   spec as a requires TRIPLE (`in-range ==> v@ == E`, `E < MIN ==> v@ ==
//!   E + 2^W`, `E > MAX ==> v@ == E - 2^W`). The triple is recognized and
//!   replaced by the exact BV binding `v := enc(E)` — for `E = 0 - x@` that
//!   is precisely `bvneg(x)`, Rust's `wrapping_neg`.
//!
//! # Semantics proven against
//!
//! The obligation is interpreted over the formula's mathematical-`Int`
//! semantics: `+`, `-`, `*`, unary `-` are unbounded integer arithmetic;
//! `&`, `|`, `^`, `~` are bitwise on infinite two's-complement integers
//! (`~a = -a-1`); `a << k` is `a * 2^k`; `a >> k` is `floor(a / 2^k)`
//! (arithmetic shift). Comparisons are integer comparisons.
//!
//! # Soundness (never a false accept)
//!
//! Fix a uniform width `W` and signedness; `M = 2^W`; the *window* is
//! `[0, 2^W)` (unsigned) or `[-2^(W-1), 2^(W-1))` (signed). `repr(n)` is the
//! W-bit pattern of an in-window `n`; interpretation is the inverse.
//!
//! * Every variable of the encoded query is either (a) premise-domained —
//!   the recovered premises force its value into the window in every model
//!   of the requires; (b) a wrapping-triple result — the triple plus the
//!   ONE-WRAP interval side-condition on `E` (`interval(E) ⊆ [MIN-M,
//!   MAX+M]`) force `v ∈ window` and `v ≡ E (mod M)`, hence
//!   `repr(v) = enc(E)` whenever `enc(E) ≡ E (mod M)`; or (c) a
//!   goal-`forall` binder whose guard provably confines it to the window
//!   (see below).
//! * CONGRUENCE: for every value node this walker accepts, `enc(e) ≡
//!   true(e) (mod M)` — literals are encoded `mod M`; `+`, `-`, `*`, `neg`
//!   are ring operations mod M; `&`, `|`, `^`, `~` act bitwise on residues
//!   (the low W bits of an infinite two's-complement integer depend only on
//!   its residue mod M); `a << k` with an EXACT non-negative `k` satisfies
//!   `bvshl(enc a, repr k) ≡ a·2^k (mod M)` for every `k ≥ 0` (both sides
//!   vanish mod M once `k ≥ W`). `>>` and `ite` do not preserve congruence
//!   in general and therefore REQUIRE exact operands.
//! * EXACTNESS: `enc(e) = repr(true(e))` whenever `enc(e)` is congruent and
//!   `true(e)` is in the window for every relevant assignment. The walker
//!   certifies the latter with a conservative interval analysis seeded from
//!   the variable windows, narrowed by premise bounds and — scoped — by
//!   implication antecedents / left conjuncts (`A ==> B`, `A && B`: when
//!   `A` is false both encodings agree trivially; when `A` is true the
//!   refinement derived from `A` holds, so `B`'s atoms are exact exactly
//!   where their value matters).
//! * ATOMS: every comparison requires BOTH operands exact; then the
//!   signedness-matching BV comparison agrees with the integer comparison.
//!   The boolean structure (`==>`, `&&`, `||`, `!`, iff/xor, ite) is encoded
//!   operator-for-operator, so the encoded formula evaluates identically to
//!   the source formula on corresponding assignments.
//! * FORALL (positive polarity only): the goal `forall<i> G(i) ==> P(i)` is
//!   encoded by declaring `i` as a FRESH free `BitVec(W)` variable in the
//!   negated goal: UNSAT of `premises ∧ ¬(G ==> P)` with `i` free IS the
//!   proof of the forall over the whole window — a SAT witness would be a
//!   counterexample value of `i`, so no witness means the body holds for
//!   every W-bit `i`. Because the source quantifier ranges over
//!   mathematical `Int`, the walker additionally requires the guard `G` to
//!   syntactically confine `i` to the window (a lower bound `>= window_lo`
//!   and an upper bound `<= window_hi`, both certified by the interval
//!   analysis): for any out-of-window integer `i`, `G(i)` is then false and
//!   the quantified body holds vacuously. Negative/mixed-polarity
//!   quantifiers bail.
//! * HYPOTHESES (requires, scoped `LetAssume` assumptions): asserted only
//!   when they encode EXACTLY; otherwise they are DROPPED, which weakens
//!   the premise side and therefore only STRENGTHENS what UNSAT proves.
//!   Dropping taints the proof: a `sat` verdict is then reported as `None`
//!   (bail) rather than `Failed`, because the model may violate a dropped
//!   premise. `LetObligation` obligations are dropped the same way (they
//!   are proven separately; assuming nothing about them only strengthens
//!   the goal) and likewise taint the `Failed` direction.
//! * Acceptance is UNSAT-only, on an isolated fresh solver with a hard
//!   timeout; every unsupported shape, missing domain, or failed
//!   side-condition bails to the general encoder. A corrupted spec (e.g.
//!   `result@ <= -x@` weakened to `result@ <= -x@ - 1`) is encoded exactly
//!   and reported `Failed` (untainted) or bails — never `Verified`.

use std::collections::HashMap;

use ay_dpll::api::{Logic, Solver, Term};
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

use super::{
    super::{solver_tail::ObligationSliceContext, VerificationResult},
    bitwise_bv_proof::{inline_visible_logic_fns, width_from_unsigned_max},
};

/// Maximum BV width (same cap as tier 1).
const MAX_BV_WIDTH: u32 = 64;

/// Wall-clock budget for the isolated QF_BV solve (same as tier 1).
const BV_SOLVE_TIMEOUT_SECS: u64 = 20;

/// Sentinel bound magnitude used to saturate interval arithmetic. Anything
/// at or beyond this magnitude can never pass a `⊆ window` or one-wrap check
/// (windows are at most 2^64 wide), so saturation is fail-closed.
const INTERVAL_SAT: i128 = i128::MAX / 4;

macro_rules! bvdbg {
    ($($t:tt)*) => {
        if std::env::var("TWP_BVDBG").is_ok() {
            eprintln!($($t)*);
        }
    };
}

/// Attempt to discharge `ensure` as a generalized native QF_BV obligation.
///
/// Returns `Some(Verified)` / `Some(Failed)` on a definitive native-BV
/// result, `None` to fall through to the general encoder.
pub(super) fn try_prove_general_bitwise_obligation(
    ensure: &PureExpr,
    ctx: &ObligationSliceContext<'_>,
) -> Option<VerificationResult> {
    let return_expr = ctx.return_expr?;
    let logic_fns = ctx.logic_fns.unwrap_or(&[]);

    // Cheap pre-gate: this path exists for `#[bitwise_proof]`-style
    // obligations; skip the substitution/inlining work when neither the
    // ensure, the return expression, nor a referenced visible logic-fn body
    // can contribute a bitwise operator.
    if !contains_bitwise_op(ensure)
        && !contains_bitwise_op(return_expr)
        && !logic_fns.iter().any(|f| contains_bitwise_op(f.body()))
    {
        return None;
    }

    // Bind `result := return_expr` and inline visible logic fns, exactly as
    // tier 1 does (`substitute` is binder-aware, so a goal-forall binder is
    // not captured).
    let mut subst = HashMap::new();
    subst.insert("result".to_string(), return_expr.clone());
    let bound = inline_visible_logic_fns(&ensure.substitute(&subst), logic_fns);

    // SCOPE GATE (post-inline): anything still without a bitwise operator
    // is the general encoder's job.
    if !contains_bitwise_op(&bound) {
        return None;
    }
    bvdbg!("=== TIER2 bound: {bound:?}");

    // Recognize wrapping-spec triples among the requires (e.g. the
    // `wrapping_neg` std contract defining `call_3`).
    let triples = recover_wrapping_defs(ctx.requires);

    // ── Domain recovery ────────────────────────────────────────────────
    // Collect the variables that must have a BV domain: the free vars of the
    // bound obligation plus the free vars of every used triple definition.
    // Qualified type constants (`i8::MIN`, ...) parse as `Var` nodes but are
    // literals, not domain variables.
    let is_named_constant =
        |name: &str| crate::encoder::resolve_qualified_int_constant(name).is_some();
    let mut domain_vars: Vec<String> = Vec::new();
    let mut used_triples: Vec<&str> = Vec::new();
    bound.for_each_free_var(|name, _| {
        if is_named_constant(name) {
            return;
        }
        if triples.contains_key(name) {
            if !used_triples.iter().any(|n| n == &name) {
                used_triples.push(name);
            }
        } else if !domain_vars.iter().any(|n| n == name) {
            domain_vars.push(name.to_string());
        }
    });
    // Hold triple processing order stable (map iteration order is arbitrary).
    used_triples.sort_unstable();
    for tname in &used_triples {
        let def = &triples[*tname];
        let mut ok = true;
        def.expr.for_each_free_var(|name, _| {
            if is_named_constant(name) {
                return;
            }
            if triples.contains_key(name) {
                // Triple-in-triple definitions: unsupported, fail closed.
                ok = false;
            } else if !domain_vars.iter().any(|n| n == name) {
                domain_vars.push(name.to_string());
            }
        });
        if !ok {
            return None;
        }
    }

    // Premise bounds for every domain var.
    let mut premise_bounds: HashMap<String, (i128, i128)> = HashMap::new();
    for var in &domain_vars {
        let Some(bounds) = recover_premise_bounds(var, ctx.requires) else {
            bvdbg!("=== TIER2 bail: no premise bounds for {var}");
            return None;
        };
        premise_bounds.insert(var.clone(), bounds);
    }

    // Choose the uniform (width, signedness).
    let Some((width, signed)) = choose_domain(&premise_bounds, &triples, &used_triples) else {
        bvdbg!("=== TIER2 bail: no uniform domain ({premise_bounds:?})");
        return None;
    };
    bvdbg!(
        "=== TIER2 domain: width={width} signed={signed} triples={:?}",
        used_triples
    );
    if width == 0 || width > MAX_BV_WIDTH {
        return None;
    }

    let mut proof = BvProof::new(width, signed);
    // Produce a proof: the UNSAT tail below refuses to report Verified without
    // a complete, fully checked certificate.
    //
    // Deliberately NOT `:check-proofs-strict`. That option is ay's EXTERNAL
    // WIRE screen, not its native-checking switch: it makes ay withhold any
    // UNSAT whose rendered Alethe text contains an unproved wire rule
    // (`decline_trust_bearing_unsat_under_strict_proofs` /
    // `proof_has_known_wire_gap`). A symbolic QF_BV refutation is always
    // anchored on a `TheoryLemmaKind::BvBitBlast` lemma, and the pinned Alethe
    // calculus has no `bv_bitblast` rule, so it always renders as an honest
    // `hole` on the wire — carcara could not check it whatever we do here.
    // Setting the option therefore did not strengthen this lane, it DISABLED
    // it: ay never published the UNSAT, so the acceptance gates below never
    // ran and the whole native path could only ever return `None`.
    //
    // The authority for a Verified verdict comes from those gates instead, and
    // they are unchanged and strictly stronger in the dimension that matters —
    // whether every inference was actually validated:
    //   * `summary.is_fully_verified()` requires ay's own strict proof-IR
    //     validation to have Verified AND zero trust / trust-fallback / hole
    //     steps in the proof IR (a real `hole` is still refused here);
    //   * `record_isolated_strict_unsat_diagnostics` requires
    //     `solve_details_have_complete_unsat_proof`: proof checking active,
    //     checked_steps == total_steps > 0, zero skipped hole steps, zero
    //     trust fallbacks, proof complete, zero checker failures.
    // Measured on the rightmost-bit i8 obligations: 3/3 steps checked,
    // skipped_hole_steps = 0, proof_trust = 0. Nothing is being taken on trust.
    proof.solver.set_produce_proofs(true);

    // Declare premise-domained vars; their sound true-value interval is the
    // tighter of the window and the recovered premise bounds.
    for var in &domain_vars {
        let (lo, hi) = premise_bounds[var];
        if lo < proof.window_lo || hi > proof.window_hi {
            return None;
        }
        let term = proof.solver.bv_var(var, width);
        proof.var_terms.insert(var.clone(), term);
        proof.intervals.insert(var.clone(), (lo, hi));
    }

    // Bind triple vars: `v := enc(E)` with the ONE-WRAP side-condition
    // `interval(E) ⊆ [window_lo - M, window_hi + M]` (see module docs).
    let mut consumed_requires: Vec<usize> = Vec::new();
    for tname in &used_triples {
        let def = &triples[*tname];
        // The triple's own window must be THE window (it defines the wrap
        // arithmetic; a mismatched width/signedness would be a different op).
        if def.min != proof.window_lo || def.max != proof.window_hi {
            return None;
        }
        let (term, info) = proof.value(&def.expr)?;
        let one_wrap_lo = proof.window_lo.checked_sub(proof.modulus)?;
        let one_wrap_hi = proof.window_hi.checked_add(proof.modulus)?;
        if info.lo < one_wrap_lo || info.hi > one_wrap_hi {
            return None;
        }
        proof.var_terms.insert((*tname).to_string(), term);
        proof
            .intervals
            .insert((*tname).to_string(), (proof.window_lo, proof.window_hi));
        consumed_requires.extend_from_slice(&def.consumed);
    }

    // Base refinement from premises: requires hold in every model relevant
    // to this obligation (both for the UNSAT and the SAT direction), so
    // their variable bounds refine intervals globally.
    for require in ctx.requires {
        let require = inline_visible_logic_fns(require, logic_fns);
        proof.refine_from_conjuncts(&require);
    }

    // Assert hypotheses: every non-consumed require that encodes EXACTLY.
    // Anything else is dropped (sound for Verified) and taints Failed.
    // Hypotheses are ASSUMED, not proven — polarity `Neg`, so a forall
    // inside a hypothesis bails to drop+taint instead of being skolemized
    // (skolemizing an assumed forall would weaken it for `Failed`).
    for (index, require) in ctx.requires.iter().enumerate() {
        if consumed_requires.contains(&index) {
            continue;
        }
        let require = inline_visible_logic_fns(require, logic_fns);
        match proof.formula(&require, Polarity::Neg) {
            Some(term) => proof.solver.assert_term(term),
            None => proof.dropped_hypothesis = true,
        }
    }

    // Encode the goal (strict: any unsupported/inexact node bails). Only
    // here do shift-amount markers collect their native-BV range checks
    // (ledger int-shift-full) — requires/assumptions above are
    // assumption-position and collected nothing.
    proof.obligation_mode = true;
    let goal = proof.formula(&bound, Polarity::Pos);
    proof.obligation_mode = false;
    let Some(mut goal) = goal else {
        bvdbg!("=== TIER2 bail: goal encode failed");
        return None;
    };
    // Conjoin the collected shift-amount range checks into the goal: they
    // are PROVED alongside it (UNSAT of the negation ⇒ goal AND every
    // range check hold for all inputs; SAT ⇒ a reachable over-wide shift
    // or a spec violation — Failed either way, the same soundness check as
    // the general encoder's obligation channel).
    for obligation in std::mem::take(&mut proof.shift_range_obligations) {
        goal = proof.solver.and(goal, obligation);
    }
    let negated = proof.solver.not(goal);
    proof.solver.assert_term(negated);
    for hyp in std::mem::take(&mut proof.let_hypotheses) {
        proof.solver.assert_term(hyp);
    }

    let verdict = proof.solver.check_sat_with_details();
    bvdbg!(
        "=== TIER2 verdict: unsat={} sat={} dropped={}",
        verdict.result.is_unsat(),
        verdict.result.is_sat(),
        proof.dropped_hypothesis
    );
    if verdict.result.is_unsat() {
        let Some(summary) = crate::verify::extract_proof_summary(&proof.solver) else {
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
        let replay = proof
            .solver
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
        && !proof.dropped_hypothesis
    {
        // The isolated BV solver validated this SAT model: carry it (with the
        // solve envelope) as the refutation witness so the `Failed` is backed
        // by a validated counterexample rather than withheld.
        let model = proof.solver.model().map(ay_dpll::VerifiedModel::into_inner);
        let replay = proof
            .solver
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
        None
    }
}

// ── Shape predicates ───────────────────────────────────────────────────

fn contains_bitwise_op(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| {
        matches!(
            node,
            PureExpr::BinOp(
                _,
                BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr,
                _
            ) | PureExpr::UnOp(UnOp::BitNot, _)
        )
    })
}

/// Value-selector key: the variable named by `expr` under `@`/`old`
/// wrappers only. For machine integers the view and the entry value ARE the
/// variable's value; `*v`/`^v` are genuinely different values (mut-ref
/// current/final), so they are NOT conflated — fail closed.
fn value_selector_key(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::View(inner) | PureExpr::Old(inner) => value_selector_key(inner),
        _ => None,
    }
}

/// Whether `expr` is a Bool-VALUED expression. Comparisons (`==`, `<`, ...)
/// are always Bool-valued; the `Eq`-on-bools (iff) vs `Eq`-on-ints (atom)
/// decision in [`BvProof::formula`] looks at the OPERANDS' shapes.
fn is_bool_shaped(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Bool(_) | PureExpr::Forall { .. } | PureExpr::Exists { .. } => true,
        PureExpr::UnOp(UnOp::Not, _) => true,
        PureExpr::BinOp(_, op, _) => matches!(
            op,
            BinOp::And
                | BinOp::Or
                | BinOp::Implies
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::Eq
                | BinOp::Ne
        ),
        PureExpr::View(inner) | PureExpr::Old(inner) => is_bool_shaped(inner),
        _ => false,
    }
}

// ── Constant folding (type-constant aware) ─────────────────────────────

/// Exactly constant-fold an integer expression, resolving qualified type
/// constants (`i8::MIN`, `u64::MAX`, ... — also under `@`) by name. Checked
/// i128 arithmetic; returns `None` for anything non-constant. This is the
/// tier-2 sibling of tier 1's `const_int_value` (which never sees named
/// constants: tier-1 premises carry plain literals).
fn fold_const(expr: &PureExpr) -> Option<i128> {
    match expr {
        PureExpr::Int(c) => Some(i128::from(*c)),
        PureExpr::Var(name, _) => {
            let resolved = crate::encoder::resolve_qualified_int_constant(name)?;
            fold_const(&resolved)
        }
        PureExpr::View(inner) | PureExpr::Old(inner) => fold_const(inner),
        PureExpr::UnOp(UnOp::Neg, inner) => fold_const(inner)?.checked_neg(),
        PureExpr::BinOp(l, op, r) => {
            let l = fold_const(l)?;
            let r = fold_const(r)?;
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

// ── Wrapping-spec triple recognition ───────────────────────────────────

/// A recognized wrapping-op result definition: the std wrapping contract
/// triple pins `v ∈ [min, max]` with `v ≡ expr (mod max - min + 1)`.
struct WrappingDef {
    /// The unwrapped defining expression `E` (e.g. `0 - x@`).
    expr: PureExpr,
    /// Folded window bounds from the spec's `MIN`/`MAX` constants.
    min: i128,
    max: i128,
    /// Indices of the three consumed requires.
    consumed: [usize; 3],
}

enum WrappingClause<'a> {
    /// `(E >= MIN && E <= MAX) ==> v@ == E`
    InRange {
        e: &'a PureExpr,
        min: i128,
        max: i128,
    },
    /// `E < MIN ==> v@ == E + M`
    Under { e: &'a PureExpr, min: i128, m: i128 },
    /// `E > MAX ==> v@ == E - M`
    Over { e: &'a PureExpr, max: i128, m: i128 },
}

fn parse_wrapping_clause(require: &PureExpr) -> Option<(String, WrappingClause<'_>)> {
    let PureExpr::BinOp(antecedent, BinOp::Implies, consequent) = require else {
        return None;
    };
    let PureExpr::BinOp(v_sel, BinOp::Eq, rhs) = consequent.as_ref() else {
        return None;
    };
    let var = value_selector_key(v_sel)?.to_string();
    match antecedent.as_ref() {
        // (E >= MIN && E <= MAX)
        PureExpr::BinOp(lo_cmp, BinOp::And, hi_cmp) => {
            let PureExpr::BinOp(e1, BinOp::Ge, min_e) = lo_cmp.as_ref() else {
                return None;
            };
            let PureExpr::BinOp(e2, BinOp::Le, max_e) = hi_cmp.as_ref() else {
                return None;
            };
            if e1 != e2 || e1.as_ref() != rhs.as_ref() {
                return None;
            }
            let min = fold_const(min_e)?;
            let max = fold_const(max_e)?;
            Some((var, WrappingClause::InRange { e: e1, min, max }))
        }
        // E < MIN  /  E > MAX
        PureExpr::BinOp(e, cmp @ (BinOp::Lt | BinOp::Gt), bound_e) => {
            let bound = fold_const(bound_e)?;
            // rhs must be `E + M` (under) or `E - M` (over).
            let PureExpr::BinOp(e_rhs, corr @ (BinOp::Add | BinOp::Sub), m_e) = rhs.as_ref() else {
                return None;
            };
            if e_rhs != e {
                return None;
            }
            let m = fold_const(m_e)?;
            match (cmp, corr) {
                (BinOp::Lt, BinOp::Add) => Some((var, WrappingClause::Under { e, min: bound, m })),
                (BinOp::Gt, BinOp::Sub) => Some((var, WrappingClause::Over { e, max: bound, m })),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Recognize complete wrapping triples among `requires`, keyed by the
/// defined variable. All three clauses must agree on `E`, `MIN`, `MAX`, and
/// `M = MAX - MIN + 1` with `M = 2^W` a power of two.
fn recover_wrapping_defs(requires: &[PureExpr]) -> HashMap<String, WrappingDef> {
    struct Partial<'a> {
        in_range: Option<(usize, &'a PureExpr, i128, i128)>,
        under: Option<(usize, &'a PureExpr, i128, i128)>,
        over: Option<(usize, &'a PureExpr, i128, i128)>,
    }
    let mut partials: HashMap<String, Partial<'_>> = HashMap::new();
    for (index, require) in requires.iter().enumerate() {
        let Some((var, clause)) = parse_wrapping_clause(require) else {
            continue;
        };
        let entry = partials.entry(var).or_insert(Partial {
            in_range: None,
            under: None,
            over: None,
        });
        match clause {
            WrappingClause::InRange { e, min, max } => {
                entry.in_range = Some((index, e, min, max));
            }
            WrappingClause::Under { e, min, m } => entry.under = Some((index, e, min, m)),
            WrappingClause::Over { e, max, m } => entry.over = Some((index, e, max, m)),
        }
    }
    let mut defs = HashMap::new();
    for (var, partial) in partials {
        let (
            Some((i_a, e_a, min, max)),
            Some((i_b, e_b, min_b, m_b)),
            Some((i_c, e_c, max_c, m_c)),
        ) = (partial.in_range, partial.under, partial.over)
        else {
            continue;
        };
        if e_a != e_b || e_a != e_c || min != min_b || max != max_c || m_b != m_c {
            continue;
        }
        let Some(m) = max.checked_sub(min).and_then(|d| d.checked_add(1)) else {
            continue;
        };
        if m != m_b {
            continue;
        }
        // M must be a power of two (2^W): the triple is modular arithmetic.
        let Ok(m_u) = u128::try_from(m) else { continue };
        if m_u == 0 || !m_u.is_power_of_two() {
            continue;
        }
        defs.insert(
            var,
            WrappingDef {
                expr: e_a.clone(),
                min,
                max,
                consumed: [i_a, i_b, i_c],
            },
        );
    }
    defs
}

// ── Domain recovery ────────────────────────────────────────────────────

/// Recover `(lo, hi)` premise bounds for `var` from requires of the form
/// `v@ >= c` / `v@ <= c` (constant-foldable `c`, type constants included).
/// Both a lower and an upper bound must exist.
fn recover_premise_bounds(var: &str, requires: &[PureExpr]) -> Option<(i128, i128)> {
    let mut lo: Option<i128> = None;
    let mut hi: Option<i128> = None;
    for require in requires {
        let PureExpr::BinOp(lhs, op, rhs) = require else {
            continue;
        };
        if value_selector_key(lhs) != Some(var) {
            continue;
        }
        let Some(c) = fold_const(rhs) else { continue };
        match op {
            BinOp::Ge => lo = Some(lo.map_or(c, |v| v.max(c))),
            BinOp::Gt => {
                let c = c.checked_add(1)?;
                lo = Some(lo.map_or(c, |v| v.max(c)));
            }
            BinOp::Le => hi = Some(hi.map_or(c, |v| v.min(c))),
            BinOp::Lt => {
                let c = c.checked_sub(1)?;
                hi = Some(hi.map_or(c, |v| v.min(c)));
            }
            _ => {}
        }
    }
    Some((lo?, hi?))
}

/// Choose the uniform `(width, signed)` domain. Triples pin it exactly
/// (their `MIN`/`MAX` define the wrap arithmetic); otherwise the smallest
/// width whose window covers every premise-bound interval is used.
fn choose_domain(
    premise_bounds: &HashMap<String, (i128, i128)>,
    triples: &HashMap<String, WrappingDef>,
    used_triples: &[&str],
) -> Option<(u32, bool)> {
    if let Some(first) = used_triples.first() {
        let def = &triples[*first];
        let m = def.max.checked_sub(def.min)?.checked_add(1)?;
        let width = width_from_unsigned_max(m.checked_sub(1)?)?;
        let signed = if def.min == 0 {
            false
        } else if def.min == -(m / 2) && def.max == m / 2 - 1 {
            true
        } else {
            return None;
        };
        for tname in used_triples {
            let other = &triples[*tname];
            if other.min != def.min || other.max != def.max {
                return None;
            }
        }
        // Every premise var must fit the pinned window (checked again by the
        // caller against the final window; do it here for early bail).
        let (window_lo, window_hi) = window(width, signed);
        for &(lo, hi) in premise_bounds.values() {
            if lo < window_lo || hi > window_hi {
                return None;
            }
        }
        return Some((width, signed));
    }
    // No triples: smallest width covering all premise intervals.
    let mut need_signed = false;
    let mut min_lo: i128 = 0;
    let mut max_hi: i128 = 0;
    if premise_bounds.is_empty() {
        return None;
    }
    for &(lo, hi) in premise_bounds.values() {
        if lo < 0 {
            need_signed = true;
        }
        min_lo = min_lo.min(lo);
        max_hi = max_hi.max(hi);
    }
    (1..=MAX_BV_WIDTH).find_map(|w| {
        let (lo_w, hi_w) = window(w, need_signed);
        (min_lo >= lo_w && max_hi <= hi_w).then_some((w, need_signed))
    })
}

fn window(width: u32, signed: bool) -> (i128, i128) {
    let m: i128 = 1i128 << width;
    if signed {
        (-(m / 2), m / 2 - 1)
    } else {
        (0, m - 1)
    }
}

// ── The proof context ──────────────────────────────────────────────────

/// Polarity of the sub-formula being encoded. `Forall` skolemization is
/// only sound where the quantifier is proven (positive) in the goal.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Polarity {
    Pos,
    Neg,
    Both,
}

impl Polarity {
    fn flip(self) -> Self {
        match self {
            Polarity::Pos => Polarity::Neg,
            Polarity::Neg => Polarity::Pos,
            Polarity::Both => Polarity::Both,
        }
    }
}

/// Interval + exactness certificate for an encoded value node (see module
/// docs: `lo`/`hi` bound the TRUE mathematical value for every relevant
/// assignment; `exact` certifies `enc = repr(true value)`; a `Some` result
/// always certifies congruence `enc ≡ true value (mod M)`).
#[derive(Clone, Copy)]
struct ValueInfo {
    lo: i128,
    hi: i128,
    exact: bool,
}

struct BvProof {
    width: u32,
    signed: bool,
    modulus: i128,
    window_lo: i128,
    window_hi: i128,
    solver: Solver,
    var_terms: HashMap<String, Term>,
    /// Sound TRUE-value intervals per variable (window at declaration,
    /// narrowed by premise bounds and scoped guard refinements).
    intervals: HashMap<String, (i128, i128)>,
    /// Hypotheses collected from value-position `LetAssume` scopes.
    let_hypotheses: Vec<Term>,
    /// Set when any hypothesis/obligation was dropped: `sat` must then bail
    /// instead of reporting `Failed`.
    dropped_hypothesis: bool,
    /// Counter for fresh skolem variable names.
    fresh_counter: u32,
    /// Native-BV shift-amount range checks collected from
    /// `__trust_wp_shift_amount_in_range_{bits}` markers while encoding the
    /// GOAL (ledger int-shift-full). Conjoined into the goal before
    /// negation, so they are PROVED — mirroring the general encoder's
    /// obligation channel — never assumed.
    shift_range_obligations: Vec<Term>,
    /// True only while the goal formula is being encoded: markers inside
    /// hypotheses (requires, `LetAssume` assumptions) are ASSUMPTION
    /// position and collect no obligation, exactly like the general
    /// encoder's `with_assumption_position` rule.
    obligation_mode: bool,
    /// Depth of interval-analysis peeks (`extract_bounds_from_conjuncts`):
    /// value encodes performed for bound extraction are not real encodings
    /// of an execution path, so markers seen there collect nothing (a peek
    /// runs OUTSIDE the branch guard and would re-introduce the unguarded
    /// collect bug).
    analysis_depth: u32,
    /// Active ITE branch conditions (MIR control flow reconstructed by the
    /// driver): shift-range checks are guarded by them, mirroring the
    /// general encoder's path-condition stack.
    path_guard: Vec<Term>,
}

impl BvProof {
    fn new(width: u32, signed: bool) -> Self {
        let (window_lo, window_hi) = window(width, signed);
        let mut solver = Solver::new(Logic::QfBv);
        solver.set_timeout(Some(std::time::Duration::from_secs(BV_SOLVE_TIMEOUT_SECS)));
        Self {
            width,
            signed,
            modulus: 1i128 << width,
            window_lo,
            window_hi,
            solver,
            var_terms: HashMap::new(),
            intervals: HashMap::new(),
            let_hypotheses: Vec::new(),
            dropped_hypothesis: false,
            fresh_counter: 0,
            shift_range_obligations: Vec::new(),
            obligation_mode: false,
            analysis_depth: 0,
            path_guard: Vec::new(),
        }
    }

    fn in_window(&self, lo: i128, hi: i128) -> bool {
        lo >= self.window_lo && hi <= self.window_hi
    }

    /// Encode a literal (or folded constant) mod M — always congruent;
    /// exact iff in the window.
    fn literal(&mut self, c: i128) -> (Term, ValueInfo) {
        let residue = c.rem_euclid(self.modulus);
        #[allow(clippy::cast_sign_loss)] // residue ∈ [0, 2^64), fits u64
        let term = self.solver.bv_const_u64(residue as u64, self.width);
        let exact = self.in_window(c, c);
        (
            term,
            ValueInfo {
                lo: c,
                hi: c,
                exact,
            },
        )
    }

    // ── Value encoding + analysis ─────────────────────────────────────

    /// Encode a value-typed node; `None` = unsupported (bail). A `Some`
    /// result certifies congruence; `.exact` certifies exactness.
    #[allow(clippy::too_many_lines)] // single exhaustive dispatch, clearer unsplit
    fn value(&mut self, expr: &PureExpr) -> Option<(Term, ValueInfo)> {
        // Constants (including `i8::MIN@`-style named constants) first.
        if let Some(c) = fold_const(expr) {
            return Some(self.literal(c));
        }
        match expr {
            PureExpr::Var(_, _) => {
                let key = value_selector_key(expr)?;
                let term = self.var_terms.get(key).copied()?;
                let (lo, hi) = self.intervals.get(key).copied()?;
                Some((
                    term,
                    ValueInfo {
                        lo,
                        hi,
                        exact: true,
                    },
                ))
            }
            // The view/entry value of a machine integer IS the integer.
            PureExpr::View(inner) | PureExpr::Old(inner) => self.value(inner),
            PureExpr::UnOp(UnOp::Neg, inner) => {
                let (t, i) = self.value(inner)?;
                let term = self.solver.bvneg(t);
                let (lo, hi) = (sat_neg(i.hi), sat_neg(i.lo));
                let exact = self.in_window(lo, hi);
                Some((term, ValueInfo { lo, hi, exact }))
            }
            PureExpr::UnOp(UnOp::BitNot, inner) => {
                // Infinite two's-complement: ~a = -a - 1 (exactly).
                let (t, i) = self.value(inner)?;
                let term = self.solver.bvnot(t);
                let (lo, hi) = (sat_sub(sat_neg(i.hi), 1), sat_sub(sat_neg(i.lo), 1));
                let exact = self.in_window(lo, hi);
                Some((term, ValueInfo { lo, hi, exact }))
            }
            PureExpr::BinOp(l, op, r) => self.value_binop(l, *op, r),
            // Shift-amount-in-range marker (ledger int-shift-full): the
            // driver wraps the amount operand of a machine-int `<<`/`>>`.
            // Value-wise it is the IDENTITY on its single argument; in goal
            // position the range side-condition is recorded as a NATIVE BV
            // check (`bvult`/`bvsge`+`bvslt` against the shifted type's
            // width) and conjoined into the goal — so an over-wide shift
            // still FAILS in this lane, with no Int-sort round-trip and no
            // uninterpreted conversion aux.
            // A machine bit operation at its type (D-242).
            PureExpr::LogicFnCall { name, args }
                if crate::encoder::parse_int_bitop_name(name).is_some() =>
            {
                let (bits, signed) = crate::encoder::parse_int_bitop_name(name)?;
                let [inner] = args.as_slice() else {
                    return None;
                };
                self.machine_bitop_value(inner, bits, signed)
            }
            PureExpr::LogicFnCall { name, args } => {
                let bits = crate::encoder::parse_shift_amount_in_range_name(name)?;
                let [amount] = args.as_slice() else {
                    return None;
                };
                let (term, info) = self.value(amount)?;
                self.record_shift_amount_range_obligation(term, info, bits)?;
                Some((term, info))
            }
            PureExpr::Ite(cond, then_br, else_br) => {
                let cond_term = self.formula(cond, Polarity::Both)?;
                let refinements = self.extract_bounds_from_conjuncts(cond);
                // Branch bodies are encoded under their branch condition so
                // marker range checks stay path-guarded (a not-taken
                // branch's over-wide amount must not fail the goal —
                // mirrors the general encoder's Ite path conditions).
                self.path_guard.push(cond_term);
                let then_result = self.with_refinements(&refinements, |p| p.value(then_br));
                self.path_guard.pop();
                let (t_term, t_info) = then_result?;
                let not_cond = self.solver.not(cond_term);
                self.path_guard.push(not_cond);
                let else_result = self.value(else_br);
                self.path_guard.pop();
                let (e_term, e_info) = else_result?;
                let term = self.solver.ite(cond_term, t_term, e_term);
                let lo = t_info.lo.min(e_info.lo);
                let hi = t_info.hi.max(e_info.hi);
                // An ITE is congruent only through the SELECTED branch, and
                // the encoded condition is exact by construction (`formula`
                // is all-atoms-exact); both branches must be exact for the
                // value to be exact.
                let exact = t_info.exact && e_info.exact && self.in_window(lo, hi);
                Some((term, ValueInfo { lo, hi, exact }))
            }
            PureExpr::LetAssume { assumption, body } => {
                // Scoped call postcondition: sound global hypothesis when it
                // encodes exactly; dropped (tainting `Failed`) otherwise.
                // Assumed, not proven — polarity `Neg` (see the requires
                // loop in `try_prove_general_bitwise_obligation`), and
                // ASSUMPTION position for shift-amount markers: facts
                // re-state already-verified body knowledge, so markers
                // inside them collect no range obligation.
                let saved_mode = self.obligation_mode;
                self.obligation_mode = false;
                let assumption_term = self.formula(assumption, Polarity::Neg);
                self.obligation_mode = saved_mode;
                match assumption_term {
                    Some(t) => self.let_hypotheses.push(t),
                    None => self.dropped_hypothesis = true,
                }
                self.value(body)
            }
            PureExpr::LetObligation { body, .. } => {
                // Obligations are proven separately; dropping one here only
                // strengthens the goal (Verified stays sound) but taints the
                // Failed direction.
                self.dropped_hypothesis = true;
                self.value(body)
            }
            _ => None,
        }
    }

    /// The machine bit operation `inner` AT ITS TYPE (`bits` wide,
    /// `signed`; the `__trust_wp_int_bitop_*` marker, D-242).
    ///
    /// The Rust value is the operation's mathematical value (the walker's
    /// reading of the bare operator) reduced into the type, so it is
    /// congruent to it modulo `2^bits` and therefore modulo `M = 2^W`
    /// whenever `W <= bits`. When the mathematical interval lies in the
    /// type's range nothing is reduced and the bare reading's interval
    /// stands; otherwise the value lies in the type's range (for `!` of an
    /// unsigned operand in `[lo, hi] ⊆ [0, 2^bits)`, in
    /// `[2^bits-1-hi, 2^bits-1-lo]`). Exactness then follows from that
    /// interval and the window as for every congruent node.
    ///
    /// A window WIDER than the type (`W > bits`, e.g. an `i8` beside a
    /// `u32` shift amount) is read by
    /// [`Self::machine_bitop_value_in_wider_window`].
    fn machine_bitop_value(
        &mut self,
        inner: &PureExpr,
        bits: u32,
        signed: bool,
    ) -> Option<(Term, ValueInfo)> {
        // The type's range, clamped inside the saturation sentinel so a
        // saturated bound never reads as contained (and a 128-bit range
        // never overflows).
        let limit = INTERVAL_SAT - 1;
        let (type_lo, type_hi) = if bits >= 124 {
            (if signed { -limit } else { 0 }, limit)
        } else if signed {
            let half = 1i128 << (bits - 1);
            (-half, half - 1)
        } else {
            (0, (1i128 << bits) - 1)
        };
        if self.width > bits {
            return self.machine_bitop_value_in_wider_window(inner, signed, type_lo, type_hi);
        }
        let (term, info) = match inner {
            PureExpr::BinOp(l, op, r)
                if matches!(
                    op,
                    BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr
                ) =>
            {
                self.value_binop(l, *op, r)?
            }
            PureExpr::UnOp(UnOp::BitNot, operand) => {
                let (t, i) = self.value(operand)?;
                let term = self.solver.bvnot(t);
                let (lo, hi) = if !signed && i.lo >= 0 && i.hi <= type_hi && bits < 124 {
                    (type_hi - i.hi, type_hi - i.lo)
                } else {
                    (sat_sub(sat_neg(i.hi), 1), sat_sub(sat_neg(i.lo), 1))
                };
                let exact = self.in_window(lo, hi);
                (term, ValueInfo { lo, hi, exact })
            }
            _ => return None,
        };
        if info.lo >= type_lo && info.hi <= type_hi {
            return Some((term, info));
        }
        let (lo, hi) = if bits >= 124 {
            (-INTERVAL_SAT, INTERVAL_SAT)
        } else {
            (type_lo, type_hi)
        };
        let exact = self.in_window(lo, hi);
        Some((term, ValueInfo { lo, hi, exact }))
    }

    /// [`Self::machine_bitop_value`] in a window wider than the type
    /// (`W > bits`), whose bits above the type are not reduced. An operation
    /// reads there only where its Rust value is exactly what the window
    /// holds: `&`, `|`, `^` and `>>` of values of the type never leave it
    /// and a signed `!a` is `-a - 1`, each the bare (infinite
    /// two's-complement) reading; a `<<` only when its mathematical interval
    /// lies in the type's range (it then wraps nowhere); an unsigned `!a` as
    /// the exact `(2^bits - 1) - a` of an exact operand of the type.
    fn machine_bitop_value_in_wider_window(
        &mut self,
        inner: &PureExpr,
        signed: bool,
        type_lo: i128,
        type_hi: i128,
    ) -> Option<(Term, ValueInfo)> {
        match inner {
            PureExpr::BinOp(
                l,
                op @ (BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shr),
                r,
            ) => self.value_binop(l, *op, r),
            PureExpr::BinOp(l, BinOp::Shl, r) => {
                let (term, info) = self.value_binop(l, BinOp::Shl, r)?;
                (info.lo >= type_lo && info.hi <= type_hi).then_some((term, info))
            }
            PureExpr::UnOp(UnOp::BitNot, _) if signed => self.value(inner),
            PureExpr::UnOp(UnOp::BitNot, operand) => {
                let (t, i) = self.value(operand)?;
                if !i.exact || i.lo < 0 || i.hi > type_hi || !self.in_window(0, type_hi) {
                    return None;
                }
                let (mask, _) = self.literal(type_hi);
                let term = self.solver.bvsub(mask, t);
                let (lo, hi) = (type_hi - i.hi, type_hi - i.lo);
                let exact = self.in_window(lo, hi);
                Some((term, ValueInfo { lo, hi, exact }))
            }
            _ => None,
        }
    }

    fn value_binop(&mut self, l: &PureExpr, op: BinOp, r: &PureExpr) -> Option<(Term, ValueInfo)> {
        let (lt, li) = self.value(l)?;
        let (rt, ri) = self.value(r)?;
        let (term, lo, hi, extra_exact) = match op {
            BinOp::Add => (
                self.solver.bvadd(lt, rt),
                sat_add(li.lo, ri.lo),
                sat_add(li.hi, ri.hi),
                true,
            ),
            BinOp::Sub => {
                let (mut lo, mut hi) = (sat_sub(li.lo, ri.hi), sat_sub(li.hi, ri.lo));
                // Interval arithmetic forgets that both operands read the
                // same value: the SWAR step `x - ((x >> 1) & 0x55)` gets
                // `[-0x55, x.hi]`, which is inexact, so the next `>>` bails.
                // When `r` is `l` narrowed only by right shifts and
                // non-negative masks and `l >= 0`, `0 <= r <= l` in every
                // valuation, so `l - r` lies in `[0, l.hi]`.
                if li.lo >= 0 && narrowed_from(r, l) {
                    lo = lo.max(0);
                    hi = hi.min(li.hi);
                }
                (self.solver.bvsub(lt, rt), lo, hi, true)
            }
            BinOp::Mul => {
                let corners = [
                    sat_mul(li.lo, ri.lo),
                    sat_mul(li.lo, ri.hi),
                    sat_mul(li.hi, ri.lo),
                    sat_mul(li.hi, ri.hi),
                ];
                let lo = corners.iter().copied().min()?;
                let hi = corners.iter().copied().max()?;
                (self.solver.bvmul(lt, rt), lo, hi, true)
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
                let term = match op {
                    BinOp::BitAnd => self.solver.bvand(lt, rt),
                    BinOp::BitOr => self.solver.bvor(lt, rt),
                    _ => self.solver.bvxor(lt, rt),
                };
                let (lo, hi) = if li.lo >= 0 && ri.lo >= 0 {
                    // Non-negative operands: AND cannot exceed either;
                    // OR/XOR cannot exceed the all-ones cover of the wider.
                    match op {
                        BinOp::BitAnd => (0, li.hi.min(ri.hi)),
                        _ => (0, all_ones_cover(li.hi.max(ri.hi))),
                    }
                } else if self.in_window(li.lo, li.hi) && self.in_window(ri.lo, ri.hi) {
                    // Bitwise ops on two W-window values stay in the
                    // W-window (bitwise on W-bit sign-extended patterns).
                    (self.window_lo, self.window_hi)
                } else {
                    return None;
                };
                (term, lo, hi, true)
            }
            BinOp::Shl => {
                // Congruent for any EXACT non-negative shift amount.
                if !ri.exact || ri.lo < 0 {
                    return None;
                }
                let term = self.solver.bvshl(lt, rt);
                let lo = if li.lo < 0 {
                    sat_shl(li.lo, ri.hi)
                } else {
                    sat_shl(li.lo, ri.lo)
                };
                let hi = if li.hi > 0 {
                    sat_shl(li.hi, ri.hi)
                } else {
                    sat_shl(li.hi, ri.lo)
                };
                (term, lo, hi, true)
            }
            BinOp::Shr => {
                // floor(a / 2^k): requires BOTH operands exact (no
                // congruence through >>). Result lies between 0 and a.
                if !li.exact || !ri.exact || ri.lo < 0 {
                    return None;
                }
                let term = if self.signed {
                    self.solver.bvashr(lt, rt)
                } else {
                    self.solver.bvlshr(lt, rt)
                };
                (term, li.lo.min(0), li.hi.max(0), true)
            }
            _ => return None,
        };
        if !extra_exact {
            return None;
        }
        let exact = self.in_window(lo, hi);
        Some((term, ValueInfo { lo, hi, exact }))
    }

    // ── Formula encoding ──────────────────────────────────────────────

    /// Encode a boolean-structured node; every comparison atom must be
    /// EXACT; `None` = unsupported (bail).
    fn formula(&mut self, expr: &PureExpr, polarity: Polarity) -> Option<Term> {
        match expr {
            PureExpr::Bool(b) => Some(self.solver.bool_const(*b)),
            PureExpr::View(inner) | PureExpr::Old(inner) => self.formula(inner, polarity),
            PureExpr::UnOp(UnOp::Not, inner) => {
                let t = self.formula(inner, polarity.flip())?;
                Some(self.solver.not(t))
            }
            PureExpr::LetAssume { assumption, body } => {
                // Formula-position LetAssume is scoped: `assumption => body`.
                // Assumption position for shift-amount markers (see the
                // value-position arm).
                let saved_mode = self.obligation_mode;
                self.obligation_mode = false;
                let a = self.formula(assumption, polarity.flip());
                self.obligation_mode = saved_mode;
                let a = a?;
                let refinements = self.extract_bounds_from_conjuncts(assumption);
                let b = self.with_refinements(&refinements, |p| p.formula(body, polarity))?;
                Some(self.solver.implies(a, b))
            }
            PureExpr::BinOp(l, op, r) => match op {
                BinOp::And | BinOp::Or => {
                    let lt = self.formula(l, polarity)?;
                    // `A && B` / value-agreement: when A is false both
                    // encodings agree regardless of B; when A is true the
                    // refinement from A holds — so B may be encoded under
                    // A's bounds. (For `||` no refinement is derived.)
                    let rt = if matches!(op, BinOp::And) {
                        let refinements = self.extract_bounds_from_conjuncts(l);
                        self.with_refinements(&refinements, |p| p.formula(r, polarity))?
                    } else {
                        self.formula(r, polarity)?
                    };
                    Some(if matches!(op, BinOp::And) {
                        self.solver.and(lt, rt)
                    } else {
                        self.solver.or(lt, rt)
                    })
                }
                BinOp::Implies => {
                    let lt = self.formula(l, polarity.flip())?;
                    let refinements = self.extract_bounds_from_conjuncts(l);
                    let rt = self.with_refinements(&refinements, |p| p.formula(r, polarity))?;
                    Some(self.solver.implies(lt, rt))
                }
                BinOp::Eq | BinOp::Ne if is_bool_shaped(l) || is_bool_shaped(r) => {
                    // iff / xor: subformulas occur in BOTH polarities.
                    let lt = self.formula(l, Polarity::Both)?;
                    let rt = self.formula(r, Polarity::Both)?;
                    Some(if matches!(op, BinOp::Eq) {
                        self.solver.iff(lt, rt)
                    } else {
                        self.solver.xor(lt, rt)
                    })
                }
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    self.atom(l, *op, r)
                }
                _ => None,
            },
            PureExpr::Forall {
                var,
                var_sort,
                body,
                ..
            } => {
                // Positive polarity only: UNSAT of the negated goal with the
                // binder as a FREE BitVec(W) var proves the forall over the
                // window; the guard-confinement check below extends that to
                // the full Int range (see module docs).
                if polarity != Polarity::Pos {
                    return None;
                }
                if !matches!(var_sort, None | Some(trust_wp_core::formula::ExprSort::Int)) {
                    return None;
                }
                self.forall_pos(var, body)
            }
            _ => None,
        }
    }

    fn forall_pos(&mut self, var: &str, body: &PureExpr) -> Option<Term> {
        // The body must confine the binder to the window through its guard:
        // `guard ==> consequent` where guard yields BOTH a lower bound
        // >= window_lo and an upper bound <= window_hi for `var`.
        let PureExpr::BinOp(guard, BinOp::Implies, _) = body else {
            return None;
        };
        // Hide any SHADOWED outer variable of the same name during the
        // confinement extraction: inside the body, every occurrence of the
        // name is the BINDER, so a bound expression that mentions it (e.g.
        // the tautological `i < i + 1`) must fail to evaluate — deriving its
        // "interval" from a shadowed outer variable would fabricate a bogus
        // window confinement (false-accept vector).
        let shadowed_term = self.var_terms.remove(var);
        let shadowed_interval = self.intervals.remove(var);
        let guard_bounds = self.extract_bounds_from_conjuncts(guard);
        restore(&mut self.var_terms, var, shadowed_term);
        restore(&mut self.intervals, var, shadowed_interval);
        let mut var_lo: Option<i128> = None;
        let mut var_hi: Option<i128> = None;
        for (name, lo, hi) in &guard_bounds {
            if name == var {
                if let Some(lo) = lo {
                    var_lo = Some(var_lo.map_or(*lo, |v: i128| v.max(*lo)));
                }
                if let Some(hi) = hi {
                    var_hi = Some(var_hi.map_or(*hi, |v: i128| v.min(*hi)));
                }
            }
        }
        let (var_lo, var_hi) = (var_lo?, var_hi?);
        if var_lo < self.window_lo || var_hi > self.window_hi {
            return None;
        }

        // Declare the binder as a fresh BV var; its base interval for atom
        // exactness is the WINDOW (the BV quantification ranges over all
        // patterns); the guard refinement narrows it inside the consequent
        // via the normal Implies handling.
        self.fresh_counter += 1;
        let fresh_name = format!("{var}!bvq{}", self.fresh_counter);
        let term = self.solver.bv_var(&fresh_name, self.width);
        let saved_term = self.var_terms.insert(var.to_string(), term);
        let saved_interval = self
            .intervals
            .insert(var.to_string(), (self.window_lo, self.window_hi));
        let encoded = self.formula(body, Polarity::Pos);
        restore(&mut self.var_terms, var, saved_term);
        restore(&mut self.intervals, var, saved_interval);
        encoded
    }

    fn atom(&mut self, l: &PureExpr, op: BinOp, r: &PureExpr) -> Option<Term> {
        let (lt, li) = self.value(l)?;
        let (rt, ri) = self.value(r)?;
        if !li.exact || !ri.exact {
            return None;
        }
        Some(match op {
            BinOp::Eq => self.solver.eq(lt, rt),
            BinOp::Ne => {
                let eq = self.solver.eq(lt, rt);
                self.solver.not(eq)
            }
            BinOp::Lt if self.signed => self.solver.bvslt(lt, rt),
            BinOp::Le if self.signed => self.solver.bvsle(lt, rt),
            BinOp::Gt if self.signed => self.solver.bvsgt(lt, rt),
            BinOp::Ge if self.signed => self.solver.bvsge(lt, rt),
            BinOp::Lt => self.solver.bvult(lt, rt),
            BinOp::Le => self.solver.bvule(lt, rt),
            BinOp::Gt => self.solver.bvugt(lt, rt),
            BinOp::Ge => self.solver.bvuge(lt, rt),
            _ => return None,
        })
    }

    // ── Guard refinement ──────────────────────────────────────────────

    /// Extract sound variable bounds from the conjuncts of `guard`:
    /// `v <cmp> e` / `e <cmp> v` where `e`'s TRUE-value interval is known.
    /// These hold whenever the guard holds (semantic reasoning on true
    /// values — encodability of `e` is irrelevant here, but `value` is used
    /// to obtain its sound interval).
    fn extract_bounds_from_conjuncts(
        &mut self,
        guard: &PureExpr,
    ) -> Vec<(String, Option<i128>, Option<i128>)> {
        let mut out = Vec::new();
        // Interval peeks value-encode sub-expressions OUTSIDE any execution
        // path; markers seen here must not collect range obligations.
        self.analysis_depth += 1;
        self.extract_bounds_impl(guard, &mut out);
        self.analysis_depth -= 1;
        out
    }

    fn extract_bounds_impl(
        &mut self,
        expr: &PureExpr,
        out: &mut Vec<(String, Option<i128>, Option<i128>)>,
    ) {
        match expr {
            PureExpr::BinOp(l, BinOp::And, r) => {
                self.extract_bounds_impl(l, out);
                self.extract_bounds_impl(r, out);
            }
            PureExpr::BinOp(
                l,
                op @ (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq),
                r,
            ) => {
                // v <cmp> e
                if let Some(var) = value_selector_key(l) {
                    if let Some(info) = self.peek_interval(r) {
                        let (lo, hi) = match op {
                            BinOp::Lt => (None, info.hi.checked_sub(1)),
                            BinOp::Le => (None, Some(info.hi)),
                            BinOp::Gt => (info.lo.checked_add(1), None),
                            BinOp::Ge => (Some(info.lo), None),
                            _ => (Some(info.lo), Some(info.hi)),
                        };
                        out.push((var.to_string(), lo, hi));
                    }
                }
                // e <cmp> v (mirrored)
                if let Some(var) = value_selector_key(r) {
                    if let Some(info) = self.peek_interval(l) {
                        let (lo, hi) = match op {
                            BinOp::Lt => (info.lo.checked_add(1), None),
                            BinOp::Le => (Some(info.lo), None),
                            BinOp::Gt => (None, info.hi.checked_sub(1)),
                            BinOp::Ge => (None, Some(info.hi)),
                            _ => (Some(info.lo), Some(info.hi)),
                        };
                        out.push((var.to_string(), lo, hi));
                    }
                }
            }
            _ => {}
        }
    }

    /// Record the native-BV range check for a shift-amount marker
    /// (ledger int-shift-full): `0 <= amount < bits` over the W-window
    /// encoding of the amount, guarded by the active ITE branch conditions.
    ///
    /// - Goal position only (`obligation_mode`, not inside an interval
    ///   peek): hypothesis markers are assumption-position and collect
    ///   nothing.
    /// - Statically discharged when the amount's SOUND true-value interval
    ///   already lies inside `[0, bits)` — the check is a tautology.
    /// - Otherwise the amount encoding must be EXACT (`info.exact`) so the
    ///   BV comparison agrees with the mathematical range check; an inexact
    ///   amount bails the lane (`None`), falling back to the general
    ///   encoder — fail closed, the obligation is still checked there.
    /// - Per-side emission mirrors [`Self::atom`]'s signedness dispatch:
    ///   unsigned window ⇒ `bvult amount, bits`; signed window ⇒
    ///   `bvsge amount, 0` and/or `bvslt amount, bits`. A side whose bound
    ///   already follows from the interval is omitted; for an exact
    ///   in-window value, `info.hi < bits` in particular covers every
    ///   `bits` too large to represent in the window, so an emitted upper
    ///   bound always has a representable `bits` literal.
    fn record_shift_amount_range_obligation(
        &mut self,
        term: Term,
        info: ValueInfo,
        bits: u32,
    ) -> Option<()> {
        if !self.obligation_mode || self.analysis_depth > 0 {
            return Some(());
        }
        let bits_i = i128::from(bits);
        if info.lo >= 0 && info.hi < bits_i {
            return Some(());
        }
        if !info.exact {
            return None;
        }
        let mut check: Option<Term> = None;
        if info.lo < 0 {
            let (zero, _) = self.literal(0);
            let ge_zero = if self.signed {
                self.solver.bvsge(term, zero)
            } else {
                self.solver.bvuge(term, zero)
            };
            check = Some(ge_zero);
        }
        if info.hi >= bits_i {
            let (bits_term, bits_info) = self.literal(bits_i);
            if !bits_info.exact {
                // Unrepresentable width bound with a possibly-violating
                // amount: bail, the general encoder owns this obligation.
                return None;
            }
            let lt_bits = if self.signed {
                self.solver.bvslt(term, bits_term)
            } else {
                self.solver.bvult(term, bits_term)
            };
            check = Some(match check {
                Some(prev) => self.solver.and(prev, lt_bits),
                None => lt_bits,
            });
        }
        let Some(mut check) = check else {
            return Some(());
        };
        for &guard in self.path_guard.iter().rev() {
            check = self.solver.implies(guard, check);
        }
        self.shift_range_obligations.push(check);
        Some(())
    }

    /// Sound TRUE-value interval of `expr` under the current environment
    /// (side effect: may create unasserted solver terms — harmless).
    fn peek_interval(&mut self, expr: &PureExpr) -> Option<ValueInfo> {
        if let Some(c) = fold_const(expr) {
            return Some(ValueInfo {
                lo: c,
                hi: c,
                exact: false,
            });
        }
        self.value(expr).map(|(_, info)| info)
    }

    /// Run `f` with `refinements` intersected into the interval env, then
    /// restore. Bounds are also clamped to the window: a refinement can
    /// only NARROW a variable whose base range is its window.
    fn with_refinements<T>(
        &mut self,
        refinements: &[(String, Option<i128>, Option<i128>)],
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let mut saved: Vec<(String, Option<(i128, i128)>)> = Vec::new();
        for (var, lo, hi) in refinements {
            let Some(&(cur_lo, cur_hi)) = self.intervals.get(var) else {
                continue;
            };
            let new_lo = lo.map_or(cur_lo, |l| l.max(cur_lo));
            let new_hi = hi.map_or(cur_hi, |h| h.min(cur_hi));
            saved.push((var.clone(), Some((cur_lo, cur_hi))));
            self.intervals.insert(var.clone(), (new_lo, new_hi));
        }
        let result = f(self);
        for (var, old) in saved.into_iter().rev() {
            restore(&mut self.intervals, &var, old);
        }
        result
    }

    /// Permanently refine intervals from a top-level premise (requires hold
    /// in every model relevant to this obligation).
    fn refine_from_conjuncts(&mut self, premise: &PureExpr) {
        let refinements = self.extract_bounds_from_conjuncts(premise);
        for (var, lo, hi) in refinements {
            let Some(&(cur_lo, cur_hi)) = self.intervals.get(&var) else {
                continue;
            };
            let new_lo = lo.map_or(cur_lo, |l| l.max(cur_lo));
            let new_hi = hi.map_or(cur_hi, |h| h.min(cur_hi));
            self.intervals.insert(var, (new_lo, new_hi));
        }
    }
}

fn restore<V>(map: &mut HashMap<String, V>, key: &str, old: Option<V>) {
    match old {
        Some(v) => {
            map.insert(key.to_string(), v);
        }
        None => {
            map.remove(key);
        }
    }
}

/// Whether `narrowed` is `base` itself, or `base` passed through right
/// shifts by non-negative constants and ANDs with non-negative constant
/// masks. For a non-negative `a`, `0 <= a >> k <= a` and `0 <= a & m <= a`
/// (`k, m >= 0`), so by induction `0 <= narrowed <= base` whenever
/// `base >= 0`. `@` and `old` are the value itself here (see `value`); any
/// other node answers `false`.
fn narrowed_from(narrowed: &PureExpr, base: &PureExpr) -> bool {
    fn strip(expr: &PureExpr) -> &PureExpr {
        match expr {
            PureExpr::View(inner) | PureExpr::Old(inner) => strip(inner),
            other => other,
        }
    }
    let non_negative_const = |e: &PureExpr| fold_const(e).is_some_and(|c| c >= 0);
    let narrowed = strip(narrowed);
    if narrowed == strip(base) {
        return true;
    }
    match narrowed {
        PureExpr::BinOp(a, BinOp::Shr, k) if non_negative_const(k) => narrowed_from(a, base),
        PureExpr::BinOp(a, BinOp::BitAnd, m) if non_negative_const(m) => narrowed_from(a, base),
        PureExpr::BinOp(m, BinOp::BitAnd, a) if non_negative_const(m) => narrowed_from(a, base),
        // A `>>` or `&` at its machine type (D-242) of a non-negative value
        // is the bare operation: neither leaves the type.
        PureExpr::LogicFnCall { name, args }
            if crate::encoder::parse_int_bitop_name(name).is_some() =>
        {
            matches!(
                args.as_slice(),
                [inner @ PureExpr::BinOp(_, BinOp::Shr | BinOp::BitAnd, _)]
                    if narrowed_from(inner, base)
            )
        }
        _ => false,
    }
}

// ── Saturating interval arithmetic ─────────────────────────────────────
//
// Saturation is fail-closed: saturated bounds are far outside any window or
// one-wrap check (`INTERVAL_SAT` >> 2^64), so an overflowing bound can never
// certify exactness — it can only cause a bail.

fn clamp(v: i128) -> i128 {
    v.clamp(-INTERVAL_SAT, INTERVAL_SAT)
}

fn sat_add(a: i128, b: i128) -> i128 {
    clamp(a.saturating_add(b))
}

fn sat_sub(a: i128, b: i128) -> i128 {
    clamp(a.saturating_sub(b))
}

fn sat_mul(a: i128, b: i128) -> i128 {
    clamp(a.saturating_mul(b))
}

fn sat_neg(a: i128) -> i128 {
    clamp(a.saturating_neg())
}

fn sat_shl(a: i128, k: i128) -> i128 {
    if a == 0 {
        return 0;
    }
    if k <= 0 {
        return clamp(a);
    }
    if k >= 100 {
        // Saturate: `checked_shl` only checks the shift COUNT, not value
        // overflow, so large shifts must be short-circuited here.
        return if a < 0 { -INTERVAL_SAT } else { INTERVAL_SAT };
    }
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // 0 < k < 100
    clamp(a.saturating_mul(1i128 << (k as u32)))
}

/// Smallest `2^k - 1` covering a non-negative `value` (shared shape with
/// tier 1's helper; duplicated to keep tier 1 untouched). Saturates to
/// `INTERVAL_SAT` instead of stopping below `value`: the earlier loop
/// stopped at `2^101 - 1`, an UNDER-approximation of a larger `value`.
fn all_ones_cover(value: i128) -> i128 {
    if value <= 0 {
        return 0;
    }
    let bits = 128 - value.leading_zeros();
    1i128
        .checked_shl(bits)
        .and_then(|m| m.checked_sub(1))
        .filter(|cover| *cover >= value)
        .map_or(INTERVAL_SAT, clamp)
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, sync::Arc};

    use trust_wp_core::{
        formula::{BinOp, PureExpr, UnOp},
        logic::{LogicFnDef, LogicMode},
    };

    use super::{
        super::super::{solver_tail::ObligationSliceContext, VerificationResult},
        choose_domain, recover_premise_bounds, recover_wrapping_defs,
        try_prove_general_bitwise_obligation,
    };

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }
    fn int(v: i64) -> PureExpr {
        PureExpr::Int(v)
    }
    fn view(e: PureExpr) -> PureExpr {
        PureExpr::View(Arc::new(e))
    }
    fn bin(l: PureExpr, op: BinOp, r: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(l), op, Arc::new(r))
    }
    fn neg(e: PureExpr) -> PureExpr {
        PureExpr::UnOp(UnOp::Neg, Arc::new(e))
    }
    fn ite(c: PureExpr, t: PureExpr, e: PureExpr) -> PureExpr {
        PureExpr::Ite(Arc::new(c), Arc::new(t), Arc::new(e))
    }
    fn i8_min() -> PureExpr {
        view(var("i8::MIN"))
    }
    fn i8_max() -> PureExpr {
        view(var("i8::MAX"))
    }

    /// The rightmostbit i8 premises exactly as the driver emits them:
    /// signed range preconditions for `x` plus the `wrapping_neg` std-spec
    /// triple defining `call_3`.
    fn rmb8_requires() -> Vec<PureExpr> {
        let e = || bin(int(0), BinOp::Sub, view(var("x")));
        let m = || bin(bin(i8_max(), BinOp::Sub, i8_min()), BinOp::Add, int(1));
        vec![
            bin(view(var("x")), BinOp::Ge, int(-128)),
            bin(view(var("x")), BinOp::Le, int(127)),
            bin(
                bin(
                    bin(e(), BinOp::Ge, i8_min()),
                    BinOp::And,
                    bin(e(), BinOp::Le, i8_max()),
                ),
                BinOp::Implies,
                bin(view(var("call_3")), BinOp::Eq, e()),
            ),
            bin(
                bin(e(), BinOp::Lt, i8_min()),
                BinOp::Implies,
                bin(view(var("call_3")), BinOp::Eq, bin(e(), BinOp::Add, m())),
            ),
            bin(
                bin(e(), BinOp::Gt, i8_max()),
                BinOp::Implies,
                bin(view(var("call_3")), BinOp::Eq, bin(e(), BinOp::Sub, m())),
            ),
        ]
    }

    /// `x & call_3` — the rightmost_bit_8 body.
    fn rmb8_return_expr() -> PureExpr {
        bin(var("x"), BinOp::BitAnd, var("call_3"))
    }

    fn prove(
        ensure: &PureExpr,
        requires: &[PureExpr],
        return_expr: &PureExpr,
        logic_fns: Option<&[LogicFnDef]>,
    ) -> Option<VerificationResult> {
        let ctx = ObligationSliceContext {
            all_ensures: &[],
            requires,
            logic_fns,
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
        try_prove_general_bitwise_obligation(ensure, &ctx)
    }

    #[test]
    fn signed_width_recovery_from_paired_premises() {
        let requires = rmb8_requires();
        // Signed premise pair -128 <= x@ <= 127 recovers the exact bounds.
        assert_eq!(
            recover_premise_bounds("x", &requires),
            Some((-128, 127)),
            "signed premise pair must recover"
        );
        // The wrapping triple pins the domain to signed W=8.
        let triples = recover_wrapping_defs(&requires);
        assert!(triples.contains_key("call_3"), "wrapping triple recognized");
        assert_eq!(triples["call_3"].min, -128);
        assert_eq!(triples["call_3"].max, 127);
        let mut premise_bounds = HashMap::new();
        premise_bounds.insert("x".to_string(), (-128i128, 127i128));
        assert_eq!(
            choose_domain(&premise_bounds, &triples, &["call_3"]),
            Some((8, true)),
            "domain pinned to signed width 8"
        );
        // Without triples: smallest covering signed width.
        assert_eq!(
            choose_domain(&premise_bounds, &HashMap::new(), &[]),
            Some((8, true))
        );
    }

    #[test]
    fn signed_implication_with_negated_bound_verifies() {
        // ensures #2: x <= 0 && x > i8::MIN ==> 0 <= result && result@ <= -x@
        // (`-x@` needs the guard refinement: unrefined, -x@ reaches 128 which
        // is outside the signed 8-bit window.)
        let ensure = bin(
            bin(
                bin(var("x"), BinOp::Le, int(0)),
                BinOp::And,
                bin(var("x"), BinOp::Gt, i8_min()),
            ),
            BinOp::Implies,
            bin(
                bin(int(0), BinOp::Le, var("result")),
                BinOp::And,
                bin(view(var("result")), BinOp::Le, neg(view(var("x")))),
            ),
        );
        let result = prove(&ensure, &rmb8_requires(), &rmb8_return_expr(), None);
        assert!(
            matches!(result, Some(VerificationResult::Verified(_))),
            "signed implication ensure should verify natively, got {result:?}"
        );
    }

    #[test]
    fn iff_on_min_sentinel_verifies() {
        // ensures #3: (x == i8::MIN) == (result == i8::MIN)
        let ensure = bin(
            bin(var("x"), BinOp::Eq, var("i8::MIN")),
            BinOp::Eq,
            bin(var("result"), BinOp::Eq, var("i8::MIN")),
        );
        let result = prove(&ensure, &rmb8_requires(), &rmb8_return_expr(), None);
        assert!(
            matches!(result, Some(VerificationResult::Verified(_))),
            "iff ensure should verify natively, got {result:?}"
        );
    }

    #[test]
    fn bounded_forall_verifies_and_unbounded_bails() {
        // ensures #4: forall<i> 0 <= i && i < result ==> i & x == 0
        let body = bin(
            bin(
                bin(int(0), BinOp::Le, var("i")),
                BinOp::And,
                bin(var("i"), BinOp::Lt, var("result")),
            ),
            BinOp::Implies,
            bin(bin(var("i"), BinOp::BitAnd, var("x")), BinOp::Eq, int(0)),
        );
        let ensure = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![],
        };
        let result = prove(&ensure, &rmb8_requires(), &rmb8_return_expr(), None);
        assert!(
            matches!(result, Some(VerificationResult::Verified(_))),
            "guard-bounded forall should verify natively, got {result:?}"
        );

        // UNGUARDED forall: the binder ranges over all of Int; the window
        // proof does not cover it — MUST bail (soundness gate).
        let unbounded = PureExpr::Forall {
            var: "i".to_string(),
            var_sort: None,
            body: Arc::new(bin(
                bin(var("i"), BinOp::BitAnd, var("x")),
                BinOp::Eq,
                int(0),
            )),
            triggers: vec![],
        };
        let result = prove(&unbounded, &rmb8_requires(), &rmb8_return_expr(), None);
        assert!(
            result.is_none(),
            "window-unconfined forall must bail, got {result:?}"
        );
    }

    #[test]
    fn shadowing_forall_binder_cannot_borrow_outer_interval() {
        // The binder shadows the tracked param `x`; its guard upper bound
        // `x < x + 1` is a TAUTOLOGY over the binder (unbounded). Reading
        // the shadowed param's interval would fabricate a window
        // confinement — this must BAIL (soundness gate).
        let body = bin(
            bin(
                bin(int(0), BinOp::Le, var("x")),
                BinOp::And,
                bin(var("x"), BinOp::Lt, bin(var("x"), BinOp::Add, int(1))),
            ),
            BinOp::Implies,
            bin(
                bin(var("x"), BinOp::BitAnd, var("call_3")),
                BinOp::Ge,
                i8_min(),
            ),
        );
        let ensure = PureExpr::Forall {
            var: "x".to_string(),
            var_sort: None,
            body: Arc::new(body),
            triggers: vec![],
        };
        let result = prove(&ensure, &rmb8_requires(), &rmb8_return_expr(), None);
        assert!(
            result.is_none(),
            "shadowing binder with tautological guard must bail, got {result:?}"
        );
    }

    #[test]
    fn corrupted_signed_ensure_is_never_verified() {
        // The cardinal no-false-accept check: weaken ensures #2's bound to
        // `result@ <= -x@ - 1` — false at e.g. x = -1 (result = 1, -x-1 = 0).
        // The fast path must report Failed (exact encoding, no dropped
        // hypotheses) or bail — NEVER Verified.
        let corrupted = bin(
            bin(
                bin(var("x"), BinOp::Le, int(0)),
                BinOp::And,
                bin(var("x"), BinOp::Gt, i8_min()),
            ),
            BinOp::Implies,
            bin(
                bin(int(0), BinOp::Le, var("result")),
                BinOp::And,
                bin(
                    view(var("result")),
                    BinOp::Le,
                    bin(neg(view(var("x"))), BinOp::Sub, int(1)),
                ),
            ),
        );
        let result = prove(&corrupted, &rmb8_requires(), &rmb8_return_expr(), None);
        assert!(
            !matches!(result, Some(VerificationResult::Verified(_))),
            "corrupted signed ensure must never be Verified, got {result:?}"
        );
        assert!(
            matches!(result, Some(VerificationResult::Failed(_))),
            "corrupted signed ensure is exactly encoded: expected Failed, got {result:?}"
        );
    }

    /// count8_log over i8 (per-bit ITE sum, masks including `i8::MIN`).
    fn count8_log_def() -> LogicFnDef {
        let bit = |mask: PureExpr| {
            ite(
                bin(bin(var("n"), BinOp::BitAnd, mask), BinOp::Eq, int(0)),
                int(0),
                int(1),
            )
        };
        let mut sum = bit(int(1));
        for mask in [2i64, 4, 8, 0x10, 0x20, 0x40] {
            sum = bin(sum, BinOp::Add, bit(int(mask)));
        }
        sum = bin(sum, BinOp::Add, bit(var("i8::MIN")));
        LogicFnDef::new(
            "count8_log".to_string(),
            "count8_log".to_string(),
            vec!["n".to_string()],
            sum,
        )
        .with_mode(LogicMode::Open)
    }

    #[test]
    fn count8_log_of_rightmost_bit_is_one() {
        // ensures #5: x != 0 ==> count8_log(result) == 1
        let ensure = bin(
            bin(var("x"), BinOp::Ne, int(0)),
            BinOp::Implies,
            bin(
                PureExpr::LogicFnCall {
                    name: "count8_log".to_string(),
                    args: vec![var("result")],
                },
                BinOp::Eq,
                int(1),
            ),
        );
        let fns = [count8_log_def()];
        let result = prove(&ensure, &rmb8_requires(), &rmb8_return_expr(), Some(&fns));
        assert!(
            matches!(result, Some(VerificationResult::Verified(_))),
            "count8_log ensure should verify natively, got {result:?}"
        );

        // Corrupted spec: count8_log(result) == 2 — false at x = 1.
        let corrupted = bin(
            bin(var("x"), BinOp::Ne, int(0)),
            BinOp::Implies,
            bin(
                PureExpr::LogicFnCall {
                    name: "count8_log".to_string(),
                    args: vec![var("result")],
                },
                BinOp::Eq,
                int(2),
            ),
        );
        let result = prove(
            &corrupted,
            &rmb8_requires(),
            &rmb8_return_expr(),
            Some(&fns),
        );
        assert!(
            !matches!(result, Some(VerificationResult::Verified(_))),
            "corrupted count ensure must never be Verified, got {result:?}"
        );
    }

    /// Driver marker for a `bits`-wide shifted operand (ledger
    /// int-shift-full).
    fn in_range_marker(bits: u32, amount: PureExpr) -> PureExpr {
        PureExpr::LogicFnCall {
            name: format!("__trust_wp_shift_amount_in_range_{bits}"),
            args: vec![amount],
        }
    }

    /// Unsigned 8-bit premises for `x` and `n`.
    fn u8_requires(n_hi: i64) -> Vec<PureExpr> {
        vec![
            bin(view(var("x")), BinOp::Ge, int(0)),
            bin(view(var("x")), BinOp::Le, int(255)),
            bin(view(var("n")), BinOp::Ge, int(0)),
            bin(view(var("n")), BinOp::Le, int(n_hi)),
        ]
    }

    /// GREEN: a premise-bounded amount (`n <= 7`) statically discharges the
    /// marker's range check — the lane verifies natively, exactly as it did
    /// before the marker existed.
    #[test]
    fn marker_with_premise_bounded_amount_verifies() {
        let ensure = bin(view(var("result")), BinOp::Le, view(var("x")));
        let return_expr = bin(var("x"), BinOp::Shr, in_range_marker(8, var("n")));
        let result = prove(&ensure, &u8_requires(7), &return_expr, None);
        assert!(
            matches!(result, Some(VerificationResult::Verified(_))),
            "marker with in-range premise-bounded amount must verify natively, got {result:?}"
        );
    }

    /// RED (BV mode): the marker's range check is PROVED, never assumed —
    /// with `n` only bounded into the u8 window (not below the width), the
    /// goal itself holds (`x >> n <= x`) but the conjoined native-BV range
    /// obligation is refutable at `n == 8`, so the lane must report Failed.
    /// A marker treated as a pure identity would falsely verify this.
    #[test]
    fn marker_with_over_wide_amount_fails_natively() {
        let ensure = bin(view(var("result")), BinOp::Le, view(var("x")));
        let return_expr = bin(var("x"), BinOp::Shr, in_range_marker(8, var("n")));
        let result = prove(&ensure, &u8_requires(255), &return_expr, None);
        assert!(
            matches!(result, Some(VerificationResult::Failed(_))),
            "an over-wide amount must fail the native-BV range obligation, got {result:?}"
        );
    }

    /// ASSUMPTION position: a marker inside a REQUIRES fact re-states
    /// already-verified body knowledge and must NOT collect a range
    /// obligation — the unrelated goal still verifies even though `n` may
    /// exceed the width.
    #[test]
    fn marker_in_requires_fact_collects_no_obligation() {
        let mut requires = u8_requires(255);
        requires.push(bin(
            bin(var("x"), BinOp::Shr, in_range_marker(8, var("n"))),
            BinOp::Le,
            view(var("x")),
        ));
        let ensure = bin(view(var("result")), BinOp::Le, int(7));
        let return_expr = bin(var("x"), BinOp::BitAnd, int(7));
        let result = prove(&ensure, &requires, &return_expr, None);
        assert!(
            matches!(result, Some(VerificationResult::Verified(_))),
            "a requires-fact marker must not fail the goal at n >= 8, got {result:?}"
        );
    }

    /// Path-guarded in the native lane too (the bits.rs `empty` shape): a
    /// shift reachable only under a branch condition carries that condition
    /// on its range check. The premise `y == 0 ==> n <= 7` makes the check
    /// provable ONLY under the branch guard — an unguarded `bvult(n, 8)`
    /// would be refuted at `y != 0, n == 8`, a state where the shift never
    /// executes.
    #[test]
    fn marker_in_ite_branch_is_branch_guarded() {
        let mut requires = u8_requires(255);
        requires.push(bin(view(var("y")), BinOp::Ge, int(0)));
        requires.push(bin(view(var("y")), BinOp::Le, int(255)));
        requires.push(bin(
            bin(view(var("y")), BinOp::Eq, int(0)),
            BinOp::Implies,
            bin(view(var("n")), BinOp::Le, int(7)),
        ));
        let ensure = bin(view(var("result")), BinOp::Le, view(var("x")));
        let return_expr = ite(
            bin(view(var("y")), BinOp::Eq, int(0)),
            bin(var("x"), BinOp::Shr, in_range_marker(8, var("n"))),
            int(0),
        );
        let result = prove(&ensure, &requires, &return_expr, None);
        assert!(
            matches!(result, Some(VerificationResult::Verified(_))),
            "a branch-guarded marker must not fail outside its branch, got {result:?}"
        );
    }

    /// The u8 SWAR popcount body over `n`, as the driver lowers `count8`.
    fn count8_swar_u8() -> PureExpr {
        let n = || var("n");
        let x1 = bin(
            n(),
            BinOp::Sub,
            bin(bin(n(), BinOp::Shr, int(1)), BinOp::BitAnd, int(0x55)),
        );
        let x2 = bin(
            bin(x1.clone(), BinOp::BitAnd, int(0x33)),
            BinOp::Add,
            bin(bin(x1, BinOp::Shr, int(2)), BinOp::BitAnd, int(0x33)),
        );
        bin(
            bin(x2.clone(), BinOp::Add, bin(x2, BinOp::Shr, int(4))),
            BinOp::BitAnd,
            int(0x0F),
        )
    }

    /// Unsigned count8_log over u8: one ITE per bit.
    fn count8_log_u8_def() -> LogicFnDef {
        let bit = |mask: i64| {
            ite(
                bin(bin(var("n"), BinOp::BitAnd, int(mask)), BinOp::Eq, int(0)),
                int(0),
                int(1),
            )
        };
        let mut sum = bit(1);
        for mask in [2i64, 4, 8, 0x10, 0x20, 0x40, 0x80] {
            sum = bin(sum, BinOp::Add, bit(mask));
        }
        LogicFnDef::new(
            "count8_log".to_string(),
            "count8_log".to_string(),
            vec!["n".to_string()],
            sum,
        )
        .with_mode(LogicMode::Open)
    }

    /// The u8 range premises of `n` alone: a premise over a variable the
    /// goal never mentions does not encode, is dropped, and would taint the
    /// `Failed` direction.
    fn n_u8_requires() -> Vec<PureExpr> {
        vec![
            bin(view(var("n")), BinOp::Ge, int(0)),
            bin(view(var("n")), BinOp::Le, int(255)),
        ]
    }

    fn count8_log_call() -> PureExpr {
        PureExpr::LogicFnCall {
            name: "count8_log".to_string(),
            args: vec![var("n")],
        }
    }

    /// `x - ((x >> 1) & 0x55)` subtracts a value the same `x` bounds, so it
    /// stays in the u8 window and the SWAR chain after it is exact: both
    /// popcount ensures verify natively. Before the narrowing rule the first
    /// `>>` on that difference bailed and the goal went to the mixed Int/BV
    /// encoder, which timed out.
    #[test]
    fn swar_popcount_u8_verifies() {
        let fns = [count8_log_u8_def()];
        let requires = n_u8_requires();
        let equal = bin(view(var("result")), BinOp::Eq, count8_log_call());
        let result = prove(&equal, &requires, &count8_swar_u8(), Some(&fns));
        assert!(
            matches!(result, Some(VerificationResult::Verified(_))),
            "result@ == count8_log(n) should verify natively, got {result:?}"
        );
        let bound = bin(view(var("result")), BinOp::Le, int(8));
        let result = prove(&bound, &requires, &count8_swar_u8(), Some(&fns));
        assert!(
            matches!(result, Some(VerificationResult::Verified(_))),
            "result@ <= 8 should verify natively, got {result:?}"
        );
    }

    /// The false twins: an off-by-one count and a bound one too small are
    /// exactly encoded and refuted, never verified.
    #[test]
    fn swar_popcount_u8_false_specs_are_refuted() {
        let fns = [count8_log_u8_def()];
        let requires = n_u8_requires();
        let off_by_one = bin(
            view(var("result")),
            BinOp::Eq,
            bin(count8_log_call(), BinOp::Add, int(1)),
        );
        let result = prove(&off_by_one, &requires, &count8_swar_u8(), Some(&fns));
        assert!(
            matches!(result, Some(VerificationResult::Failed(_))),
            "result@ == count8_log(n) + 1 must be refuted, got {result:?}"
        );
        let too_small = bin(view(var("result")), BinOp::Le, int(7));
        let result = prove(&too_small, &requires, &count8_swar_u8(), Some(&fns));
        assert!(
            matches!(result, Some(VerificationResult::Failed(_))),
            "result@ <= 7 is false at n == 255 and must be refuted, got {result:?}"
        );
    }

    /// The narrowing rule reads the SAME operand on both sides. With a
    /// different variable the difference can go negative (`x = 0, n = 2`),
    /// its interval stays inexact, and a claim that it is non-negative must
    /// not verify.
    #[test]
    fn narrowing_needs_the_same_operand() {
        let return_expr = bin(
            var("x"),
            BinOp::Sub,
            bin(bin(var("n"), BinOp::Shr, int(1)), BinOp::BitAnd, int(0x55)),
        );
        let ensure = bin(view(var("result")), BinOp::Ge, int(0));
        let result = prove(&ensure, &u8_requires(255), &return_expr, None);
        assert!(
            !matches!(result, Some(VerificationResult::Verified(_))),
            "x - ((n >> 1) & 0x55) >= 0 is false at x = 0, n = 2, got {result:?}"
        );
        // An OR can raise the value above its operand: `x | 1 > x` at even
        // `x`, so `x - (x | 1)` is negative there and is not narrowed.
        let or_return = bin(var("x"), BinOp::Sub, bin(var("x"), BinOp::BitOr, int(1)));
        let result = prove(&ensure, &u8_requires(255), &or_return, None);
        assert!(
            !matches!(result, Some(VerificationResult::Verified(_))),
            "x - (x | 1) >= 0 is false at x = 0, got {result:?}"
        );
    }

    fn machine_bitop(signed: bool, bits: u32, inner: PureExpr) -> PureExpr {
        PureExpr::LogicFnCall {
            name: trust_wp_core::formula::internal::machine_bitop::name(signed, bits),
            args: vec![inner],
        }
    }

    fn is_verified(result: &Option<VerificationResult>) -> bool {
        matches!(result, Some(VerificationResult::Verified(_)))
    }

    /// The rightmost_bit_8 body as the driver now lowers it (D-242): the
    /// signed `&` at its type. Every proof the bare body had still goes
    /// through at the i8 window.
    #[test]
    fn rightmost_bit_at_its_type_still_verifies() {
        let marked = machine_bitop(true, 8, rmb8_return_expr());
        let ensure = bin(
            bin(var("x"), BinOp::Eq, var("i8::MIN")),
            BinOp::Eq,
            bin(var("result"), BinOp::Eq, var("i8::MIN")),
        );
        assert!(is_verified(&prove(
            &ensure,
            &rmb8_requires(),
            &marked,
            None
        )));
        let ensure = bin(
            bin(var("x"), BinOp::Ge, int(0)),
            BinOp::Implies,
            bin(
                bin(int(0), BinOp::Le, var("result")),
                BinOp::And,
                bin(var("result"), BinOp::Le, var("x")),
            ),
        );
        assert!(is_verified(&prove(
            &ensure,
            &rmb8_requires(),
            &marked,
            None
        )));
    }

    fn u8_u16_requires() -> Vec<PureExpr> {
        vec![
            bin(view(var("x")), BinOp::Ge, int(0)),
            bin(view(var("x")), BinOp::Le, int(255)),
            bin(view(var("y")), BinOp::Ge, int(0)),
            bin(view(var("y")), BinOp::Le, int(65535)),
        ]
    }

    /// Regression (r35): with a `u8` and a `u16` operand the window is 16
    /// bits, and the bare `x << 4` read `x * 16` there although Rust drops
    /// the bits above the `u8` (`16u8 << 4 == 0`): `result@ == x@ * 16` over
    /// `((x << 4) as u16) | (y & 0)` was proved. At its type a `<<` that may
    /// wrap at the `u8` bails in a wider window, and a `!x` there is
    /// `255 - x`, not `65535 - x`.
    #[test]
    fn machine_op_narrower_than_the_window_bails() {
        let shl = machine_bitop(false, 8, bin(var("x"), BinOp::Shl, int(4)));
        let ret = bin(shl, BinOp::BitOr, bin(var("y"), BinOp::BitAnd, int(0)));
        let ensure = bin(
            view(var("result")),
            BinOp::Eq,
            bin(view(var("x")), BinOp::Mul, int(16)),
        );
        let result = prove(&ensure, &u8_u16_requires(), &ret, None);
        assert!(!is_verified(&result), "16u8 << 4 is 0: {result:?}");
        let not = machine_bitop(false, 8, PureExpr::UnOp(UnOp::BitNot, Arc::new(var("x"))));
        let ret = bin(not, BinOp::BitOr, bin(var("y"), BinOp::BitAnd, int(0)));
        let ensure = bin(
            view(var("result")),
            BinOp::Eq,
            bin(int(65535), BinOp::Sub, view(var("x"))),
        );
        let result = prove(&ensure, &u8_u16_requires(), &ret, None);
        assert!(!is_verified(&result), "!0u8 is 255: {result:?}");
    }

    /// An `i8` `>>` beside a `u16` operand (a 17-bit signed window) never
    /// reduces, so it reads as the bare arithmetic shift there: the true
    /// `x >= 0 ==> x >> 1 <= x` verifies and the false `x >> 1 >= 0` does
    /// not (`-128 >> 1 == -64`). A signed `<<` in that window, which wraps at
    /// the `i8`, still bails.
    #[test]
    fn machine_shr_reads_in_a_window_wider_than_its_type() {
        let requires = vec![
            bin(view(var("x")), BinOp::Ge, int(-128)),
            bin(view(var("x")), BinOp::Le, int(127)),
            bin(view(var("y")), BinOp::Ge, int(0)),
            bin(view(var("y")), BinOp::Le, int(65535)),
        ];
        let y_and_0 = bin(view(var("y")), BinOp::BitAnd, int(0));
        let shr = machine_bitop(true, 8, bin(var("x"), BinOp::Shr, int(1)));
        let shrinks = bin(
            bin(view(var("x")), BinOp::Ge, int(0)),
            BinOp::Implies,
            bin(
                view(var("result")),
                BinOp::Le,
                bin(view(var("x")), BinOp::Add, y_and_0.clone()),
            ),
        );
        assert!(is_verified(&prove(&shrinks, &requires, &shr, None)));
        let nonneg = bin(view(var("result")), BinOp::Ge, y_and_0.clone());
        assert!(!is_verified(&prove(&nonneg, &requires, &shr, None)));
        let shl = machine_bitop(true, 8, bin(var("x"), BinOp::Shl, int(1)));
        let doubles = bin(
            view(var("result")),
            BinOp::Eq,
            bin(bin(view(var("x")), BinOp::Mul, int(2)), BinOp::Add, y_and_0),
        );
        assert!(!is_verified(&prove(&doubles, &requires, &shl, None)));
    }

    /// In a window wider than a `u8` (a `u16` operand beside it), a `<<`
    /// that cannot wrap at the `u8` (`x <= 15`) is the exact product, and a
    /// `!` is the exact `255 - x`: both true contracts verify, and the
    /// `!` read as `65535 - x` does not.
    #[test]
    fn machine_op_that_does_not_wrap_reads_in_a_wider_window() {
        let mut requires = u8_u16_requires();
        requires.push(bin(view(var("x")), BinOp::Le, int(15)));
        let y_and_0 = bin(var("y"), BinOp::BitAnd, int(0));
        let shl = machine_bitop(false, 8, bin(var("x"), BinOp::Shl, int(4)));
        let ret = bin(shl, BinOp::BitOr, y_and_0.clone());
        let times16 = bin(
            view(var("result")),
            BinOp::Eq,
            bin(view(var("x")), BinOp::Mul, int(16)),
        );
        assert!(is_verified(&prove(&times16, &requires, &ret, None)));
        let not = machine_bitop(false, 8, PureExpr::UnOp(UnOp::BitNot, Arc::new(var("x"))));
        let ret = bin(not, BinOp::BitOr, y_and_0);
        let complement = bin(
            view(var("result")),
            BinOp::Eq,
            bin(int(255), BinOp::Sub, view(var("x"))),
        );
        assert!(is_verified(&prove(
            &complement,
            &u8_u16_requires(),
            &ret,
            None
        )));
        let wide = bin(
            view(var("result")),
            BinOp::Eq,
            bin(int(65535), BinOp::Sub, view(var("x"))),
        );
        assert!(!is_verified(&prove(&wide, &u8_u16_requires(), &ret, None)));
    }

    /// At the type's own window a `u8` `<<` and `!` are exact: the true
    /// `x << 4 <= 240` and `!x == 255 - x` verify, `x << 4 == x * 16` does not.
    #[test]
    fn machine_op_at_its_own_window_is_exact() {
        let requires = vec![
            bin(view(var("x")), BinOp::Ge, int(0)),
            bin(view(var("x")), BinOp::Le, int(255)),
        ];
        let shl = machine_bitop(false, 8, bin(var("x"), BinOp::Shl, int(4)));
        let le240 = bin(view(var("result")), BinOp::Le, int(240));
        assert!(is_verified(&prove(&le240, &requires, &shl, None)));
        let times16 = bin(
            view(var("result")),
            BinOp::Eq,
            bin(view(var("x")), BinOp::Mul, int(16)),
        );
        assert!(!is_verified(&prove(&times16, &requires, &shl, None)));
        let not = machine_bitop(false, 8, PureExpr::UnOp(UnOp::BitNot, Arc::new(var("x"))));
        let complement = bin(
            view(var("result")),
            BinOp::Eq,
            bin(int(255), BinOp::Sub, view(var("x"))),
        );
        assert!(is_verified(&prove(&complement, &requires, &not, None)));
    }

    #[test]
    fn mixed_domain_bails() {
        // A var premised into an UNSIGNED window alongside the signed triple:
        // no uniform domain — must bail, not guess.
        let mut requires = rmb8_requires();
        requires.push(bin(view(var("y")), BinOp::Ge, int(0)));
        requires.push(bin(view(var("y")), BinOp::Le, int(255)));
        let ensure = bin(
            bin(var("y"), BinOp::BitAnd, var("call_3")),
            BinOp::Ge,
            int(-128),
        );
        let result = prove(&ensure, &requires, &rmb8_return_expr(), None);
        assert!(
            result.is_none(),
            "y's [0,255] premise does not fit the signed 8-bit window pinned \
             by the triple: must bail, got {result:?}"
        );
    }
}
