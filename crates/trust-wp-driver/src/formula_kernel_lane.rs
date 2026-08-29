// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The REAL kernel lane (feature `clean-kernel`, design §9 P(−1) applied to the
//! product): translate the driver's ACTUAL obligation formulas — the
//! `trust_wp_core::formula::PureExpr` clauses handed to `dispatch_smt_verification`
//! at the discharge layer — into `clean_kernel` goals and grade them through the
//! frozen interface (`trust_spec_iface`).
//!
//! # Contract with the rest of the driver
//!
//! - **Non-invasive.** This lane is observation ONLY. It is invoked from the
//!   discharge/report site in `per_contract.rs` after the solver verdict is
//!   already fixed, and it never reads back into that verdict — it only ADDS
//!   information (a per-obligation [`trust_spec_iface::ClauseStatus`] in the
//!   debug log plus a per-function summary line).
//! - **Fail closed.** The translator is total via `Option`: it covers ONLY the
//!   fragment it can render faithfully into the kernel's Nat/Bool model (see
//!   below). Anything else returns `None` — the obligation stays solver-only and
//!   NO kernel claim of any kind is made for it (interface invariant I5).
//! - **No self-grading.** The lane never decides truth itself: it produces
//!   candidate `LaneVerdict`s and every verdict goes through
//!   `trust_spec_iface::grade_verdict` (invariant I1) — the meter kernel-checks
//!   the term against the goal and decides Certified/Trusted/Rejected.
//!
//! # The covered fragment (everything else → `None`)
//!
//! Boolean clauses over:
//!
//! - non-negative integer literals, rendered as kernel `Nat` literals
//!   (the driver's `Int` model restricted to ℕ — negative literals decline);
//! - contract variables of UNSIGNED integer MIR type (`u8`..`u64`, `usize` at
//!   the target pointer width; see [`kernel_vars_for_contract`]) — parameters
//!   and `result` — rendered as de-Bruijn-bound kernel `Nat` variables under a
//!   `∀ (v : Nat)` prefix. The rendering is faithful because every Int-model
//!   valuation of an unsigned variable lies in `[0, 2^width−1] ⊆ ℕ` and the
//!   admitted operators agree with the kernel's Nat semantics pointwise there;
//!   proving the universal Nat closure is therefore ≥ the driver obligation.
//!   SIGNED variables (and everything else) still decline: a Nat rendering of a
//!   possibly-negative value is unfaithful — a later brick;
//! - the view operator `v@` on such a variable (`View` is the identity on the
//!   integer model — anything else under `View` declines);
//! - `+` and `*` (`Nat.add` / `Nat.mul`: faithful on the non-negative fragment,
//!   which is closed under both);
//! - `/` and `%` (Euclidean or truncated flavor) ONLY when the divisor is a
//!   positive integer literal (`Nat.div` / `Nat.mod`: on a non-negative dividend
//!   and positive divisor the Euclidean and truncated semantics coincide with
//!   the kernel's; division by zero is left to the solver's model — decline);
//! - integer comparisons `==  !=  <  <=  >  >=` (`Nat.beq` / `Nat.blt` /
//!   `Nat.ble` with argument swaps for `>` / `>=`);
//! - boolean literals, boolean equality (`Bool.beq`), and the connectives
//!   `&&  ||  !  ==>` (`Bool.and` / `Bool.or` / `Bool.not`; `p ==> q` as
//!   `!p || q`) — the kernel side of each connective exists and computes.
//!
//! Deliberately OUTSIDE the fragment (fail closed, with the reason): signed /
//! `u128` / non-integer variables (no faithful Nat rendering), `-` (kernel
//! `Nat.sub` is monus, not integer subtraction), negation, floats,
//! bitwise/shift operators, quantifiers, `old`/`^`/`*`-operators, `@` on
//! non-variables, method calls, matches, `if`.
//!
//! # What a grade MEANS here (hypotheses are best-effort, conclusions exact)
//!
//! The rendered obligation is
//!
//! ```text
//! ∀ (v₁ … vₙ : Nat), (vᵢ ≤ 2^widthᵢ − 1) → ⟦requires⟧ → ⟦ensures-clause⟧
//! ```
//!
//! built as a [`trust_spec_iface::UOb`]: when every hypothesis is closed they
//! ride `UOb::hypotheses` and I3's `elaborated_goal` folds them; when variables
//! are involved the hypothesis arrows must live UNDER the `∀` prefix (I3 folds
//! OUTSIDE any binder), so the same chain is baked into `UOb::goal` directly.
//!
//! - The per-variable `2^width` bounds and the contract's requires clauses are
//!   HYPOTHESES. They translate through the SAME fragment translator; any
//!   requires clause that does not translate is DROPPED with a debug note.
//!   Dropping a hypothesis makes the goal STRONGER, so a `Certified` grade of
//!   the stronger goal is still sound for the contract obligation.
//! - The ensures CONCLUSION must translate exactly — otherwise the whole
//!   obligation declines (`None`, no kernel claim).
//! - `Rejected` is surfaced ONLY for a variable-free clause of a contract with
//!   ZERO requires clauses: there the refl candidate's failure computes the
//!   clause itself false, which refutes the hypothesis-free obligation. With
//!   requires present (or variables involved) a failed candidate says nothing
//!   about the obligation (the requires may be unsatisfiable — the contract
//!   holds vacuously; an auto term may simply be ill-typed), so the lane
//!   degrades to no-kernel-claim: a `Decline` graded to `Pending` (I5).
//!
//! # The race (every leg graded through `grade_verdict`, I1)
//!
//! 1. **refl** — ground conclusions: `Eq.refl Bool ⟦clause⟧` against the
//!    hypothesis-free goal; the kernel decides by computation.
//! 2. **clean-auto, bare** — conclusions with variables: `auto_prove` (5s) on
//!    `∀ vars, ⟦clause⟧ = true` with ALL hypotheses dropped (sound, above) —
//!    the induction lane (`Nat.rec`) closes universal Nat tautologies here.
//! 3. **clean-auto, full** — `auto_prove` (5s) on the complete rendering with
//!    bounds + kept requires.
//!
//! `clean-auto` is built with `default-features = false` (no ay/SMT backend):
//! the induction/superposition lanes are pure clean-kernel term assembly, and
//! every produced term is INDEPENDENTLY re-checked by the meter — an ill-typed
//! candidate grades `Rejected` and is degraded to no-claim, never surfaced.
//! `ProgramTier::TrustedReflection` remains the safe default (the reflection
//! fragment condition is not proven at this call site), so no status this lane
//! produces ever licenses UB elision.

use std::{collections::BTreeSet, time::Duration};

use clean_auto::AutomationEngine;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use tracing::debug;
use trust_spec_iface::{
    clean_kernel::{
        expr::{BinderInfo, ExprKind},
        Environment, Expr, Level, Name,
    },
    grade_verdict, ClauseStatus, LaneVerdict, LogicTier, ObKind, ProgramTier, UOb,
};
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

/// A contract variable the lane can render: a parameter (or `result`) of
/// integer MIR type, with its resolved bit width (`usize`/`isize` already
/// resolved to the target pointer width; always ≤ 64). `signed` selects the
/// kernel model: unsigned vars are `Nat` (implicitly `≥ 0`, upper-bounded),
/// signed vars are `Int` (two-sided bounds `-2^(bits-1) ≤ x ≤ 2^(bits-1)-1`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct KernelVar {
    pub(crate) name: String,
    pub(crate) bits: u32,
    pub(crate) signed: bool,
}

/// Per-obligation translation context: the contract's renderable variables and
/// its hypothesis pool (the effective requires clauses at the discharge site).
pub(crate) struct ObligationCtx<'a> {
    pub(crate) vars: &'a [KernelVar],
    pub(crate) requires: &'a [PureExpr],
}

/// The variable scope for one clause rendering. `vars` are the ∀-bound
/// variables, OUTERMOST binder first; `offset` is the number of extra binders
/// (hypothesis arrows are Pi binders too) between the ∀ prefix and the subterm
/// being rendered — a variable at position `p` renders as
/// `BVar(len − 1 − p + offset)`.
struct Scope<'a> {
    vars: &'a [KernelVar],
    offset: u32,
    /// Whether this goal's variables are modeled as `Int` (signed) rather than
    /// `Nat` (unsigned). A goal is homogeneous — all vars signed or all
    /// unsigned (mixed goals are declined, see `build_goal`) — so this one flag
    /// selects the integer vocabulary (`Int.beq`/`Int.ble`/`Int.blt`/`Int.add`
    /// vs the `Nat.*` family) for the whole rendering.
    signed: bool,
}

impl Scope<'_> {
    fn var(&self, name: &str) -> Option<Expr> {
        let p = self.vars.iter().position(|v| v.name == name)?;
        let base = u32::try_from(self.vars.len() - 1 - p).ok()?;
        Some(Expr::bvar(base + self.offset))
    }
}

/// `Bool`, the kernel type of the rendered clause.
fn bool_ty() -> Expr {
    Expr::const_(Name::from_string("Bool"), vec![])
}

/// `Nat`, the kernel type of every bound contract variable.
fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// Apply a prelude constant (universe-monomorphic) to arguments.
fn capp(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(name), vec![]), args)
}

/// `2^bits − 1` as a kernel Nat literal (the unsigned max for the width).
fn unsigned_max_lit(bits: u32) -> Expr {
    if bits >= 64 {
        Expr::nat_lit(u64::MAX)
    } else {
        Expr::nat_lit((1u64 << bits) - 1)
    }
}

/// Render a clause as a Bool-VALUED kernel term `⟦clause⟧` under `scope`.
/// `None` ⇒ outside the covered fragment (fail closed).
fn bool_term(e: &PureExpr, scope: &Scope<'_>) -> Option<Expr> {
    match e {
        PureExpr::Bool(true) => Some(Expr::const_(Name::from_string("Bool.true"), vec![])),
        PureExpr::Bool(false) => Some(Expr::const_(Name::from_string("Bool.false"), vec![])),
        // The driver's `UnOp::Not` is boolean negation (`BitNot` is the
        // separate integer complement — outside the fragment).
        PureExpr::UnOp(UnOp::Not, inner) => Some(capp("Bool.not", [bool_term(inner, scope)?])),
        PureExpr::BinOp(l, op, r) => match op {
            BinOp::And => Some(capp(
                "Bool.and",
                [bool_term(l, scope)?, bool_term(r, scope)?],
            )),
            BinOp::Or => Some(capp(
                "Bool.or",
                [bool_term(l, scope)?, bool_term(r, scope)?],
            )),
            // p ==> q  ≡  !p || q (boolean implication).
            BinOp::Implies => Some(capp(
                "Bool.or",
                [
                    capp("Bool.not", [bool_term(l, scope)?]),
                    bool_term(r, scope)?,
                ],
            )),
            BinOp::Eq => eq_term(l, r, scope),
            BinOp::Ne => Some(capp("Bool.not", [eq_term(l, r, scope)?])),
            BinOp::Lt => lt_term(l, r, scope),
            BinOp::Le => le_term(l, r, scope),
            // a > b ⟺ b < a and a >= b ⟺ b <= a: strict/weak total-order swaps.
            BinOp::Gt => lt_term(r, l, scope),
            BinOp::Ge => le_term(r, l, scope),
            _ => None,
        },
        _ => None,
    }
}

/// Sort-dispatched equality: `Nat.beq` when both sides render as Nat values,
/// `Bool.beq` when both render as Bool values. The two renderers cover disjoint
/// constructors (variables are Nat-only: the env admits only unsigned integer
/// vars), so a term's sort is unambiguous; mixed or unrenderable operands
/// decline.
fn eq_term(l: &PureExpr, r: &PureExpr, scope: &Scope<'_>) -> Option<Expr> {
    if scope.signed {
        if let (Some(li), Some(ri)) = (int_term(l, scope), int_term(r, scope)) {
            return Some(capp("Int.beq", [li, ri]));
        }
    } else if let (Some(ln), Some(rn)) = (nat_term(l, scope), nat_term(r, scope)) {
        return Some(capp("Nat.beq", [ln, rn]));
    }
    match (bool_term(l, scope), bool_term(r, scope)) {
        (Some(lb), Some(rb)) => Some(capp("Bool.beq", [lb, rb])),
        _ => None,
    }
}

/// Render `l ≤ r` as a Bool term in the scope's integer model. Signed uses
/// `Int.ble`; unsigned `Nat.ble`.
fn le_term(l: &PureExpr, r: &PureExpr, scope: &Scope<'_>) -> Option<Expr> {
    if scope.signed {
        Some(capp("Int.ble", [int_term(l, scope)?, int_term(r, scope)?]))
    } else {
        Some(capp("Nat.ble", [nat_term(l, scope)?, nat_term(r, scope)?]))
    }
}

/// Render `l < r` as a Bool term. Unsigned uses `Nat.blt`; signed uses
/// `l < r ⟺ ¬(r ≤ l)` (`Bool.not (Int.ble r l)`) since `Int.blt` is not a
/// declared prelude constant (only a native reducer), so this keeps the
/// rendered term kernel-well-formed.
fn lt_term(l: &PureExpr, r: &PureExpr, scope: &Scope<'_>) -> Option<Expr> {
    if scope.signed {
        Some(capp("Bool.not", [le_term(r, l, scope)?]))
    } else {
        Some(capp("Nat.blt", [nat_term(l, scope)?, nat_term(r, scope)?]))
    }
}

/// Render an arithmetic subterm as a Nat-VALUED kernel term under `scope`.
/// `None` ⇒ outside the covered fragment (fail closed). The fragment produces
/// only non-negative values and is closed under every operator it admits, so
/// the Nat rendering is faithful to the driver's Int model on it.
fn nat_term(e: &PureExpr, scope: &Scope<'_>) -> Option<Expr> {
    match e {
        // Negative literals have no faithful Nat rendering — decline.
        PureExpr::Int(n) => u64::try_from(*n).ok().map(Expr::nat_lit),
        // A contract variable in the scope: an unsigned-integer param/result,
        // rendered as its de Bruijn index. Unknown names (signed, non-integer,
        // unresolvable) are NOT in the scope — decline.
        PureExpr::Var(name, _) => scope.var(name),
        // `v@` on such a variable: View is the identity on the integer model.
        // View of anything else declines (Seq/FMap views are NOT identity).
        PureExpr::View(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => scope.var(name),
            _ => None,
        },
        PureExpr::BinOp(l, op, r) => match op {
            BinOp::Add => Some(capp("Nat.add", [nat_term(l, scope)?, nat_term(r, scope)?])),
            BinOp::Mul => Some(capp("Nat.mul", [nat_term(l, scope)?, nat_term(r, scope)?])),
            // Division/remainder only under a POSITIVE LITERAL divisor: there
            // Euclidean (`Div`/`Mod`) and truncated (`DivTrunc`/`RemTrunc`)
            // semantics coincide with `Nat.div`/`Nat.mod` on the non-negative
            // dividend this fragment guarantees. Division by zero is
            // underspecified in the solver's model but TOTAL in the kernel
            // (`Nat.div x 0 = 0`), so certifying it would be an unfaithful
            // claim — decline anything but `Int(k), k > 0` on the right.
            BinOp::Div | BinOp::DivTrunc => {
                positive_literal(r)?;
                Some(capp("Nat.div", [nat_term(l, scope)?, nat_term(r, scope)?]))
            }
            BinOp::Mod | BinOp::RemTrunc => {
                positive_literal(r)?;
                Some(capp("Nat.mod", [nat_term(l, scope)?, nat_term(r, scope)?]))
            }
            // `Sub` is deliberately absent: kernel `Nat.sub` is MONUS
            // (2 − 3 = 0), not integer subtraction — unfaithful. Fail closed.
            _ => None,
        },
        _ => None,
    }
}

fn positive_literal(e: &PureExpr) -> Option<()> {
    match e {
        PureExpr::Int(n) if *n > 0 => Some(()),
        _ => None,
    }
}

/// `Int`, the kernel type of every bound SIGNED contract variable.
fn int_ty() -> Expr {
    Expr::const_(Name::from_string("Int"), vec![])
}

/// An `i64` as a closed `Int` constructor literal: `Int.ofNat n` for `n ≥ 0`,
/// `Int.negSucc (−n−1)` for `n < 0` (since `negSucc k = −(k+1)`).
fn int_lit(n: i64) -> Option<Expr> {
    if n >= 0 {
        Some(capp("Int.ofNat", [Expr::nat_lit(u64::try_from(n).ok()?)]))
    } else {
        // −n−1 ≥ 0 for n < 0; compute without overflow at i64::MIN.
        let k = u64::try_from(-(n + 1)).ok()?;
        Some(capp("Int.negSucc", [Expr::nat_lit(k)]))
    }
}

/// The inclusive signed range endpoints for a `bits`-wide signed integer, as
/// closed `Int` literals: `(-2^(bits-1), 2^(bits-1) - 1)`. `bits ≤ 64`.
fn signed_bounds(bits: u32) -> Option<(Expr, Expr)> {
    // half = bits-1 ≤ 63, so 2^half fits in i64 (2^63 = i64::MIN magnitude via
    // the i128 intermediate) and 2^half - 1 fits in i64.
    let half = bits.checked_sub(1)?;
    if half >= 64 {
        return None;
    }
    let pow: i128 = 1i128 << half;
    let min = int_lit(i64::try_from(-pow).ok()?)?;
    let max = int_lit(i64::try_from(pow - 1).ok()?)?;
    Some((min, max))
}

/// Render an arithmetic subterm as an `Int`-VALUED kernel term under `scope`
/// (the SIGNED counterpart of `nat_term`). Unlike the Nat model, `Int` is
/// faithful to the driver's integer semantics for negative values and `Sub`.
/// `None` ⇒ outside the covered fragment (fail closed).
fn int_term(e: &PureExpr, scope: &Scope<'_>) -> Option<Expr> {
    match e {
        PureExpr::Int(n) => int_lit(*n),
        PureExpr::Var(name, _) => scope.var(name),
        PureExpr::View(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => scope.var(name),
            _ => None,
        },
        PureExpr::BinOp(l, op, r) => match op {
            BinOp::Add => Some(capp("Int.add", [int_term(l, scope)?, int_term(r, scope)?])),
            BinOp::Sub => Some(capp("Int.sub", [int_term(l, scope)?, int_term(r, scope)?])),
            BinOp::Mul => Some(capp("Int.mul", [int_term(l, scope)?, int_term(r, scope)?])),
            // Int Div/Mod semantics (Euclidean vs truncated) diverge from the
            // kernel's `Int.div`/`Int.mod`; decline rather than claim an
            // unfaithful equality. (Extend when a faithful lemma lands.)
            _ => None,
        },
        _ => None,
    }
}

/// `Eq Bool lhs Bool.true` — Bool lives in `Type 0`, so `Eq` takes level 1.
fn eq_bool_goal(lhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
        [
            bool_ty(),
            lhs,
            Expr::const_(Name::from_string("Bool.true"), vec![]),
        ],
    )
}

/// Collect the scope positions of every bound variable occurring in a rendered
/// term (probes are rendered at `offset` 0 over the FULL scope, so `BVar(i)` ⇔
/// position `n_vars − 1 − i`). Rendered terms contain only
/// Const/Lit/App/BVar nodes — no binders — so a plain spine walk suffices.
fn bvar_positions(e: &Expr, n_vars: usize, acc: &mut BTreeSet<usize>) {
    match e.kind() {
        ExprKind::App(f, a) => {
            bvar_positions(f, n_vars, acc);
            bvar_positions(a, n_vars, acc);
        }
        ExprKind::BVar(i) => {
            if let Some(p) = n_vars.checked_sub(1 + *i as usize) {
                acc.insert(p);
            }
        }
        _ => {}
    }
}

/// Select the subset of `vars` at the given positions, preserving order
/// (params in declaration order, then `result`) — the ∀-binding order.
fn select_vars(vars: &[KernelVar], positions: &BTreeSet<usize>) -> Vec<KernelVar> {
    vars.iter()
        .enumerate()
        .filter(|(p, _)| positions.contains(p))
        .map(|(_, v)| v.clone())
        .collect()
}

/// Build the quantified goal `∀ (bound : Nat), [bounds →] ⟦kept⟧ → ⟦clause⟧ = true`.
///
/// Hypothesis arrows are Pi binders, so a variable's de Bruijn index grows by
/// one per hypothesis standing between the ∀ prefix and the subterm: hypothesis
/// `j` (0-based) renders at offset `j`, the conclusion at offset `k` (the total
/// hypothesis count). `with_bounds` = false is the BARE form (every hypothesis
/// dropped — a sound strengthening; see the module docs).
fn build_goal(
    bound: &[KernelVar],
    with_bounds: bool,
    kept: &[&PureExpr],
    clause: &PureExpr,
) -> Option<Expr> {
    let n = bound.len();
    // Homogeneous signedness: the whole goal is Nat (unsigned) or Int (signed).
    // Mixed signed/unsigned bindings are outside the covered fragment — decline
    // (fail closed) rather than model one var's range in the wrong type.
    let signed = if bound.is_empty() {
        false
    } else if bound.iter().all(|v| v.signed) {
        true
    } else if bound.iter().all(|v| !v.signed) {
        false
    } else {
        return None;
    };
    let mut hyps: Vec<Expr> = Vec::new();
    if with_bounds {
        for (p, v) in bound.iter().enumerate() {
            let base = u32::try_from(n - 1 - p).ok()?;
            if signed {
                // Two-sided range: `min ≤ x` AND `x ≤ max`, each a Bool hyp.
                let (min, max) = signed_bounds(v.bits)?;
                let o1 = u32::try_from(hyps.len()).ok()?;
                hyps.push(eq_bool_goal(capp("Int.ble", [min, Expr::bvar(base + o1)])));
                let o2 = u32::try_from(hyps.len()).ok()?;
                hyps.push(eq_bool_goal(capp("Int.ble", [Expr::bvar(base + o2), max])));
            } else {
                let o = u32::try_from(hyps.len()).ok()?;
                hyps.push(eq_bool_goal(capp(
                    "Nat.ble",
                    [Expr::bvar(base + o), unsigned_max_lit(v.bits)],
                )));
            }
        }
    }
    for r in kept {
        let scope = Scope {
            vars: bound,
            offset: u32::try_from(hyps.len()).ok()?,
            signed,
        };
        hyps.push(eq_bool_goal(bool_term(r, &scope)?));
    }
    let concl_scope = Scope {
        vars: bound,
        offset: u32::try_from(hyps.len()).ok()?,
        signed,
    };
    let concl = eq_bool_goal(bool_term(clause, &concl_scope)?);
    let chain = hyps
        .into_iter()
        .rev()
        .fold(concl, |acc, h| Expr::arrow(h, acc));
    let binder_ty = if signed { int_ty() } else { nat_ty() };
    Some((0..n).fold(chain, |acc, _| {
        Expr::pi(BinderInfo::Default, binder_ty.clone(), acc)
    }))
}

/// Translate a driver obligation clause into its BARE `clean_kernel` goal:
/// `∀ (used vars : Nat), Eq Bool ⟦clause⟧ Bool.true` (no binders when the
/// clause is ground). `None` ⇒ the CONCLUSION is outside the covered fragment —
/// the clause stays solver-only and no kernel claim is made (fail closed).
pub(crate) fn formula_to_expr(clause: &PureExpr, vars: &[KernelVar]) -> Option<Expr> {
    // Probe under the goal's homogeneous signedness so the render selects the
    // right integer vocabulary; `build_goal` re-derives it from the used subset
    // and declines a mixed binding.
    let signed = !vars.is_empty() && vars.iter().all(|v| v.signed);
    let probe = bool_term(
        clause,
        &Scope {
            vars,
            offset: 0,
            signed,
        },
    )?;
    let mut used = BTreeSet::new();
    bvar_positions(&probe, vars.len(), &mut used);
    build_goal(&select_vars(vars, &used), false, &[], clause)
}

/// One clean-auto leg of the race: `auto_prove` (5s) on the obligation's
/// elaborated goal, the produced term graded THROUGH THE FROZEN INTERFACE.
/// Returns the status only when the meter certifies: any non-Certified outcome
/// of an auto candidate judges the TERM, not the obligation — no claim escapes.
fn auto_attempt(env: &Environment, engine: &AutomationEngine, ob: &UOb) -> Option<ClauseStatus> {
    let goal = ob.elaborated_goal();
    let result = engine.auto_prove(env, &goal, Duration::from_secs(5), None)?;
    let verdict = LaneVerdict::Term {
        term: result.proof_term().clone(),
        auto: true,
    };
    let status = grade_verdict(env, ob, &verdict, ProgramTier::TrustedReflection);
    if matches!(status.logic, LogicTier::Certified { .. }) {
        Some(status)
    } else {
        debug!(
            "kernel-lane: clean-auto candidate failed the meter ({:?}) — \
             a statement about the term, not the obligation; no claim",
            status.logic
        );
        None
    }
}

/// Attempt the kernel lane on one obligation clause: render the conclusion
/// exactly, gather the best-effort hypothesis pool, race the candidate routes,
/// and grade every verdict THROUGH THE FROZEN INTERFACE.
///
/// `None` ⇒ the conclusion is outside the covered fragment: no kernel claim.
/// `Some(status)` is a meter grade (I1: `grade_verdict` is the only path to a
/// `ClauseStatus`); `Rejected` is surfaced only under the zero-requires,
/// variable-free condition documented in the module docs.
pub(crate) fn kernel_grade_obligation(
    env: &Environment,
    engine: &AutomationEngine,
    ctx: &ObligationCtx<'_>,
    clause: &PureExpr,
) -> Option<ClauseStatus> {
    let full_scope = Scope {
        vars: ctx.vars,
        offset: 0,
        signed: !ctx.vars.is_empty() && ctx.vars.iter().all(|v| v.signed),
    };
    // The conclusion must render EXACTLY — else fail closed (no claim at all).
    let concl_probe = bool_term(clause, &full_scope)?;
    let mut concl_used = BTreeSet::new();
    bvar_positions(&concl_probe, ctx.vars.len(), &mut concl_used);

    // ROUTE 1 (ground conclusions) — the refl candidate on the hypothesis-free
    // goal: `Eq.refl Bool ⟦clause⟧` has type `Eq Bool ⟦clause⟧ ⟦clause⟧`; the
    // goal demands `… ⟦clause⟧ Bool.true`, so the KERNEL's defeq check decides.
    // Proving the clause outright is STRONGER than `requires ⟹ ensures` — a
    // Certified grade is sound for the obligation regardless of hypotheses.
    if concl_used.is_empty() {
        let ob = UOb::new(eq_bool_goal(concl_probe.clone()), ObKind::Postcondition);
        let term = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![Level::succ(Level::zero())]),
            [bool_ty(), concl_probe.clone()],
        );
        let verdict = LaneVerdict::Term { term, auto: true };
        let status = grade_verdict(env, &ob, &verdict, ProgramTier::TrustedReflection);
        match &status.logic {
            LogicTier::Certified { .. } => return Some(status),
            // The reporting-hole fix: a computed-false GROUND clause refutes
            // the OBLIGATION only when the contract assumes nothing at all.
            // With any requires present the obligation may hold vacuously —
            // degrade to the remaining routes and, failing those, to Pending.
            LogicTier::Rejected { .. } if ctx.requires.is_empty() => return Some(status),
            _ => {}
        }
    }

    // The hypothesis pool: per-variable width bounds + every requires clause
    // that translates. Best-effort BY DESIGN — a dropped hypothesis STRENGTHENS
    // the goal, which is sound for certifying (module docs); the conclusion was
    // rendered exactly above.
    let mut kept: Vec<&PureExpr> = Vec::new();
    let mut bound_positions = concl_used.clone();
    for r in ctx.requires {
        match bool_term(r, &full_scope) {
            Some(probe) => {
                bvar_positions(&probe, ctx.vars.len(), &mut bound_positions);
                kept.push(r);
            }
            None => debug!(
                "kernel-lane: requires clause outside the fragment DROPPED \
                 (goal strengthened — sound for certifying): {r}"
            ),
        }
    }
    let bound = select_vars(ctx.vars, &bound_positions);

    // ROUTE 2 (conclusions with variables) — clean-auto on the BARE quantified
    // conclusion: every hypothesis dropped (sound strengthening). This is the
    // form the induction lane (`Nat.rec`) actually closes for ∀-Nat tautologies.
    if !concl_used.is_empty() {
        let bare = select_vars(ctx.vars, &concl_used);
        if let Some(goal) = build_goal(&bare, false, &[], clause) {
            let ob = UOb::new(goal, ObKind::Postcondition);
            if let Some(status) = auto_attempt(env, engine, &ob) {
                return Some(status);
            }
        }
    }

    // ROUTE 3 — clean-auto on the FULL rendering (bounds + kept requires).
    // Closed hypothesis chains ride `UOb::hypotheses` (I3 folds them); with
    // variables the chain must sit UNDER the ∀ prefix, so it is baked into the
    // goal itself (I3's fold happens OUTSIDE any binder).
    let full_ob = if bound.is_empty() {
        let mut ob = UOb::new(eq_bool_goal(concl_probe), ObKind::Postcondition);
        ob.hypotheses = kept
            .iter()
            .map(|r| Some(eq_bool_goal(bool_term(r, &full_scope)?)))
            .collect::<Option<Vec<_>>>()?;
        ob
    } else {
        UOb::new(
            build_goal(&bound, true, &kept, clause)?,
            ObKind::Postcondition,
        )
    };
    if !kept.is_empty() || !bound.is_empty() {
        if let Some(status) = auto_attempt(env, engine, &full_ob) {
            return Some(status);
        }
    }

    // Nothing closed: an honest Decline, graded (I1) to Pending — never a
    // fabricated Rejected.
    let verdict = LaneVerdict::Decline {
        reason: "no kernel lane closed the goal".to_string(),
    };
    Some(grade_verdict(
        env,
        &full_ob,
        &verdict,
        // ProgramTier::TrustedReflection is the SAFE DEFAULT and the honest one
        // here: we have not proven the covered-fragment condition of the step
        // relation (design §8-3) for the driver's MIR→spec reflection at this
        // call site — which also keeps `licenses_ub_elision()` false for every
        // status this lane produces.
        ProgramTier::TrustedReflection,
    ))
}

/// The `(bit-width, signed)` of an integer MIR type this lane models, or `None`
/// for non-integer types and the 128-bit widths (outside the `u64`/`i64`
/// literal fragment). `usize`/`isize` resolve to the target pointer width —
/// the same resolution as `callbacks::integer_range`.
fn integer_kind_bits(
    kind: &rustc_middle::ty::TyKind<'_>,
    pointer_bits: u32,
) -> Option<(u32, bool)> {
    use rustc_middle::ty::TyKind;
    match kind {
        TyKind::Uint(u) => {
            let bits = crate::callbacks::integer_range::uint_bit_width(*u, pointer_bits);
            (bits <= 64).then_some((bits, false))
        }
        TyKind::Int(i) => {
            let bits = crate::callbacks::integer_range::int_bit_width(*i, pointer_bits);
            (bits <= 64).then_some((bits, true))
        }
        _ => None,
    }
}

/// Resolve the contract variables this lane can render: parameters (and
/// `result`) of integer MIR type — UNSIGNED (`u8`..`u64`/`usize`, modeled as
/// `Nat`) or SIGNED (`i8`..`i64`/`isize`, modeled as `Int`). Width resolution
/// matches `callbacks::integer_range`, the range-precondition source of truth.
///
/// Fail-closed exclusions: closures (no `fn_sig`), the 128-bit widths (bound
/// exceeds the `u64`/`i64` literal fragment), parameters bound by non-identifier
/// patterns (no stable name), and — when a parameter is literally named
/// `result` — the `result` variable AND that parameter (the ensures name would
/// be ambiguous).
pub(crate) fn kernel_vars_for_contract(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<KernelVar> {
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return Vec::new();
    }
    let sig = tcx.fn_sig(def_id).instantiate_identity();
    let sig = sig.skip_binder();
    let pointer_bits = u32::try_from(tcx.data_layout.pointer_size().bits()).unwrap_or(64);
    let names = hir_param_names(tcx, def_id);

    let mut vars = Vec::new();
    for (i, ty) in sig.inputs().iter().enumerate() {
        let Some(Some(name)) = names.get(i) else {
            continue;
        };
        if name == "result" {
            continue;
        }
        if let Some((bits, signed)) = integer_kind_bits(ty.kind(), pointer_bits) {
            vars.push(KernelVar {
                name: name.clone(),
                bits,
                signed,
            });
        }
    }
    let param_shadows_result = names.iter().flatten().any(|n| n == "result");
    if !param_shadows_result {
        if let Some((bits, signed)) = integer_kind_bits(sig.output().kind(), pointer_bits) {
            vars.push(KernelVar {
                name: "result".to_string(),
                bits,
                signed,
            });
        }
    }
    vars
}

/// Source-level parameter names from the local HIR body (the same resolution
/// `mir_analysis::call_resolve::arg_names_for_def_id` uses for local
/// functions). Non-identifier patterns yield `None` — those parameters simply
/// never enter the variable environment (fail closed).
fn hir_param_names(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<Option<String>> {
    let Some(local_def_id) = def_id.as_local() else {
        return Vec::new();
    };
    let Some(body_id) = tcx.hir_node_by_def_id(local_def_id).body_id() else {
        return Vec::new();
    };
    tcx.hir_body(body_id)
        .params
        .iter()
        .map(|param| match param.pat.kind {
            rustc_hir::PatKind::Binding(_, _, ident, _) => Some(ident.as_str().to_string()),
            _ => None,
        })
        .collect()
}

/// The observation hook: attempt the kernel lane on every ensures clause of a
/// just-discharged contract and debug!-log the per-obligation `ClauseStatus`
/// plus a summary line. Requires clauses are HYPOTHESES at this site (they are
/// obligations only at call sites), so only the ensures vector is graded — the
/// requires vector feeds the hypothesis pool.
///
/// Purely additive: no return value, no effect on the solver verdict.
pub(crate) fn observe_contract_obligations(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    def_path: &str,
    effective_requires: &[PureExpr],
    effective_ensures: &[PureExpr],
) {
    if effective_ensures.is_empty() {
        return;
    }
    let vars = kernel_vars_for_contract(tcx, def_id);
    let ctx = ObligationCtx {
        vars: &vars,
        requires: effective_requires,
    };
    let total = effective_ensures.len();
    let mut certified = 0usize;
    let mut rejected = 0usize;
    let mut pending = 0usize;
    let mut out_of_fragment = 0usize;
    // The prelude environment and the automation engine are only built when at
    // least one clause is inside the fragment — the common all-out-of-fragment
    // case costs the probe walks only.
    let mut lane: Option<(Environment, AutomationEngine)> = None;
    for (idx, clause) in effective_ensures.iter().enumerate() {
        if formula_to_expr(clause, &vars).is_none() {
            out_of_fragment += 1;
            debug!(
                "kernel-lane[{def_path}] ensures#{idx}: outside the covered fragment \
                 (solver-only, no kernel claim): {clause}"
            );
            continue;
        }
        let (env, engine) =
            lane.get_or_insert_with(|| (Environment::with_prelude(), AutomationEngine::new()));
        match kernel_grade_obligation(env, engine, &ctx, clause) {
            Some(status) => {
                match status.logic {
                    LogicTier::Certified { .. } => certified += 1,
                    LogicTier::Rejected { .. } => rejected += 1,
                    _ => pending += 1,
                }
                debug!("kernel-lane[{def_path}] ensures#{idx}: {status:?} for {clause}");
            }
            // Unreachable given the pre-check above, but stay total.
            None => out_of_fragment += 1,
        }
    }
    // Out-of-fragment clauses have no kernel evidence — their interface state
    // is Pending (I4/I5), reported separately so the covered fragment is visible.
    let pending_total = pending + out_of_fragment;
    debug!(
        "kernel-lane[{def_path}] summary: {certified} Certified, \
         {pending_total} Pending ({out_of_fragment} outside fragment), \
         {rejected} Rejected of {total} ensures clauses"
    );
}

/// Feasibility record for the SIGNED-integer contract-variable flagship
/// (paragon completeness). Executable evidence, captured 2026-07-07, that the
/// signed lane is BLOCKED on `clean-auto`, not on this driver:
///
/// * the Int VOCABULARY needed to render signed contracts IS present in
///   `Environment::with_prelude()` — `Int` (`Int.ofNat`/`Int.negSucc`),
///   `Int.add`/`Int.sub`/`Int.mul`, `Int.beq`/`Int.ble`, `Int.le`/`Int.neg`
///   (only `Int.blt` is missing — a rendering would swap `ble` args like the
///   Nat path already does for `>`/`>=`);
/// * BUT `clean-auto` (built here `default-features = false`, NO ay/SMT — the
///   induction/superposition lanes only) discharges NONE of the signed goals,
///   not even the simplest tautology `∀ (x : Int), x == x`, while it closes the
///   *Nat* analog in the very same harness (see `nat_tautology_certifies_control`).
///   The gap is Int-specific, not a harness artifact.
/// * Even GROUND signed arithmetic fails: the refl route (`Eq.refl Bool ⟦c⟧`
///   graded against `Eq Bool ⟦c⟧ Bool.true`) is `Rejected{TypeMismatch}` because
///   `Int.beq (Int.add (ofNat 1) (ofNat 2)) (ofNat 3)` does NOT reduce to
///   `Bool.true` under the kernel's defeq — Int.add/beq are registered but not
///   definitionally computable the way Nat's are.
///
/// Conclusion: a signed *variable* ensures cannot reach `Certified{auto:true}`
/// today; the flagship needs a `clean-auto` Int induction/decision path first
/// (a separate, larger scope). These tests are the tripwire: if `clean-auto`
/// later closes the signed tautologies, `signed_goals_not_yet_dischargeable`
/// FAILS — the signal to wire the signed rendering path (mirror
/// `nat_term`/`kernel_vars_for_contract` with two-sided Int bounds).
#[cfg(test)]
mod signed_feasibility {
    use std::time::Duration;

    use clean_auto::AutomationEngine;
    use trust_spec_iface::{
        clean_kernel::{expr::BinderInfo, Environment, Expr, Level, Name},
        grade_verdict, LaneVerdict, LogicTier, ObKind, ProgramTier, UOb,
    };

    fn c(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }
    fn bool_ty() -> Expr {
        c("Bool")
    }
    /// Int literal n ≥ 0 as `Int.ofNat n`.
    fn of_nat(n: u64) -> Expr {
        Expr::apps(c("Int.ofNat"), [Expr::nat_lit(n)])
    }
    fn eq_bool_goal(lhs: Expr) -> Expr {
        Expr::apps(
            Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
            [bool_ty(), lhs, c("Bool.true")],
        )
    }
    /// `auto_prove` (5s) + meter-grade, exactly as the lane's `auto_attempt` does.
    fn auto_grade(env: &Environment, engine: &AutomationEngine, goal: Expr) -> LogicTier {
        let ob = UOb::new(goal, ObKind::Postcondition);
        match engine.auto_prove(env, &ob.elaborated_goal(), Duration::from_secs(5), None) {
            Some(result) => {
                let verdict = LaneVerdict::Term {
                    term: result.proof_term().clone(),
                    auto: true,
                };
                grade_verdict(env, &ob, &verdict, ProgramTier::TrustedReflection).logic
            }
            None => LogicTier::Pending,
        }
    }

    /// The Int rendering vocabulary the (future) signed lane would emit exists in
    /// the prelude — the flagship is NOT blocked on missing constants.
    #[test]
    fn int_vocabulary_present_in_prelude() {
        let env = Environment::with_prelude();
        for n in [
            "Int",
            "Int.ofNat",
            "Int.negSucc",
            "Int.rec",
            "Int.neg",
            "Int.add",
            "Int.sub",
            "Int.mul",
            "Int.beq",
            "Int.ble",
            "Int.le",
        ] {
            assert!(
                env.get_const(&Name::from_string(n)).is_some(),
                "signed lane needs {n} in Environment::with_prelude()"
            );
        }
        // `Int.blt` is absent (unlike `Nat.blt`); a signed `<` would render via a
        // `ble` argument swap, the same trick the Nat path uses for `>`/`>=`.
        assert!(env.get_const(&Name::from_string("Int.blt")).is_none());
    }

    /// POSITIVE CONTROL: the SAME harness proves the Nat analogs to
    /// `Certified{auto:true}` — so a `None` for the Int versions below is an
    /// Int-specific `clean-auto` limitation, not a harness mistake.
    #[test]
    fn nat_tautology_certifies_control() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        let x = || Expr::bvar(0);
        let forall_nat = |body: Expr| Expr::pi(BinderInfo::Default, c("Nat"), body);
        // ∀ n, n <= n
        assert!(matches!(
            auto_grade(
                &env,
                &engine,
                forall_nat(eq_bool_goal(Expr::apps(c("Nat.ble"), [x(), x()]))),
            ),
            LogicTier::Certified { auto: true }
        ));
        // ∀ n, (n + 0) == n
        assert!(matches!(
            auto_grade(
                &env,
                &engine,
                forall_nat(eq_bool_goal(Expr::apps(
                    c("Nat.beq"),
                    [Expr::apps(c("Nat.add"), [x(), Expr::nat_lit(0)]), x()],
                ))),
            ),
            LogicTier::Certified { auto: true }
        ));
    }

    /// SIGNED FLAGSHIP ACHIEVED (was the `signed_goals_not_yet_dischargeable`
    /// tripwire). clean-auto now discharges the reflexive-equality flagship
    /// `∀x:Int, Int.beq x x = true` — the shape the signed contract lane emits
    /// for `ensures x == x` — via the Step A `Int.beq` symbolic `Int.rec`
    /// reduction plus the Step B non-recursive-eliminator field-induction
    /// fallback (clean `ed98e747` / `588f335c`).
    ///
    /// The honest boundary the meter still reports as Pending: `Int.ble` under a
    /// binder (`∀x, x ≤ x`) and open `Int.add` under a binder (`∀x, x + 0 == x`)
    /// both route through the `subNatNat` iterated-decrement recursion, which is
    /// stuck on a symbolic `Nat` — the next milestone (would need `Int.ble` as a
    /// reducible `Int.rec` definition and/or `subNatNat` reduction lemmas).
    #[test]
    fn signed_reflexive_equality_certifies_ble_and_open_add_pending() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        let x = || Expr::bvar(0);
        let forall_int = |body: Expr| Expr::pi(BinderInfo::Default, c("Int"), body);
        let certifies =
            |g: Expr| matches!(auto_grade(&env, &engine, g), LogicTier::Certified { .. });

        // NOW CERTIFIED — the reflexive-equality flagship.
        assert!(
            certifies(forall_int(eq_bool_goal(Expr::apps(
                c("Int.beq"),
                [x(), x()]
            )))),
            "the signed flagship ∀x:Int, Int.beq x x = true must certify"
        );

        // STILL PENDING — the next boundary (subNatNat stuck under a binder).
        // ∀ x, Int.ble x x = true
        assert!(
            !certifies(forall_int(eq_bool_goal(Expr::apps(
                c("Int.ble"),
                [x(), x()]
            )))),
            "Int.ble under ∀ is not yet dischargeable"
        );
        // ∀ x, (x + 0) == x
        assert!(
            !certifies(forall_int(eq_bool_goal(Expr::apps(
                c("Int.beq"),
                [Expr::apps(c("Int.add"), [x(), of_nat(0)]), x()],
            )))),
            "open Int.add (x+0) under ∀ is not yet dischargeable"
        );
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use clean_auto::AutomationEngine;
    use trust_spec_iface::{clean_kernel::Environment, BoundTier, LogicTier, ProgramTier};
    use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

    use super::{formula_to_expr, kernel_grade_obligation, KernelVar, ObligationCtx};

    fn int(n: i64) -> Arc<PureExpr> {
        Arc::new(PureExpr::Int(n))
    }

    fn var(name: &str) -> Arc<PureExpr> {
        Arc::new(PureExpr::Var(name.to_string(), None))
    }

    fn view(inner: Arc<PureExpr>) -> Arc<PureExpr> {
        Arc::new(PureExpr::View(inner))
    }

    fn bin(l: Arc<PureExpr>, op: BinOp, r: Arc<PureExpr>) -> Arc<PureExpr> {
        Arc::new(PureExpr::BinOp(l, op, r))
    }

    fn uvar(name: &str, bits: u32) -> KernelVar {
        KernelVar {
            name: name.to_string(),
            bits,
            signed: false,
        }
    }

    fn ivar(name: &str, bits: u32) -> KernelVar {
        KernelVar {
            name: name.to_string(),
            bits,
            signed: true,
        }
    }

    const NO_VARS: &[KernelVar] = &[];
    const NO_REQUIRES: &[PureExpr] = &[];

    fn ground_ctx() -> ObligationCtx<'static> {
        ObligationCtx {
            vars: NO_VARS,
            requires: NO_REQUIRES,
        }
    }

    fn assert_certified(
        env: &Environment,
        engine: &AutomationEngine,
        ctx: &ObligationCtx<'_>,
        clause: &PureExpr,
    ) {
        let status = kernel_grade_obligation(env, engine, ctx, clause)
            .unwrap_or_else(|| panic!("clause should be inside the fragment: {clause}"));
        assert!(
            matches!(status.logic, LogicTier::Certified { auto: true }),
            "expected Certified{{auto:true}} for {clause}, got {:?}",
            status.logic
        );
        // The reflection tier is the safe default: never CertifiedReflection,
        // so no status from this lane ever licenses UB elision.
        assert_eq!(status.program, ProgramTier::TrustedReflection);
        assert_eq!(status.bound, BoundTier::Unbounded);
        assert!(!status.licenses_ub_elision());
    }

    /// Ground linear arithmetic grades Certified via the auto/refl route
    /// through the frozen interface: the meter (not this lane) decides.
    #[test]
    fn formula_kernel_lane_ground_arith_certifies_via_auto_refl() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        let ctx = ground_ctx();
        // 1 + 2 == 3
        assert_certified(
            &env,
            &engine,
            &ctx,
            &bin(bin(int(1), BinOp::Add, int(2)), BinOp::Eq, int(3)),
        );
        // 2 * 3 + 1 == 7
        assert_certified(
            &env,
            &engine,
            &ctx,
            &bin(
                bin(bin(int(2), BinOp::Mul, int(3)), BinOp::Add, int(1)),
                BinOp::Eq,
                int(7),
            ),
        );
        // 7 / 2 == 3 (Euclidean == truncated == Nat.div on this fragment)
        assert_certified(
            &env,
            &engine,
            &ctx,
            &bin(bin(int(7), BinOp::Div, int(2)), BinOp::Eq, int(3)),
        );
        // 7 % 2 == 1
        assert_certified(
            &env,
            &engine,
            &ctx,
            &bin(bin(int(7), BinOp::Mod, int(2)), BinOp::Eq, int(1)),
        );
    }

    /// Comparisons, boolean equality, and the connectives all render into the
    /// kernel's computable Bool vocabulary and certify.
    #[test]
    fn formula_kernel_lane_comparisons_and_connectives_certify() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        let ctx = ground_ctx();
        // (1 < 2 && !(3 <= 2)) ==> 4 >= 4
        let lhs = bin(
            bin(int(1), BinOp::Lt, int(2)),
            BinOp::And,
            Arc::new(PureExpr::UnOp(UnOp::Not, bin(int(3), BinOp::Le, int(2)))),
        );
        assert_certified(
            &env,
            &engine,
            &ctx,
            &bin(lhs, BinOp::Implies, bin(int(4), BinOp::Ge, int(4))),
        );
        // 5 > 4 || false
        assert_certified(
            &env,
            &engine,
            &ctx,
            &bin(
                bin(int(5), BinOp::Gt, int(4)),
                BinOp::Or,
                Arc::new(PureExpr::Bool(false)),
            ),
        );
        // 1 != 2
        assert_certified(&env, &engine, &ctx, &bin(int(1), BinOp::Ne, int(2)));
        // Sort-dispatched boolean equality: (1 == 1) == true
        assert_certified(
            &env,
            &engine,
            &ctx,
            &bin(
                bin(int(1), BinOp::Eq, int(1)),
                BinOp::Eq,
                Arc::new(PureExpr::Bool(true)),
            ),
        );
    }

    /// Fail closed: everything outside the faithful fragment translates to
    /// `None` — the obligation stays solver-only, no kernel claim of any kind.
    /// With an EMPTY variable environment (signed / unknown / unresolvable
    /// contract variables never enter it), any variable reference declines.
    #[test]
    fn formula_kernel_lane_out_of_fragment_declines_to_none() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        let ctx = ground_ctx();
        let out_of_fragment: Vec<Arc<PureExpr>> = vec![
            // Free variable NOT in the environment (e.g. a SIGNED param —
            // signed types never enter the env: no faithful Nat rendering).
            bin(var("x"), BinOp::Eq, int(1)),
            // Negative literal: no faithful Nat rendering.
            bin(int(-1), BinOp::Lt, int(0)),
            // Subtraction: kernel Nat.sub is monus (2 - 3 = 0), unfaithful.
            bin(bin(int(2), BinOp::Sub, int(3)), BinOp::Eq, int(0)),
            // Division by zero: total in the kernel, underspecified in the
            // solver's model — certifying `1 / 0 == 0` would be unfaithful.
            bin(bin(int(1), BinOp::Div, int(0)), BinOp::Eq, int(0)),
            // Non-literal divisor: same guard, fail closed.
            bin(
                bin(int(8), BinOp::Div, bin(int(1), BinOp::Add, int(1))),
                BinOp::Eq,
                int(4),
            ),
            // View of a non-variable: only `var@` is the identity rendering.
            bin(view(int(3)), BinOp::Eq, int(3)),
            // Quantifier: not in the clause fragment.
            Arc::new(PureExpr::Forall {
                var: "x".to_string(),
                var_sort: None,
                body: bin(var("x"), BinOp::Eq, var("x")),
                triggers: Vec::new(),
            }),
            // Bare non-boolean term: not a clause in the fragment.
            int(3),
        ];
        for clause in &out_of_fragment {
            assert!(
                formula_to_expr(clause, NO_VARS).is_none(),
                "must fail closed (None) for {clause}"
            );
            assert!(
                kernel_grade_obligation(&env, &engine, &ctx, clause).is_none(),
                "must make NO kernel claim for {clause}"
            );
        }
    }

    /// A SIGNED variable never enters the environment, so a clause over it
    /// declines even when an unsigned sibling is renderable.
    #[test]
    fn formula_kernel_lane_signed_var_declines_even_with_unsigned_env() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        let vars = vec![uvar("x", 32)]; // `y: i32` is NOT in the env
        let ctx = ObligationCtx {
            vars: &vars,
            requires: NO_REQUIRES,
        };
        let clause = bin(var("y"), BinOp::Le, var("y"));
        assert!(formula_to_expr(&clause, &vars).is_none());
        assert!(kernel_grade_obligation(&env, &engine, &ctx, &clause).is_none());
        // Mixed: unsigned var alone is fine, adding the signed one declines.
        let mixed = bin(var("x"), BinOp::Le, var("y"));
        assert!(kernel_grade_obligation(&env, &engine, &ctx, &mixed).is_none());
    }

    /// Predictability roundtrip (audit 2026-07-07): every constant this lane can emit
    /// must classify Auto under the interface's author-time checker — the lane and the
    /// whitelist may never disagree. (The quantified GOALS route Deep — binders — by
    /// design; this pins the emitted CONSTANT vocabulary only.)
    #[test]
    fn formula_kernel_lane_vocabulary_classifies_auto() {
        use trust_spec_iface::clean_kernel::{Expr, Name};
        for c in [
            "Nat",
            "Nat.add",
            "Nat.mul",
            "Nat.div",
            "Nat.mod",
            "Nat.beq",
            "Nat.ble",
            "Nat.blt",
            "Bool.and",
            "Bool.or",
            "Bool.not",
            "Bool.beq",
            "Bool.true",
            "Bool.false",
        ] {
            let e = Expr::const_(Name::from_string(c), vec![]);
            assert!(
                trust_spec_iface::classify_auto_fragment(&e).is_ok(),
                "lane-emittable const {c} must classify Auto"
            );
        }
    }

    /// A false ground clause of a contract with ZERO requires clauses is
    /// Rejected by the METER (the refl candidate does not type-check against
    /// the goal) — never Certified, and this lane never decides falsity itself.
    #[test]
    fn formula_kernel_lane_false_ground_formula_never_certifies() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        let ctx = ground_ctx();
        let false_clauses: Vec<Arc<PureExpr>> = vec![
            bin(int(1), BinOp::Eq, int(2)),
            bin(bin(int(2), BinOp::Add, int(2)), BinOp::Eq, int(5)),
            bin(
                bin(int(3), BinOp::Lt, int(2)),
                BinOp::Or,
                Arc::new(PureExpr::Bool(false)),
            ),
        ];
        for clause in &false_clauses {
            let status = kernel_grade_obligation(&env, &engine, &ctx, clause)
                .unwrap_or_else(|| panic!("false ground clause is still in-fragment: {clause}"));
            assert!(
                matches!(status.logic, LogicTier::Rejected { .. }),
                "expected Rejected for {clause}, got {:?}",
                status.logic
            );
            assert!(!matches!(status.logic, LogicTier::Certified { .. }));
            assert!(!status.licenses_ub_elision());
        }
    }

    /// The reporting-hole fix: with ANY requires clause present, clause-false
    /// does NOT imply obligation-false (the requires may be unsatisfiable and
    /// the contract vacuously true) — the failed candidate degrades to a
    /// no-kernel-claim Pending, never a Rejected.
    #[test]
    fn formula_kernel_lane_false_ground_with_requires_makes_no_rejected_claim() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        let false_clause = bin(int(1), BinOp::Eq, int(2));
        // A vacuous (itself false) TRANSLATABLE requires: `2 == 1`. The
        // obligation `2 == 1 ⟹ 1 == 2` is TRUE — Rejected would be a lie.
        let vacuous = vec![(*bin(int(2), BinOp::Eq, int(1))).clone()];
        let ctx = ObligationCtx {
            vars: NO_VARS,
            requires: &vacuous,
        };
        let status = kernel_grade_obligation(&env, &engine, &ctx, &false_clause)
            .expect("ground clause stays in-fragment");
        assert!(
            !matches!(status.logic, LogicTier::Rejected { .. }),
            "with requires present, no Rejected claim may surface; got {:?}",
            status.logic
        );
        assert!(!matches!(status.logic, LogicTier::Certified { .. }));

        // Same with an UNTRANSLATABLE requires (dropped as hypothesis, but
        // still forbids the Rejected claim — the obligation has hypotheses).
        let opaque = vec![(*bin(var("p"), BinOp::Gt, int(0))).clone()];
        let ctx = ObligationCtx {
            vars: NO_VARS,
            requires: &opaque,
        };
        let status = kernel_grade_obligation(&env, &engine, &ctx, &false_clause)
            .expect("ground clause stays in-fragment");
        assert!(
            !matches!(status.logic, LogicTier::Rejected { .. }),
            "untranslatable requires still suppresses Rejected; got {:?}",
            status.logic
        );

        // A TRUE ground clause under the same requires still certifies (refl
        // proves the clause outright — stronger than the obligation, sound).
        let true_clause = bin(int(1), BinOp::Eq, int(1));
        let status = kernel_grade_obligation(&env, &engine, &ctx, &true_clause)
            .expect("ground clause stays in-fragment");
        assert!(
            matches!(status.logic, LogicTier::Certified { auto: true }),
            "true ground clause certifies regardless of requires; got {:?}",
            status.logic
        );
    }

    /// Unsigned-variable TAUTOLOGIES certify via the clean-auto race leg: the
    /// induction lane assembles a Nat.rec term for the bare quantified goal and
    /// the meter (not this lane) certifies it.
    #[test]
    fn formula_kernel_lane_unsigned_var_tautology_certifies_via_clean_auto() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        let vars = vec![uvar("x", 32)];
        let ctx = ObligationCtx {
            vars: &vars,
            requires: NO_REQUIRES,
        };
        // x <= x
        assert_certified(&env, &engine, &ctx, &bin(var("x"), BinOp::Le, var("x")));
        // x + 0 == x
        assert_certified(
            &env,
            &engine,
            &ctx,
            &bin(bin(var("x"), BinOp::Add, int(0)), BinOp::Eq, var("x")),
        );
        // The view operator on an unsigned variable is the identity: x@ <= x@
        assert_certified(
            &env,
            &engine,
            &ctx,
            &bin(view(var("x")), BinOp::Le, view(var("x"))),
        );
        // Hypotheses are best-effort: an untranslatable requires is dropped and
        // the tautology still certifies (dropping = stronger goal = sound).
        let opaque = vec![(*bin(var("p"), BinOp::Gt, int(0))).clone()];
        let ctx = ObligationCtx {
            vars: &vars,
            requires: &opaque,
        };
        assert_certified(&env, &engine, &ctx, &bin(var("x"), BinOp::Le, var("x")));
    }

    /// THE SIGNED FLAGSHIP: `ensures x == x` on an `i32` parameter. The lane
    /// renders `∀ (x : Int), -2^31 ≤ x → x ≤ 2^31-1 → Int.beq x x = true`
    /// (two-sided `Int.ble` bounds as antecedents, `Int.beq` conclusion) and
    /// clean-auto discharges it — the Step A `Int.beq` symbolic reduction plus
    /// the Step B non-recursive-`Int.rec`-minor field-induction fallback. This
    /// is the first SIGNED contract-syntax obligation graded Certified{auto} by
    /// the kernel lane.
    #[test]
    fn formula_kernel_lane_signed_var_reflexive_equality_certifies_via_clean_auto() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        let vars = vec![ivar("x", 32)];
        let ctx = ObligationCtx {
            vars: &vars,
            requires: NO_REQUIRES,
        };
        assert_certified(&env, &engine, &ctx, &bin(var("x"), BinOp::Eq, var("x")));
    }

    /// A variable ensures needing FUNCTION SEMANTICS (`result == a + b`) is not
    /// provable from the contract text alone: the lane stays honest — Pending,
    /// never Rejected, never Certified.
    #[test]
    fn formula_kernel_lane_semantic_var_ensures_stays_pending() {
        let env = Environment::with_prelude();
        let engine = AutomationEngine::new();
        let vars = vec![uvar("a", 32), uvar("b", 32), uvar("result", 32)];
        let ctx = ObligationCtx {
            vars: &vars,
            requires: NO_REQUIRES,
        };
        let clause = bin(
            var("result"),
            BinOp::Eq,
            bin(var("a"), BinOp::Add, var("b")),
        );
        let status = kernel_grade_obligation(&env, &engine, &ctx, &clause)
            .expect("semantic clause is inside the variable fragment");
        assert!(
            matches!(status.logic, LogicTier::Pending),
            "expected Pending for {clause}, got {:?}",
            status.logic
        );
        assert!(!status.licenses_ub_elision());
    }

    /// The bare quantified goal binds exactly the variables the conclusion
    /// uses, in declaration order — a structural pin for the de Bruijn math.
    #[test]
    fn formula_kernel_lane_bare_goal_binds_used_vars_only() {
        use trust_spec_iface::clean_kernel::expr::ExprKind;
        let vars = vec![uvar("a", 8), uvar("b", 16), uvar("result", 64)];
        // b <= b uses one var; a and result must not be bound.
        let goal =
            formula_to_expr(&bin(var("b"), BinOp::Le, var("b")), &vars).expect("tautology renders");
        let mut pis = 0usize;
        let mut cur = &goal;
        while let ExprKind::Pi(_, _, body) = cur.kind() {
            pis += 1;
            cur = body;
        }
        assert_eq!(pis, 1, "exactly the used variable is ∀-bound");
        // Ground clause: no binders at all.
        let goal = formula_to_expr(&bin(int(1), BinOp::Eq, int(1)), &vars).expect("renders");
        assert!(
            !matches!(goal.kind(), ExprKind::Pi(..)),
            "ground clause renders binder-free"
        );
    }
}
