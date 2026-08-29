// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sound completeness lemmas for nonlinear integer products.
//!
//! `ay-dpll` reasons in linear integer arithmetic: a multiplication term
//! `mul(x, y)` where neither operand is a literal is effectively an
//! uninterpreted, unconstrained value. For an obligation like
//! `dumb_nonlinear_arith` (`#[requires(a@ <= 1000)] #[ensures(a@ * a@ <= 1_000_000)]`)
//! the solver can pick `mul(a, a) > 1_000_000` and report a spurious
//! counterexample.
//!
//! This pass restores completeness *without any soundness risk* by emitting
//! the monotonicity-of-multiplication theorem as a guarded ground lemma. For a
//! product term `mul(x, y)` where constant upper bounds `kx`/`ky` and a
//! non-negative lower bound for each operand are derivable from the current
//! assertions, it asserts:
//!
//! ```text
//!   (0 <= x && x <= kx && 0 <= y && y <= ky)  ==>  mul(x, y) <= kx*ky
//!   (0 <= x && 0 <= y)                         ==>  mul(x, y) >= 0
//! ```
//!
//! Both implications are *unconditional theorems of integer arithmetic*: the
//! antecedent is fully spelled out in the lemma itself, so the assertion is
//! true in every model regardless of how (or whether) the bounds were actually
//! derived. The solver discharges the antecedent from its own asserted bounds
//! and the consequent then closes the goal linearly (`mul(x, y)` is a single
//! opaque term and `kx*ky` is a folded constant).
//!
//! ## Soundness contract
//!
//! - The emitted fact is always the *implication* `bounds ==> product-bound`,
//!   never a bare `mul(x, y) <= K`. Even a mis-derived `kx`/`ky` cannot make a
//!   false fact: monotonicity of `*` on the non-negative integers is a theorem,
//!   so `(0<=x<=kx && 0<=y<=ky) ==> x*y <= kx*ky` holds for *all* integer
//!   `x, y, kx, ky` (the antecedent is vacuous when the bounds don't hold).
//! - We only emit when `kx` and `ky` are concrete non-negative integer
//!   constants. No quantified nonlinear axioms are produced.
//! - Completeness loss (emitting nothing) is always acceptable; emitting a
//!   false fact is not. When in doubt, this pass emits nothing.

use std::collections::HashMap;

use ay_dpll::api::{Sort, Term, TermKind};
use num_bigint::BigInt;
use num_traits::ToPrimitive;

use crate::{encoder::AYEncoder, error::EncodingError};

/// Upper limit on how many distinct product terms we instantiate per flush.
/// Product bounds are cheap (a single linear implication each) but we still cap
/// to keep the assertion set bounded on pathological inputs.
const MAX_PRODUCT_BOUND_INSTANCES: usize = 64;

/// Maximum recursion depth when walking asserted terms for `mul`/bound
/// extraction. Guards against deeply nested or cyclic term graphs.
const MAX_WALK_DEPTH: usize = 64;

/// SMT symbol for the uninterpreted nonlinear-product function emitted by the
/// `BinOp::Mul` encoder when neither operand is a literal. Must stay in sync
/// with the `NLMUL` constant in `encoder::operators::encode_nonlinear_mul_uf`.
const NONLINEAR_MUL_UF: &str = "__trust_wp_nonlinear_mul";

/// Inclusive numeric bounds for an integer-sorted term.
#[derive(Clone, Copy, Debug)]
struct IntBounds {
    /// Greatest known lower bound, if any.
    lower: Option<i128>,
    /// Least known upper bound, if any.
    upper: Option<i128>,
}

impl IntBounds {
    const fn empty() -> Self {
        Self {
            lower: None,
            upper: None,
        }
    }

    fn tighten_lower(&mut self, candidate: i128) {
        self.lower = Some(match self.lower {
            Some(existing) => existing.max(candidate),
            None => candidate,
        });
    }

    fn tighten_upper(&mut self, candidate: i128) {
        self.upper = Some(match self.upper {
            Some(existing) => existing.min(candidate),
            None => candidate,
        });
    }
}

impl AYEncoder {
    /// Emit guarded product-bound completeness lemmas for nonlinear integer
    /// multiplications in the current assertion set.
    ///
    /// Returns the number of lemmas asserted. This is a completeness aid only:
    /// every emitted fact is a tautology of integer arithmetic (see module
    /// docs), so it can never introduce a false-accept. Failures to derive
    /// bounds are silently skipped.
    pub(crate) fn assert_nonlinear_product_bounds(&mut self) -> Result<usize, EncodingError> {
        let assertions = self.solver.assertions();

        // 1. Collect distinct nonlinear product terms (the UF abstraction, or a
        //    native `*` with two opaque operands). This single walk is the cheap
        //    gate: the overwhelming majority of obligations contain no nonlinear
        //    product, so we return immediately and skip the (more expensive)
        //    bound/exact-value collection below. This keeps the pass close to
        //    zero-cost on the common case (e.g. recursive list/Seq proofs that
        //    re-solve many times). (#knights-tour perf gate)
        let mut products: Vec<(Term, Term, Term)> = Vec::new();
        let mut seen: std::collections::HashSet<Term> = std::collections::HashSet::new();
        for &assertion in &assertions {
            self.collect_products(assertion, &mut products, &mut seen, 0);
        }
        if products.is_empty() {
            return Ok(0);
        }

        // 2. Derive constant integer bounds and exact pinned values for terms
        //    from the asserted comparisons / equalities (top-level conjuncts
        //    only — see the collectors' soundness notes).
        let mut bounds: HashMap<Term, IntBounds> = HashMap::new();
        // Exact integer values pinned by top-level `term == literal` conjuncts.
        // Used to recover the concrete value of an opaque product whose
        // operands become constant under the current assertions (so the UF
        // abstraction does not lose the evaluability that native `*` had once
        // its operands are pinned).
        let mut exact_values: HashMap<Term, i128> = HashMap::new();
        for &assertion in &assertions {
            self.collect_bounds_from_assertion(assertion, &mut bounds, 0);
            self.collect_exact_values(assertion, &mut exact_values, 0);
        }

        // 3. For each product term, attach the SOUND facts we can justify:
        //    (a) an exact-value congruence `product == x*y` when both operands
        //        evaluate to concrete constants (recovers native-mul
        //        evaluability), and
        //    (b) the guarded monotonicity bound when both operands have a
        //        concrete non-negative upper bound.
        let mut emitted = 0usize;
        for (product, x, y) in products {
            if emitted >= MAX_PRODUCT_BOUND_INSTANCES {
                break;
            }

            // (a) Exact-value congruence. If both operands evaluate to concrete
            //     integers under the asserted equalities, the product's value is
            //     fully determined. Asserting `product == vx*vy` is a tautology
            //     given those equalities (the consequent of a true congruence),
            //     so it is sound and restores concrete arithmetic for the UF.
            if let (Some(vx), Some(vy)) = (
                self.eval_term_const(x, &exact_values, 0),
                self.eval_term_const(y, &exact_values, 0),
            ) {
                let exact = BigInt::from(vx) * BigInt::from(vy);
                if self.assert_product_exact_value(product, &exact) {
                    emitted += 1;
                }
                // Exact value subsumes the looser monotonicity bound.
                continue;
            }

            // (b) Guarded monotonicity bound: needs concrete non-negative upper
            //     bounds on both operands.
            let Some(kx) = self.nonneg_upper_bound(x, &bounds) else {
                continue;
            };
            let Some(ky) = self.nonneg_upper_bound(y, &bounds) else {
                continue;
            };

            // kx, ky >= 0 (checked) so the product is a well-defined
            // non-negative constant. Use BigInt to avoid overflow on the fold.
            let product_bound: BigInt = BigInt::from(kx) * BigInt::from(ky);

            if self.assert_one_product_bound(product, x, y, kx, ky, &product_bound) {
                emitted += 1;
            }
        }
        Ok(emitted)
    }

    /// Assert the exact-value fact `product == value` for an opaque product
    /// whose operands are pinned to constants by the current assertions.
    ///
    /// Sound: when `x == vx` and `y == vy` are entailed by the assertions, the
    /// mathematical product `x*y == vx*vy` is a theorem, so `product == vx*vy`
    /// holds in every model consistent with those equalities. (For models where
    /// the operand equalities do *not* hold this fact would be unjustified — but
    /// we only call this when the equalities are present as asserted facts, and
    /// the bare `product == value` fact is then a logical consequence.)
    fn assert_product_exact_value(&mut self, product: Term, value: &BigInt) -> bool {
        if self.solver.get_sort(product) != Sort::Int {
            return false;
        }
        let value_term = self.solver.int_const_bigint(value);
        let eq = self.solver.eq(product, value_term);
        self.solver.assert_term(eq);
        true
    }

    /// Build and assert the guarded lemma for a single product term.
    ///
    /// Asserts:
    ///   `(0 <= x && x <= kx && 0 <= y && y <= ky) ==> product <= kx*ky`
    ///   `(0 <= x && 0 <= y)                        ==> product >= 0`
    ///
    /// Returns `true` if at least the upper-bound lemma was asserted.
    fn assert_one_product_bound(
        &mut self,
        product: Term,
        x: Term,
        y: Term,
        kx: i128,
        ky: i128,
        product_bound: &BigInt,
    ) -> bool {
        // Guard against sort surprises: only operate on Int-sorted terms.
        if self.solver.get_sort(product) != Sort::Int
            || self.solver.get_sort(x) != Sort::Int
            || self.solver.get_sort(y) != Sort::Int
        {
            return false;
        }

        let zero_x = self.solver.int_const(0);
        let zero_y = self.solver.int_const(0);
        let x_ge_0 = self.solver.ge(x, zero_x);
        let y_ge_0 = self.solver.ge(y, zero_y);

        let kx_term = int_const_i128(&mut self.solver, kx);
        let ky_term = int_const_i128(&mut self.solver, ky);
        let x_le_kx = self.solver.le(x, kx_term);
        let y_le_ky = self.solver.le(y, ky_term);

        // antecedent = 0<=x && x<=kx && 0<=y && y<=ky
        let x_part = self.solver.and(x_ge_0, x_le_kx);
        let y_part = self.solver.and(y_ge_0, y_le_ky);
        let antecedent = self.solver.and(x_part, y_part);

        // consequent = product <= kx*ky
        let bound_term = self.solver.int_const_bigint(product_bound);
        let product_le_bound = self.solver.le(product, bound_term);

        let upper_lemma = self.solver.implies(antecedent, product_le_bound);
        self.solver.assert_term(upper_lemma);

        // Non-negativity: (0<=x && 0<=y) ==> product >= 0. Re-derive the
        // `>= 0` literals so we don't reuse terms tied to the upper antecedent
        // (term interning makes this free, but keeps intent explicit).
        let zero_lo = self.solver.int_const(0);
        let x_ge_0b = self.solver.ge(x, zero_lo);
        let zero_lo2 = self.solver.int_const(0);
        let y_ge_0b = self.solver.ge(y, zero_lo2);
        let nonneg_ante = self.solver.and(x_ge_0b, y_ge_0b);
        let zero_rhs = self.solver.int_const(0);
        let product_ge_0 = self.solver.ge(product, zero_rhs);
        let nonneg_lemma = self.solver.implies(nonneg_ante, product_ge_0);
        self.solver.assert_term(nonneg_lemma);

        true
    }

    /// Return a concrete non-negative upper bound for `term` if one is
    /// derivable. Requires `upper >= 0` (a negative upper bound would make the
    /// product-bound fold sign-sensitive; we conservatively skip those — the
    /// lemma stays sound by emitting nothing).
    fn nonneg_upper_bound(&self, term: Term, bounds: &HashMap<Term, IntBounds>) -> Option<i128> {
        // A literal operand is its own bound.
        if let Some(value) = term_i128_literal(&self.solver, term) {
            return if value >= 0 { Some(value) } else { None };
        }
        let entry = bounds.get(&term)?;
        let upper = entry.upper?;
        if upper >= 0 {
            Some(upper)
        } else {
            None
        }
    }

    /// Collect exact integer values pinned by top-level `term == literal`
    /// conjuncts of an asserted fact.
    ///
    /// Same soundness discipline as [`Self::collect_bounds_from_assertion`]:
    /// descend only through `and` conjunctions so every recorded equality is
    /// entailed in *every* model of the current query. An equality recorded
    /// here therefore licenses asserting the exact product value as a logical
    /// consequence.
    fn collect_exact_values(&self, term: Term, values: &mut HashMap<Term, i128>, depth: usize) {
        if depth > MAX_WALK_DEPTH {
            return;
        }
        match self.solver.term_kind(term) {
            TermKind::App { name, num_args: 2 } if name == "and" => {
                for child in self.solver.term_children(term) {
                    self.collect_exact_values(child, values, depth + 1);
                }
            }
            TermKind::App { name, num_args: 2 } if name == "=" => {
                let children = self.solver.term_children(term);
                let [lhs, rhs] = children.as_slice() else {
                    return;
                };
                let lhs = *lhs;
                let rhs = *rhs;
                match (
                    term_i128_literal(&self.solver, lhs),
                    term_i128_literal(&self.solver, rhs),
                ) {
                    // `subject == literal` — pin the subject's value. (When both
                    // sides are literals the equality carries no variable info;
                    // when neither is, there is no constant to record.)
                    (None, Some(v)) => {
                        values.entry(lhs).or_insert(v);
                    }
                    (Some(v), None) => {
                        values.entry(rhs).or_insert(v);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    /// Evaluate `term` to a concrete integer using the pinned `values` map and
    /// literal folding over `+`, `-`, `*`. Returns `None` if any leaf is not a
    /// literal and not pinned.
    ///
    /// This makes the opaque nonlinear-product UF evaluate to the same value
    /// native `*` would once its operands are constant under the assertions —
    /// e.g. `n*(n+1)` with `n == 2` evaluates to `2*3 == 6`.
    fn eval_term_const(
        &self,
        term: Term,
        values: &HashMap<Term, i128>,
        depth: usize,
    ) -> Option<i128> {
        if depth > MAX_WALK_DEPTH {
            return None;
        }
        if self.solver.get_sort(term) != Sort::Int {
            return None;
        }
        // Direct literal.
        if let Some(v) = term_i128_literal(&self.solver, term) {
            return Some(v);
        }
        // Pinned by an asserted equality.
        if let Some(&v) = values.get(&term) {
            return Some(v);
        }
        // Fold arithmetic (including the nonlinear-product UF) over operands
        // that themselves evaluate to constants.
        match self.solver.term_kind(term) {
            TermKind::App { name, num_args: 2 }
                if matches!(name.as_str(), "+" | "-" | "*") || name == NONLINEAR_MUL_UF =>
            {
                let children = self.solver.term_children(term);
                let [lhs, rhs] = children.as_slice() else {
                    return None;
                };
                let lhs = self.eval_term_const(*lhs, values, depth + 1)?;
                let rhs = self.eval_term_const(*rhs, values, depth + 1)?;
                match name.as_str() {
                    "+" => lhs.checked_add(rhs),
                    "-" => lhs.checked_sub(rhs),
                    "*" => lhs.checked_mul(rhs),
                    _ => lhs.checked_mul(rhs), // NONLINEAR_MUL_UF
                }
            }
            _ => None,
        }
    }

    /// Recursively collect bounds implied by an asserted term.
    ///
    /// Only *top-level conjuncts* of an assertion are sound to read as facts:
    /// `a && b` asserted means both `a` and `b` hold, but `a || b` or the
    /// branches of an `ite`/implication do not. We therefore descend only
    /// through `and` (operator `"and"`) and never through disjunctions,
    /// negations, implications, or quantifiers.
    fn collect_bounds_from_assertion(
        &self,
        term: Term,
        bounds: &mut HashMap<Term, IntBounds>,
        depth: usize,
    ) {
        if depth > MAX_WALK_DEPTH {
            return;
        }
        match self.solver.term_kind(term) {
            TermKind::App { name, num_args: 2 } if name == "and" => {
                for child in self.solver.term_children(term) {
                    self.collect_bounds_from_assertion(child, bounds, depth + 1);
                }
            }
            TermKind::App { name, num_args: 2 }
                if matches!(name.as_str(), "<" | "<=" | ">" | ">=") =>
            {
                if let Some((subject, lower, upper)) = self.comparison_bound(&name, term) {
                    let entry = bounds.entry(subject).or_insert_with(IntBounds::empty);
                    if let Some(lo) = lower {
                        entry.tighten_lower(lo);
                    }
                    if let Some(hi) = upper {
                        entry.tighten_upper(hi);
                    }
                }
            }
            _ => {}
        }
    }

    /// Interpret a binary comparison `op` term as a bound on a non-literal
    /// subject term, when the other operand is an integer literal.
    ///
    /// Returns `(subject, lower_bound, upper_bound)` where exactly one of the
    /// bounds is `Some`. The bounds are *inclusive* (strict comparisons against
    /// integer literals are tightened by one).
    fn comparison_bound(&self, op: &str, term: Term) -> Option<(Term, Option<i128>, Option<i128>)> {
        let children = self.solver.term_children(term);
        let [lhs, rhs] = children.as_slice() else {
            return None;
        };
        let lhs = *lhs;
        let rhs = *rhs;
        let lhs_lit = term_i128_literal(&self.solver, lhs);
        let rhs_lit = term_i128_literal(&self.solver, rhs);

        // Only handle `subject OP literal` or `literal OP subject` with exactly
        // one literal side. Both-literal comparisons carry no variable bound.
        match (lhs_lit, rhs_lit) {
            (None, Some(k)) => {
                // subject OP k
                let (lower, upper) = match op {
                    // subject <= k  -> upper = k ; subject < k -> upper = k-1
                    "<=" => (None, Some(k)),
                    "<" => (None, Some(k.checked_sub(1)?)),
                    // subject >= k  -> lower = k ; subject > k -> lower = k+1
                    ">=" => (Some(k), None),
                    ">" => (Some(k.checked_add(1)?), None),
                    _ => return None,
                };
                Some((lhs, lower, upper))
            }
            (Some(k), None) => {
                // k OP subject  (flip the relation)
                let (lower, upper) = match op {
                    // k <= subject -> subject >= k -> lower = k
                    "<=" => (Some(k), None),
                    // k < subject  -> subject > k  -> lower = k+1
                    "<" => (Some(k.checked_add(1)?), None),
                    // k >= subject -> subject <= k -> upper = k
                    ">=" => (None, Some(k)),
                    // k > subject  -> subject < k  -> upper = k-1
                    ">" => (None, Some(k.checked_sub(1)?)),
                    _ => return None,
                };
                Some((rhs, lower, upper))
            }
            _ => None,
        }
    }

    /// Recursively collect distinct nonlinear product terms where neither
    /// operand is an integer literal.
    ///
    /// Matches both the uninterpreted nonlinear-product UF
    /// (`__trust_wp_nonlinear_mul`, the standard encoding for `x*y` with both
    /// operands opaque) and a native `(* x y)` term (defensive: should not
    /// reach the solver for two non-literal operands after the encoder change,
    /// but a bound is still sound and useful if one appears).
    fn collect_products(
        &self,
        term: Term,
        out: &mut Vec<(Term, Term, Term)>,
        seen: &mut std::collections::HashSet<Term>,
        depth: usize,
    ) {
        if depth > MAX_WALK_DEPTH {
            return;
        }
        if let TermKind::App { name, num_args: 2 } = self.solver.term_kind(term) {
            if name == NONLINEAR_MUL_UF || name == "*" {
                let children = self.solver.term_children(term);
                if let [x, y] = children.as_slice() {
                    let x = *x;
                    let y = *y;
                    // Literal*anything folds in the linear solver already; the
                    // lemma is only useful when both operands are opaque.
                    let x_lit = term_i128_literal(&self.solver, x).is_some();
                    let y_lit = term_i128_literal(&self.solver, y).is_some();
                    if !x_lit && !y_lit && seen.insert(term) {
                        out.push((term, x, y));
                    }
                }
            }
        }
        for child in self.solver.term_children(term) {
            self.collect_products(child, out, seen, depth + 1);
        }
    }
}

/// Build an Int constant term for an `i128` value (the solver API takes `i64`
/// or `&BigInt`; route large magnitudes through `BigInt`).
fn int_const_i128(solver: &mut ay_dpll::api::Solver, value: i128) -> Term {
    if let Ok(v) = i64::try_from(value) {
        solver.int_const(v)
    } else {
        solver.int_const_bigint(&BigInt::from(value))
    }
}

/// Extract an `i128` literal value from an Int-sorted constant term, including
/// the SMT prefix-negation form `(- N)`. Returns `None` for non-literals or
/// magnitudes that exceed `i128`.
fn term_i128_literal(solver: &ay_dpll::api::Solver, term: Term) -> Option<i128> {
    if solver.get_sort(term) != Sort::Int {
        return None;
    }
    match solver.term_kind(term) {
        TermKind::Const => {
            let rendered = solver.format_term(term);
            let value: BigInt = if let Ok(v) = rendered.parse::<BigInt>() {
                v
            } else {
                let inner = rendered
                    .strip_prefix("(- ")
                    .and_then(|s| s.strip_suffix(')'))?;
                -inner.trim().parse::<BigInt>().ok()?
            };
            bigint_to_i128(&value)
        }
        // Constant-folded arithmetic over literals: `(+ a b)`, `(- a b)`,
        // `(* a b)` where both sides are literals. Mirrors the encoder's
        // `term_int_literal_for_arithmetic` so e.g. `1000*1000` reads as a
        // literal if it appears pre-folded.
        TermKind::App { name, num_args: 2 } if matches!(name.as_str(), "+" | "-" | "*") => {
            let children = solver.term_children(term);
            let [lhs, rhs] = children.as_slice() else {
                return None;
            };
            let lhs = term_i128_literal(solver, *lhs)?;
            let rhs = term_i128_literal(solver, *rhs)?;
            match name.as_str() {
                "+" => lhs.checked_add(rhs),
                "-" => lhs.checked_sub(rhs),
                "*" => lhs.checked_mul(rhs),
                _ => None,
            }
        }
        _ => None,
    }
}

fn bigint_to_i128(value: &BigInt) -> Option<i128> {
    value.to_i128()
}
