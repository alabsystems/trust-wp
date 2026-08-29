// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Internal whole-borrow function symbols for `MutRef` carrier sorts. (#2141)
//!
//! The `ExprSort::MutRef` carrier sort stays an uninterpreted SMT sort. This
//! helper layers deterministic constructor/accessor UFs on top so whole-borrow
//! equality can observe the `(current, final, id)` components without changing
//! the existing sort plumbing.

use ay_dpll::api::{FuncDecl, Sort, Term};
use trust_wp_core::formula::ExprSort;

use super::AYEncoder;
use crate::error::EncodingError;

#[derive(Clone)]
struct MutRefUfSet {
    constructor: FuncDecl,
    current: FuncDecl,
    final_val: FuncDecl,
    id: FuncDecl,
}

fn fnv_suffix(seed: &str) -> String {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64;
    for byte in seed.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    format!("{hash:016x}")
}

fn mut_ref_symbol_suffix(whole_sort: &Sort) -> String {
    fnv_suffix(&format!("{whole_sort:?}"))
}

impl AYEncoder {
    fn ensure_mut_ref_uf_set(&mut self, whole_sort: &Sort, inner_sort: &Sort) -> MutRefUfSet {
        let suffix = mut_ref_symbol_suffix(whole_sort);
        let constructor = self.get_or_declare_logic_func(
            &format!("__trust_wp_mk_mut_ref_{suffix}"),
            &[inner_sort.clone(), inner_sort.clone(), Sort::Int],
            whole_sort.clone(),
        );
        let current = self.get_or_declare_logic_func(
            &format!("__trust_wp_mut_ref_current_{suffix}"),
            std::slice::from_ref(whole_sort),
            inner_sort.clone(),
        );
        let final_val = self.get_or_declare_logic_func(
            &format!("__trust_wp_mut_ref_final_{suffix}"),
            std::slice::from_ref(whole_sort),
            inner_sort.clone(),
        );
        let id = self.get_or_declare_logic_func(
            &format!("__trust_wp_mut_ref_id_{suffix}"),
            std::slice::from_ref(whole_sort),
            Sort::Int,
        );
        MutRefUfSet {
            constructor,
            current,
            final_val,
            id,
        }
    }

    pub(crate) fn bind_whole_mut_ref(
        &mut self,
        whole_sort: &Sort,
        inner_sort: &Sort,
        whole_term: Term,
        current_term: Term,
        final_term: Term,
        id_term: Term,
    ) -> Result<(), EncodingError> {
        // Self-correct carrier depth: when the whole_term's actual sort differs
        // from the annotation-derived whole_sort, use the actual sort and derive
        // the correct inner sort. This handles nested mutable-reference types
        // like `&mut &mut T` where the annotation-derived whole_sort may assume
        // one nesting depth while the pre-declared term sits at another. (#2585)
        let actual_whole_sort = self.solver.get_sort(whole_term);
        let (whole_sort, inner_sort) = if &actual_whole_sort == whole_sort {
            (whole_sort.clone(), inner_sort.clone())
        } else {
            // Derive inner sort from the actual whole sort.
            if let Some(trust_wp_core::formula::ExprSort::MutRef(actual_inner)) =
                crate::encoder::sort_context::ay_sort_to_expr_sort(&actual_whole_sort)
            {
                let corrected_inner = self.sort_from_expr_sort((*actual_inner).clone());
                // Verify current/final terms match the corrected inner sort.
                if self.solver.get_sort(current_term) != corrected_inner
                    || self.solver.get_sort(final_term) != corrected_inner
                {
                    return Ok(());
                }
                (actual_whole_sort.clone(), corrected_inner)
            } else {
                return Ok(());
            }
        };
        let whole_sort = &whole_sort;
        let inner_sort = &inner_sort;
        let ufs = self.ensure_mut_ref_uf_set(whole_sort, inner_sort);

        let ctor_term = self.safe_apply(
            "mut-ref constructor",
            &ufs.constructor,
            &[current_term, final_term, id_term],
        )?;
        self.assert_eq(whole_term, ctor_term);

        let current_proj =
            self.safe_apply("mut-ref current selector", &ufs.current, &[whole_term])?;
        self.assert_eq(current_proj, current_term);

        let final_proj =
            self.safe_apply("mut-ref final selector", &ufs.final_val, &[whole_term])?;
        self.assert_eq(final_proj, final_term);

        let id_proj = self.safe_apply("mut-ref id selector", &ufs.id, &[whole_term])?;
        self.assert_eq(id_proj, id_term);

        Ok(())
    }

    /// Whether `term` carries a `MutRef` (mutable-reference) carrier sort.
    pub(crate) fn is_mut_ref_sorted(&self, term: Term) -> bool {
        matches!(
            crate::encoder::sort_context::ay_sort_to_expr_sort(&self.solver.get_sort(term)),
            Some(ExprSort::MutRef(_))
        )
    }

    /// Project the `current` (Deref) or `final` (Final) component out of a
    /// `MutRef`-sorted carrier term, returning the inner-sorted value via the
    /// definitional accessor UF (`mut_ref_current` / `mut_ref_final`).
    ///
    /// Returns `None` when `term` is not `MutRef`-sorted. SOUND: the accessor
    /// UFs are the definitional projections of the `(current, final, id)`
    /// constructor (see `bind_whole_mut_ref`), so `mut_ref_final(r)` *is* `^r`
    /// and `mut_ref_current(r)` *is* `*r` — using them is exact, never an
    /// over- or under-approximation. (#nested-mutref final/current projection)
    pub(crate) fn mut_ref_component_projection(
        &mut self,
        term: Term,
        want_final: bool,
    ) -> Result<Option<Term>, EncodingError> {
        let whole_sort = self.solver.get_sort(term);
        let Some(ExprSort::MutRef(inner)) =
            crate::encoder::sort_context::ay_sort_to_expr_sort(&whole_sort)
        else {
            return Ok(None);
        };
        let inner_sort = self.sort_from_expr_sort((*inner).clone());
        let ufs = self.ensure_mut_ref_uf_set(&whole_sort, &inner_sort);
        let accessor = if want_final {
            &ufs.final_val
        } else {
            &ufs.current
        };
        let label = if want_final {
            "mut-ref final selector"
        } else {
            "mut-ref current selector"
        };
        let projected = self.safe_apply(label, accessor, &[term])?;
        Ok(Some(projected))
    }

    pub(crate) fn try_decompose_mut_ref_equality(
        &mut self,
        lhs: Term,
        rhs: Term,
    ) -> Result<Option<Term>, EncodingError> {
        let whole_sort = self.solver.get_sort(lhs);
        if self.solver.get_sort(rhs) != whole_sort {
            return Ok(None);
        }
        let Some(ExprSort::MutRef(inner)) =
            crate::encoder::sort_context::ay_sort_to_expr_sort(&whole_sort)
        else {
            return Ok(None);
        };

        let inner_sort = self.sort_from_expr_sort((*inner).clone());
        let ufs = self.ensure_mut_ref_uf_set(&whole_sort, &inner_sort);

        let lhs_current = self.safe_apply("mut-ref current selector", &ufs.current, &[lhs])?;
        let rhs_current = self.safe_apply("mut-ref current selector", &ufs.current, &[rhs])?;
        let lhs_final = self.safe_apply("mut-ref final selector", &ufs.final_val, &[lhs])?;
        let rhs_final = self.safe_apply("mut-ref final selector", &ufs.final_val, &[rhs])?;
        let lhs_id = self.safe_apply("mut-ref id selector", &ufs.id, &[lhs])?;
        let rhs_id = self.safe_apply("mut-ref id selector", &ufs.id, &[rhs])?;

        let current_eq = self.eq_or_iff(lhs_current, rhs_current, &inner_sort);
        let final_eq = self.eq_or_iff(lhs_final, rhs_final, &inner_sort);
        let id_eq = self.eq_term(lhs_id, rhs_id);
        let current_and_final = self.solver.and(current_eq, final_eq);
        Ok(Some(self.solver.and(current_and_final, id_eq)))
    }

    /// Whole-carrier equality for two `MutRef`-sorted terms, when both sides
    /// carry the same carrier sort.
    ///
    /// This is the *carrier-level* counterpart of
    /// [`Self::try_decompose_mut_ref_equality`]: where that expands `a == b`
    /// into the `(current, final, id)` componentwise conjunction `C`, this
    /// returns the single literal `W := (= a b)`.
    ///
    /// SOUNDNESS — `W` entails `C` unconditionally. `current`, `final` and `id`
    /// are ordinary uninterpreted function symbols, so congruence gives
    /// `a == b ==> current(a) == current(b)` (likewise `final`, `id`) with no
    /// extra axioms required. A refutation of `base /\ ~W` therefore
    /// establishes `base |= W`, hence `base |= C` — the componentwise
    /// postcondition the mut-borrow path actually asserts.
    ///
    /// It is also *conservative*: since `W ==> C`, we have `~C ==> ~W`, so
    /// `~W` is the WEAKER assumption and `base /\ ~W` is the strictly harder
    /// query to refute. A goal that only holds componentwise (because one side
    /// lacks the `mk` reconstruction axiom that
    /// [`Self::bind_whole_mut_ref`] emits) simply fails to close here, leaving
    /// the caller's existing verdict untouched. Nothing is accepted that the
    /// componentwise query would have rejected.
    ///
    /// Used to obtain a *certifiable* proof of an obligation that ay refutes
    /// but cannot emit structured Alethe steps for: the componentwise negated
    /// goal is a disjunction of >=2 disequalities, each closed by its own
    /// transitivity chain, and ay's proof producer collapses that case split
    /// into a single `hole` step (making the certificate non-strict, so the
    /// mandatory authority gate demotes it). The carrier-level goal closes by
    /// `eq_congruent` + `eq_transitive` + `resolution`, which the strict
    /// checker — and carcara — accept.
    pub(crate) fn try_mut_ref_carrier_equality(&mut self, lhs: Term, rhs: Term) -> Option<Term> {
        let whole_sort = self.solver.get_sort(lhs);
        if self.solver.get_sort(rhs) != whole_sort {
            return None;
        }
        if !matches!(
            crate::encoder::sort_context::ay_sort_to_expr_sort(&whole_sort),
            Some(ExprSort::MutRef(_))
        ) {
            return None;
        }
        Some(self.eq_term(lhs, rhs))
    }
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::{SolveResult, Sort};
    use ntest::timeout;
    use trust_wp_core::formula::ExprSort;

    use super::*;

    #[test]
    #[timeout(30000)]
    fn equal_components_force_whole_mut_ref_equality() {
        let mut encoder = AYEncoder::new_all();
        let whole_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));

        let lhs = encoder
            .get_or_declare_var("lhs", whole_sort.clone())
            .expect("lhs should declare");
        let rhs = encoder
            .get_or_declare_var("rhs", whole_sort.clone())
            .expect("rhs should declare");

        let lhs_current = encoder
            .get_or_declare_var("lhs_current", Sort::Int)
            .expect("lhs_current should declare");
        let lhs_final = encoder
            .get_or_declare_var("lhs_final", Sort::Int)
            .expect("lhs_final should declare");
        let lhs_id = encoder
            .get_or_declare_var("lhs_id", Sort::Int)
            .expect("lhs_id should declare");

        let rhs_current = encoder
            .get_or_declare_var("rhs_current", Sort::Int)
            .expect("rhs_current should declare");
        let rhs_final = encoder
            .get_or_declare_var("rhs_final", Sort::Int)
            .expect("rhs_final should declare");
        let rhs_id = encoder
            .get_or_declare_var("rhs_id", Sort::Int)
            .expect("rhs_id should declare");

        encoder
            .bind_whole_mut_ref(&whole_sort, &Sort::Int, lhs, lhs_current, lhs_final, lhs_id)
            .expect("lhs whole mutref binding should encode");
        encoder
            .bind_whole_mut_ref(&whole_sort, &Sort::Int, rhs, rhs_current, rhs_final, rhs_id)
            .expect("rhs whole mutref binding should encode");

        encoder.assert_eq(lhs_current, rhs_current);
        encoder.assert_eq(lhs_final, rhs_final);
        encoder.assert_eq(lhs_id, rhs_id);

        let whole_eq = encoder.eq_term(lhs, rhs);
        let neq_whole = encoder.solver.not(whole_eq);
        encoder.assert_term(neq_whole);

        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "equal current/final/id components should force whole MutRef equality"
        );
    }

    /// The carrier-level equality returned by `try_mut_ref_carrier_equality`
    /// ENTAILS the componentwise conjunction that
    /// `try_decompose_mut_ref_equality` builds.
    ///
    /// This is the soundness property the mut-borrow carrier-certificate path
    /// relies on: it proves the carrier goal and reports the componentwise
    /// postcondition proved. Note the entailment needs NO `bind_whole_mut_ref`
    /// reconstruction axiom — plain congruence on the selector UFs suffices —
    /// which is why the substitution is sound even for an opaque carrier.
    #[test]
    #[timeout(30000)]
    fn carrier_equality_entails_componentwise_equality() {
        let mut encoder = AYEncoder::new_all();
        let whole_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));

        let lhs = encoder
            .get_or_declare_var("lhs", whole_sort.clone())
            .expect("lhs should declare");
        let rhs = encoder
            .get_or_declare_var("rhs", whole_sort)
            .expect("rhs should declare");

        // Deliberately NO `bind_whole_mut_ref`: the carriers stay opaque.
        let carrier_eq = encoder
            .try_mut_ref_carrier_equality(lhs, rhs)
            .expect("MutRef-sorted operands should yield a carrier equality");
        encoder.assert_term(carrier_eq);

        let componentwise = encoder
            .try_decompose_mut_ref_equality(lhs, rhs)
            .expect("decomposition should encode")
            .expect("MutRef-sorted operands should decompose");
        let negated_componentwise = encoder.solver.not(componentwise);
        encoder.assert_term(negated_componentwise);

        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "carrier equality must entail the componentwise (current, final, id) \
             conjunction, with no reconstruction axiom required"
        );
    }

    /// `try_mut_ref_carrier_equality` refuses operands that are not a `MutRef`
    /// carrier, so the certificate path cannot fire on an unrelated sort.
    #[test]
    #[timeout(30000)]
    fn carrier_equality_refuses_non_mut_ref_sorts() {
        let mut encoder = AYEncoder::new_all();
        let lhs = encoder
            .get_or_declare_var("plain_lhs", Sort::Int)
            .expect("lhs should declare");
        let rhs = encoder
            .get_or_declare_var("plain_rhs", Sort::Int)
            .expect("rhs should declare");

        assert!(
            encoder.try_mut_ref_carrier_equality(lhs, rhs).is_none(),
            "Int-sorted operands must not produce a MutRef carrier equality"
        );
    }

    /// Regression: the nested mut-ref final projection (`mut_ref_component_projection`)
    /// plus the call-site aliasing (dest pre-state inner ref == caller `*x`) makes the
    /// `inferred_invariants::nested_borrows` postcondition `^*x == 1` provable (UNSAT
    /// of its negation). Mirrors the function_contract VC at the carrier level.
    #[test]
    #[timeout(30000)]
    fn nested_mut_ref_final_projection_closes_postcondition() {
        // Minimal nested_borrows function_contract VC for `^*x == 1`.
        let mut e = AYEncoder::new_all();
        let mr = e.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
        let decl = |e: &mut AYEncoder, n: &str, s: Sort| e.get_or_declare_var(n, s).unwrap();

        let x_current = decl(&mut e, "x_current", mr.clone());
        let x_final = decl(&mut e, "x_final", mr.clone());
        let arg0_current = decl(&mut e, "arg0_current", mr.clone());
        let arg0_final = decl(&mut e, "arg0_final", mr.clone());
        let arg1 = decl(&mut e, "arg1", mr.clone());
        let b = decl(&mut e, "b", mr.clone());
        let b_current = decl(&mut e, "b_current", Sort::Int);
        let b_final = decl(&mut e, "b_final", Sort::Int);
        let b_id = decl(&mut e, "b_id", Sort::Int);
        let x_current_current = decl(&mut e, "x_current_current", Sort::Int);

        // precond **x == 0
        let zero = e.solver.int_const(0);
        e.assert_eq(zero, x_current_current);
        // x_final == x_current
        e.assert_eq(x_final, x_current);
        // x_current_current == mut_ref_current(x_current)
        let xcc_proj = e
            .mut_ref_component_projection(x_current, false)
            .unwrap()
            .unwrap();
        e.assert_eq(x_current_current, xcc_proj);
        // mem::replace effects
        let bc = e.mut_ref_component_projection(b, false).unwrap().unwrap();
        let a0c_c = e
            .mut_ref_component_projection(arg0_current, false)
            .unwrap()
            .unwrap();
        e.assert_eq(bc, a0c_c); // mut_ref_current(b) == mut_ref_current(arg0_current)
        let bf = e.mut_ref_component_projection(b, true).unwrap().unwrap();
        let a0c_f = e
            .mut_ref_component_projection(arg0_current, true)
            .unwrap()
            .unwrap();
        e.assert_eq(bf, a0c_f);
        let a0f_f = e
            .mut_ref_component_projection(arg0_final, true)
            .unwrap()
            .unwrap();
        let a1_f = e.mut_ref_component_projection(arg1, true).unwrap().unwrap();
        e.assert_eq(a0f_f, a1_f);
        // b == mk(b_current, b_final, b_id); *b += 1
        e.bind_whole_mut_ref(&mr, &Sort::Int, b, b_current, b_final, b_id)
            .unwrap();
        let one = e.solver.int_const(1);
        let bc1 = e.solver.add(b_current, one);
        e.assert_eq(b_final, bc1);

        // ALIAS (Lean-validated): arg0_current == x_current
        e.assert_eq(arg0_current, x_current);

        // negated goal: not (mut_ref_final(x_final) == 1)
        let goal_lhs = e
            .mut_ref_component_projection(x_final, true)
            .unwrap()
            .unwrap();
        let one2 = e.solver.int_const(1);
        let goal = e.eq_term(goal_lhs, one2);
        let neg = e.solver.not(goal);
        e.assert_term(neg);

        let res = e.check_sat();
        assert!(
            matches!(res, SolveResult::Unsat(_)),
            "alias should close goal, got {res:?}"
        );
    }

    /// bug/682 probe: the proof_assert call-precondition slice as ACTUALLY
    /// encoded today. The negated goal is `not (call_2 <= IMAX)` where `call_2`
    /// (the pre-call value `*a` passed to `add_some`) is DECLARED but bound by
    /// NO assumption (the driver's retain_non_entry_pinning filter dropped both
    /// `call_2 == a_current` and `call_2 == a_final`). With `call_2` free this
    /// is genuinely SAT, so ay correctly returns NOT-Unsat. This is the real
    /// blocker — proving it would be an unsound false-accept.
    #[test]
    #[timeout(30000)]
    fn bug682_call_obligation_with_free_call_arg_is_not_unsat() {
        let mut e = AYEncoder::new_all();
        let imax = e.solver.int_const(9_223_372_036_854_775_807);
        let three = e.solver.int_const(3);
        let a_current = e.get_or_declare_var("a_current", Sort::Int).unwrap();
        let a_final = e.get_or_declare_var("a_final", Sort::Int).unwrap();
        let a_p = e.get_or_declare_var("a_p", Sort::Int).unwrap();
        let call_2 = e.get_or_declare_var("call_2", Sort::Int).unwrap();
        // Assumptions present in the real replay.
        let f0 = e.eq_term(a_current, three);
        e.assert_term(f0); // a_current = 3
        let f1 = e.eq_term(a_current, a_p);
        e.assert_term(f1); // a_current = a_p
        let f3 = e.solver.lt(a_current, a_final);
        e.assert_term(f3); // a_current < a_final
                           // Negated goal: not (call_2 <= IMAX). call_2 is otherwise free.
        let goal = e.solver.le(call_2, imax);
        let neg = e.solver.not(goal);
        e.assert_term(neg);
        let res = e.check_sat();
        assert!(
            !matches!(res, SolveResult::Unsat(_)),
            "free call_2 must NOT be provable (would be a false-accept), got {res:?}"
        );
    }

    // ------------------------------------------------------------------
    // #prophecy-slots M0 kill-gate (Fix B, fixb-prophecy-slots-design §C M0).
    //
    // Probes the REPRESENTATION only: an Option datatype whose `Some` field
    // sort is the `__trust_wp_mutref::int` carrier record, a carrier bound
    // via `bind_whole_mut_ref`, read back THROUGH the native datatype
    // selector, projected with the definitional accessor UFs. The campaign
    // is only viable if ay congruence-closes
    //   mut_ref_current(sel(Some(r))) == r_cur
    // (this exact composition — native DT selector ranging over
    // `__trust_wp_mutref::*` — is what broke closures/09 and needed ay
    // 18483d1f). A failure here REFUTES the record-in-field lowering.
    // ------------------------------------------------------------------

    /// Shared M0 fixture: declare `Option<__trust_wp_mutref::int>`, bind a
    /// carrier `r` = mk(cur, fin, id), build `Some(r)` and read the payload
    /// back through the NATIVE datatype selector. Returns the selector term.
    fn m0_option_mutref_selector_payload(
        e: &mut AYEncoder,
        var: &str,
        cur: i64,
        fin: i64,
        id: i64,
    ) -> ay_dpll::api::Term {
        let mr = e.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
        let dt = crate::encoder::match_enc::stdlib_option_datatype_for_payload(mr.clone());
        e.ensure_datatype_declared(&dt);
        // ensure_datatype_declared silently falls back to an opaque sort when
        // the solver rejects the declaration (#2706); that fallback would
        // nullify the probe, so make it loud.
        assert!(
            e.has_datatype_decl(&dt.name),
            "M0 REFUTED at declaration: solver rejected the Option<mutref> datatype '{}'",
            dt.name
        );

        let r = e.get_or_declare_var(var, mr.clone()).unwrap();
        let cur_t = e.solver.int_const(cur);
        let fin_t = e.solver.int_const(fin);
        let id_t = e.solver.int_const(id);
        e.bind_whole_mut_ref(&mr, &Sort::Int, r, cur_t, fin_t, id_t)
            .expect("whole mutref binding should encode");

        let some_name = crate::encoder::match_enc::datatype_constructor_name(&dt, "Some");
        let res = e
            .solver
            .try_datatype_constructor(&dt, &some_name, &[r])
            .expect("Some(r) with a mutref-sorted payload should construct");
        let (sel_name, sel_sort) = AYEncoder::constructor_payload_selector(&dt, "Some")
            .expect("Option Some payload selector should exist");
        let sel_sort = sel_sort.clone();
        let sel_name = sel_name.to_string();
        e.solver
            .try_datatype_selector(&sel_name, res, sel_sort)
            .expect("native selector over a mutref-sorted field should build")
    }

    /// M0 primary: `mut_ref_current(sel(Some(r))) == r_cur` and
    /// `mut_ref_final(sel(Some(r))) == r_fin` must close — the negation is
    /// UNSAT. PASS = campaign representation viable; FAIL = kill-gate fired.
    #[test]
    #[timeout(30000)]
    fn m0_option_mutref_selector_projection_closes() {
        let mut e = AYEncoder::new_all();
        let t = m0_option_mutref_selector_payload(&mut e, "r", 3, 7, 1);

        let cur_proj = e
            .mut_ref_component_projection(t, false)
            .unwrap()
            .expect("selector payload must be MutRef-sorted");
        let fin_proj = e
            .mut_ref_component_projection(t, true)
            .unwrap()
            .expect("selector payload must be MutRef-sorted");
        let three = e.solver.int_const(3);
        let seven = e.solver.int_const(7);
        let cur_eq = e.eq_term(cur_proj, three);
        let fin_eq = e.eq_term(fin_proj, seven);
        let goal = e.solver.and(cur_eq, fin_eq);
        let neg = e.solver.not(goal);
        e.assert_term(neg);

        let res = e.check_sat();
        assert!(
            matches!(res, SolveResult::Unsat(_)),
            "M0 KILL-GATE FIRED: mut_ref_current/final(sel(Some(r))) failed to \
             congruence-close to the bound components, got {res:?}"
        );
    }

    /// M0 vacuity control: the SAME premise set with the goal asserted
    /// POSITIVELY must be SAT. Guards against the primary probe passing
    /// vacuously off an inconsistent base (the take_first_mut lesson: a
    /// fabricated-contradiction base proves everything).
    #[test]
    #[timeout(30000)]
    fn m0_option_mutref_selector_projection_base_consistent() {
        let mut e = AYEncoder::new_all();
        let t = m0_option_mutref_selector_payload(&mut e, "r", 3, 7, 1);

        let cur_proj = e
            .mut_ref_component_projection(t, false)
            .unwrap()
            .expect("selector payload must be MutRef-sorted");
        let fin_proj = e
            .mut_ref_component_projection(t, true)
            .unwrap()
            .expect("selector payload must be MutRef-sorted");
        let three = e.solver.int_const(3);
        let seven = e.solver.int_const(7);
        e.assert_eq(cur_proj, three);
        e.assert_eq(fin_proj, seven);

        let res = e.check_sat();
        assert!(
            matches!(res, SolveResult::Sat),
            "M0 CONTROL FAILED: the base + positive goal must be consistent, got {res:?}"
        );
    }

    /// M0 separability: two carriers with DISTINCT ids read back through the
    /// selector must not be conflatable — asserting `sel(Some(r)) ==
    /// sel(Some(r2))` with id 1 vs 2 must be UNSAT (id-selector congruence
    /// forces 1 == 2). This is the bug/869 id-distinctness invariant at the
    /// payload level. (Blueprint step 5, stated there with a garbled double
    /// negation; the intent "ids must keep them separable" is this check.)
    #[test]
    #[timeout(30000)]
    fn m0_option_mutref_distinct_ids_keep_carriers_separable() {
        let mut e = AYEncoder::new_all();
        let t1 = m0_option_mutref_selector_payload(&mut e, "r", 3, 7, 1);
        let t2 = m0_option_mutref_selector_payload(&mut e, "r2", 3, 7, 2);

        let conflate = e.eq_term(t1, t2);
        e.assert_term(conflate);
        let res = e.check_sat();
        assert!(
            matches!(res, SolveResult::Unsat(_)),
            "M0 SEPARABILITY FAILED: distinct-id carriers were conflatable \
             through the selector, got {res:?}"
        );
    }

    /// M0 separability control: the two-carrier base WITHOUT the conflation
    /// assertion is SAT (so the UNSAT above is attributable to the id clash,
    /// not to an inconsistent base).
    #[test]
    #[timeout(30000)]
    fn m0_option_mutref_distinct_ids_control_sat() {
        let mut e = AYEncoder::new_all();
        let _t1 = m0_option_mutref_selector_payload(&mut e, "r", 3, 7, 1);
        let _t2 = m0_option_mutref_selector_payload(&mut e, "r2", 3, 7, 2);
        let res = e.check_sat();
        assert!(
            matches!(res, SolveResult::Sat),
            "M0 SEPARABILITY CONTROL FAILED: two-carrier base must be SAT, got {res:?}"
        );
    }

    /// M0 secondary check 1 (blueprint §A.4 / §C): the `ambiguous_stdlib_option`
    /// guard (pattern_condition/bindings.rs) forces the `spec_unwrap : … → Int`
    /// UF fallback when >1 Option* datatype declares a constructor literally
    /// named "Some" — which would silently nullify the whole mechanism. The
    /// carrier family must therefore mint a SPECIALIZED constructor name
    /// (`Option…__Some`), keeping the "Some"-named census at exactly the
    /// OptionInt entry even with both families declared.
    #[test]
    #[timeout(30000)]
    fn m0_carrier_option_family_does_not_trip_ambiguous_stdlib_option() {
        let mut e = AYEncoder::new_all();
        // Declare plain OptionInt first (the common in-scope companion).
        let opt_int = crate::encoder::match_enc::SwitchTarget::OptionInt.datatype();
        e.ensure_datatype_declared(&opt_int);
        // Then the carrier family.
        let mr = e.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
        let dt = crate::encoder::match_enc::stdlib_option_datatype_for_payload(mr);
        e.ensure_datatype_declared(&dt);
        assert!(e.has_datatype_decl(&dt.name));
        assert_ne!(dt.name, "OptionInt");

        let some_name = crate::encoder::match_enc::datatype_constructor_name(&dt, "Some");
        assert_eq!(
            some_name,
            format!("{}__Some", dt.name),
            "carrier Option family must specialize its Some constructor name"
        );
        // M1 LANDED (#prophecy-slots): the ambiguity census now counts
        // LITERAL "Some" constructor names only
        // (`stdlib_option_some_literally_ambiguous`) — the carrier family's
        // constructor is `{family}__Some`, so the guard no longer trips and
        // the native-selector lane stays trusted. Pin flipped from
        // `assert!(ambiguous)` (the M0 retire-on-signal form) per the M0
        // instruction.
        assert!(
            !e.stdlib_option_some_literally_ambiguous(),
            "carrier-family constructor names are specialized ({{family}}__Some); \
             the literal-collision census must NOT count them"
        );
        // The reverse index still carries the LOGICAL "Some" alias for
        // constructor->datatype lookup — that is a lookup aid, not a
        // solver-level name collision. Pin the distinction.
        let alias_hits = e
            .datatypes_for_constructor("Some")
            .filter(|c| c.name.starts_with("Option"))
            .count();
        assert!(
            alias_hits > 1,
            "logical-alias lookup must still find both Option families, got {alias_hits}"
        );
        // A LITERAL collision (a second Option* family whose constructor is
        // literally named "Some") must still trip the guard — the census is
        // narrowed, not removed.
        let colliding = ay_dpll::api::DatatypeSort {
            name: "OptionColliding".to_string(),
            constructors: vec![
                ay_dpll::api::DatatypeConstructor {
                    name: "None_colliding".to_string(),
                    fields: vec![],
                },
                ay_dpll::api::DatatypeConstructor {
                    name: "Some".to_string(),
                    fields: vec![ay_dpll::api::DatatypeField {
                        name: "optioncolliding_some_value".to_string(),
                        sort: Sort::Bool,
                    }],
                },
            ],
        };
        e.ensure_datatype_declared(&colliding);
        assert!(
            e.stdlib_option_some_literally_ambiguous(),
            "a literal 'Some' constructor collision must still trip the guard"
        );
    }

    /// #prophecy-slots M1: an instantiation-suffixed `Option<&mut i32>`
    /// annotation resolves to the specialized carrier Option family — the
    /// `Some` payload field sits at the `__trust_wp_mutref::int` record sort
    /// and the constructor name is specialized (`{family}__Some`).
    #[test]
    #[timeout(30000)]
    fn m1_option_mutref_annotation_resolves_to_carrier_family() {
        use trust_wp_core::formula::intern_sort_name;
        let mut e = AYEncoder::new_all();
        let payload = ExprSort::MutRef(Box::new(ExprSort::Int));
        let name = crate::encoder::sort_context::sort_mapping::mutref_instantiated_option_name(
            "std::option::Option",
            &payload,
        );
        assert_eq!(name, "std::option::Option__twpm0_mutref_int");

        let resolved = e.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name(&name)));
        let Sort::Datatype(dt) = resolved else {
            panic!(
                "suffixed Option annotation must resolve to a native datatype, got {resolved:?}"
            );
        };
        let mr = e.sort_from_expr_sort(payload.clone());
        let expected = crate::encoder::match_enc::stdlib_option_datatype_for_payload(mr.clone());
        assert_eq!(dt.name, expected.name, "both routes must mint ONE family");
        assert!(e.has_datatype_decl(&dt.name), "family must be declared");
        let some_name = crate::encoder::match_enc::datatype_constructor_name(&dt, "Some");
        assert_eq!(some_name, format!("{}__Some", dt.name));
        let (_, sel_sort) =
            AYEncoder::constructor_payload_selector(&dt, "Some").expect("Some payload selector");
        assert_eq!(
            sel_sort, &mr,
            "the Some payload field must sit at the mutref record sort"
        );

        // The stateless lane agrees on the family name (declaration-free).
        let pure = crate::encoder::sort_context::sort_mapping::expr_sort_to_ay_sort(
            &ExprSort::Datatype(intern_sort_name(&name)),
        );
        assert_eq!(pure, Sort::Uninterpreted(dt.name.clone()));
    }

    /// #prophecy-slots M1: the wrapper Phase-1 projection arm. For a
    /// quantifier-bound MutRef-SORTED binder, `*r` and `^r` encode as the
    /// definitional accessor applications (`mut_ref_current`/`mut_ref_final`)
    /// — inner-sorted, distinct, and congruence-connected to the bound
    /// components — never the raw carrier (which would reinstate `*r == ^r`
    /// at the carrier level: the take_first_mut inversion one sort up).
    #[test]
    #[timeout(30000)]
    fn m1_projection_arm_splits_bound_carrier_wrappers() {
        use std::sync::Arc;

        use trust_wp_core::formula::PureExpr;
        let mut e = AYEncoder::new_all();
        let mr = e.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
        let r = e.get_or_declare_var("r", mr.clone()).unwrap();
        let three = e.solver.int_const(3);
        let seven = e.solver.int_const(7);
        let one = e.solver.int_const(1);
        e.bind_whole_mut_ref(&mr, &Sort::Int, r, three, seven, one)
            .expect("whole mutref binding should encode");
        e.bind_quantifier_var("r".to_string());
        e.bind_match_binder_var("r".to_string());

        let var = || PureExpr::Var("r".to_string(), None);
        let deref_t = e
            .encode_pure(&PureExpr::Deref(Arc::new(var())))
            .expect("`*r` must encode via the projection arm");
        let final_t = e
            .encode_pure(&PureExpr::Final(Arc::new(var())))
            .expect("`^r` must encode via the projection arm");

        // Projections are inner-sorted (Int), NOT the carrier record sort.
        assert_eq!(e.solver.get_sort(deref_t), Sort::Int);
        assert_eq!(e.solver.get_sort(final_t), Sort::Int);

        // They are the definitional accessors: ¬(*r == 3 ∧ ^r == 7) is UNSAT.
        let cur_eq = e.eq_term(deref_t, three);
        let fin_eq = e.eq_term(final_t, seven);
        let both = e.solver.and(cur_eq, fin_eq);
        let neg = e.solver.not(both);
        e.assert_term(neg);
        let res = e.check_sat();
        assert!(
            matches!(res, SolveResult::Unsat(_)),
            "projection arm must connect *r/^r to the bound components, got {res:?}"
        );
    }

    /// #prophecy-slots M1 anti-conflation control: with distinct bound
    /// components, asserting `*r == ^r` must be UNSAT (3 == 7) — proving the
    /// two wrapper directions no longer alias — while the positive base is
    /// SAT (consistency control for the UNSAT above).
    #[test]
    #[timeout(30000)]
    fn m1_projection_arm_deref_final_do_not_alias() {
        use std::sync::Arc;

        use trust_wp_core::formula::PureExpr;
        let mut e = AYEncoder::new_all();
        let mr = e.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
        let r = e.get_or_declare_var("r", mr.clone()).unwrap();
        let three = e.solver.int_const(3);
        let seven = e.solver.int_const(7);
        let one = e.solver.int_const(1);
        e.bind_whole_mut_ref(&mr, &Sort::Int, r, three, seven, one)
            .expect("whole mutref binding should encode");
        e.bind_quantifier_var("r".to_string());
        e.bind_match_binder_var("r".to_string());

        let var = || PureExpr::Var("r".to_string(), None);
        let deref_t = e
            .encode_pure(&PureExpr::Deref(Arc::new(var())))
            .expect("`*r` must encode");
        let final_t = e
            .encode_pure(&PureExpr::Final(Arc::new(var())))
            .expect("`^r` must encode");

        let conflate = e.eq_term(deref_t, final_t);
        e.assert_term(conflate);
        let res = e.check_sat();
        assert!(
            matches!(res, SolveResult::Unsat(_)),
            "`*r == ^r` with cur=3/fin=7 must be UNSAT — the conflation is gone, got {res:?}"
        );
    }

    /// M0 secondary check 2: proliferation shape — three distinct inner sorts
    /// mint three DISTINCT carrier record sorts and three DISTINCT hex-named
    /// Option families (no name collisions, no shared datatype).
    #[test]
    #[timeout(30000)]
    fn m0_carrier_option_families_distinct_per_inner_sort() {
        let mut e = AYEncoder::new_all();
        let inners = [ExprSort::Int, ExprSort::Bool, ExprSort::Float];
        let mut names = std::collections::HashSet::new();
        for inner in inners {
            let mr = e.sort_from_expr_sort(ExprSort::MutRef(Box::new(inner)));
            let Sort::Uninterpreted(ref sort_name) = mr else {
                panic!("MutRef carrier must stay an uninterpreted sort, got {mr:?}");
            };
            assert!(sort_name.starts_with("__trust_wp_mutref::"));
            let dt = crate::encoder::match_enc::stdlib_option_datatype_for_payload(mr.clone());
            e.ensure_datatype_declared(&dt);
            assert!(e.has_datatype_decl(&dt.name));
            assert!(
                names.insert(dt.name.clone()),
                "Option family name collision for inner sort {sort_name}"
            );
        }
        assert_eq!(names.len(), 3);
    }

    /// bug/682 fix-direction probe: supplying the SOUND missing binding
    /// `call_2 == a_current` (the pre-call value `*a` the callee observed)
    /// closes the call-precondition goal. `a_current == 3` then forces
    /// `call_2 == 3 <= IMAX`, so the negated goal is UNSAT. Confirms the
    /// blocker is the missing pre-call argument binding, not solver depth.
    #[test]
    #[timeout(30000)]
    fn bug682_call_obligation_with_precall_binding_is_unsat() {
        let mut e = AYEncoder::new_all();
        let imax = e.solver.int_const(9_223_372_036_854_775_807);
        let three = e.solver.int_const(3);
        let a_current = e.get_or_declare_var("a_current", Sort::Int).unwrap();
        let a_final = e.get_or_declare_var("a_final", Sort::Int).unwrap();
        let a_p = e.get_or_declare_var("a_p", Sort::Int).unwrap();
        let call_2 = e.get_or_declare_var("call_2", Sort::Int).unwrap();
        let f0 = e.eq_term(a_current, three);
        e.assert_term(f0);
        let f1 = e.eq_term(a_current, a_p);
        e.assert_term(f1);
        let f3 = e.solver.lt(a_current, a_final);
        e.assert_term(f3);
        // The SOUND missing fact: call_2 is the pre-call *a = a_current.
        let bind = e.eq_term(call_2, a_current);
        e.assert_term(bind);
        let goal = e.solver.le(call_2, imax);
        let neg = e.solver.not(goal);
        e.assert_term(neg);
        let res = e.check_sat();
        assert!(
            matches!(res, SolveResult::Unsat(_)),
            "with call_2 == a_current the goal must close, got {res:?}"
        );
    }
}
