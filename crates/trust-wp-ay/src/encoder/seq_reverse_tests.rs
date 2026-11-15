// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq reverse axioms (R1-R4): initialization, preservation,
//! and view-indirection proofs.
//!
//! Extracted from `seq.rs` as part of #1669 structural decomposition.

#[cfg(test)]
mod seq_reverse_axiom_tests {
    use ay_dpll::api::{SolveResult, Sort, Term, TermKind};
    use ntest::timeout;
    use trust_wp_core::formula::PureExpr;

    use crate::{
        encoder::AYEncoder,
        tests::helpers::{eq, gt, int, method_call, sub, var, view},
    };

    fn term_contains_quantifier(encoder: &AYEncoder, term: Term) -> bool {
        let solver = encoder.solver();
        let mut stack = vec![term];
        let mut seen = std::collections::HashSet::new();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if matches!(solver.term_kind(term), TermKind::Forall | TermKind::Exists) {
                return true;
            }
            stack.extend(solver.term_children(term));
        }
        false
    }

    fn assertion_contains_quantified_seq_reverse(encoder: &AYEncoder, term: Term) -> bool {
        term_contains_quantifier(encoder, term)
            && encoder.solver().format_term(term).contains("seq_reverse")
    }

    /// Direct SMT-level test for R4 axiom in preservation context (#1581).
    ///
    /// Bypasses the loop verifier to isolate whether the axiom system alone
    /// can close the preservation proof for `result == reverse(produced)`.
    ///
    /// Setup:
    ///   - Invariant: result == reverse(produced)
    ///   - Body effect: result_prime == push_front(result, x)
    ///   - Body effect: produced_prime == push_back(produced, x)
    ///   - Goal (negated): result_prime != reverse(produced_prime)
    ///
    /// If UNSAT, the R4 axiom + congruence closure are sufficient.
    #[test]
    #[timeout(30000)]
    fn r4_axiom_closes_preservation_at_smt_level() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        let seq_funcs = encoder
            .seq_state
            .funcs_clone()
            .expect("seq funcs initialized");

        // Assert reverse axioms (including R4)
        let seq_sort = encoder.get_seq_sort();
        encoder.assert_seq_reverse_axioms(&seq_sort, &seq_funcs);

        // Declare variables
        let result = encoder
            .get_or_declare_var("result", seq_sort.clone())
            .expect("declare result");
        let produced = encoder
            .get_or_declare_var("produced", seq_sort.clone())
            .expect("declare produced");
        let result_prime = encoder
            .get_or_declare_var("result_prime", seq_sort.clone())
            .expect("declare result_prime");
        let produced_prime = encoder
            .get_or_declare_var("produced_prime", seq_sort.clone())
            .expect("declare produced_prime");
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");

        // Assert invariant: result == reverse(produced)
        let rev_produced = encoder.solver.apply(&seq_funcs.seq_reverse, &[produced]);
        let inv = encoder.solver.eq(result, rev_produced);
        encoder.assert_term(inv);

        // Assert body effect: produced_prime == push_back(produced, x)
        let pb = encoder
            .solver
            .apply(&seq_funcs.seq_push_back, &[produced, x]);
        let eff_produced = encoder.solver.eq(produced_prime, pb);
        encoder.assert_term(eff_produced);

        // Assert body effect: result_prime == push_front(result, x)
        let pf = encoder
            .solver
            .apply(&seq_funcs.seq_push_front, &[result, x]);
        let eff_result = encoder.solver.eq(result_prime, pf);
        encoder.assert_term(eff_result);

        // Negate goal: result_prime != reverse(produced_prime)
        let rev_produced_prime = encoder
            .solver
            .apply(&seq_funcs.seq_reverse, &[produced_prime]);
        let goal_neg = encoder.solver.neq(result_prime, rev_produced_prime);
        encoder.assert_term(goal_neg);

        let solve_result = encoder.check_sat();
        assert!(
            matches!(solve_result, SolveResult::Unsat(_)),
            "R4 axiom should close preservation proof at SMT level, got {solve_result:?}"
        );
    }

    /// Like `r4_axiom_closes_preservation_at_smt_level` but uses `encode_pure` to
    /// create concrete array-backed terms (shape constraints), mimicking the loop
    /// verifier's actual encoding path (#1581).
    ///
    /// This isolates whether the concrete array encoding (store/select/offset)
    /// interferes with UF-level R4 reasoning.
    #[test]
    #[timeout(30000)]
    fn r4_axiom_closes_preservation_with_encode_pure() {
        let mut encoder = AYEncoder::new();

        // Encode body effects through encode_pure (creates shape constraints)
        let produced_effect = method_call(view(var("produced")), "push_back", vec![int(0)]);
        let result_effect = method_call(view(var("result")), "push_front_ghost", vec![int(0)]);

        // Pre-register sort hints to ensure Seq sorts
        encoder.register_sort_hints(&[
            eq(
                view(var("result")),
                method_call(view(var("produced")), "reverse", vec![]),
            ),
            produced_effect.clone(),
            result_effect.clone(),
        ]);

        // Encode invariant: result_view == reverse(produced_view)
        let inv_expr = eq(
            view(var("result")),
            method_call(view(var("produced")), "reverse", vec![]),
        );
        let inv_term = encoder.encode_pure(&inv_expr).expect("encode invariant");
        encoder.assert_term(inv_term);

        // Encode body effects and get the result terms
        let push_back_term = encoder
            .encode_pure(&produced_effect)
            .expect("encode push_back");
        let push_front_term = encoder
            .encode_pure(&result_effect)
            .expect("encode push_front");

        // Declare prime variables (Seq sort)
        let seq_sort = encoder.get_seq_sort();
        let result_prime = encoder
            .get_or_declare_var("result_prime", seq_sort.clone())
            .expect("result_prime");
        let produced_prime = encoder
            .get_or_declare_var("produced_prime", seq_sort.clone())
            .expect("produced_prime");

        // Constrain primes to body effects
        encoder.assert_eq(result_prime, push_front_term);
        encoder.assert_eq(produced_prime, push_back_term);

        // Declare prime view variables with view identity
        let result_prime_view = encoder
            .get_or_declare_var("result_prime_view", seq_sort.clone())
            .expect("result_prime_view");
        let produced_prime_view = encoder
            .get_or_declare_var("produced_prime_view", seq_sort.clone())
            .expect("produced_prime_view");
        encoder.assert_eq(result_prime, result_prime_view);
        encoder.assert_eq(produced_prime, produced_prime_view);

        // Negate primed invariant: result_prime_view != reverse(produced_prime_view)
        let seq_funcs = encoder.seq_state.funcs_clone().expect("seq funcs");
        let rev_produced_prime_view = encoder
            .solver
            .apply(&seq_funcs.seq_reverse, &[produced_prime_view]);
        encoder.register_standard_ground_application(
            "seq_reverse",
            rev_produced_prime_view,
            vec![produced_prime_view],
        );
        let goal_equality =
            encoder.seq_aware_equality_term(result_prime_view, rev_produced_prime_view);
        let goal_neg = encoder.solver.not(goal_equality);
        encoder.assert_term(goal_neg);

        let solve_result = encoder.check_sat();
        assert!(
            matches!(solve_result, SolveResult::Unsat(_)),
            "R4 axiom should close preservation with encode_pure path, got {solve_result:?}"
        );
    }

    /// Like `r4_axiom_closes_preservation_at_smt_level` but with `_view` indirection
    /// to simulate what the loop verifier actually encodes (#1581).
    ///
    /// The loop verifier uses `View(Var("result"))` → `result_view` in the invariant
    /// and body effects. Primed variables get `result_prime_view` via view identity.
    /// This deliberately keeps native Seq-carrier equalities as a solver
    /// diagnostic.  The production `encode_pure` and ground-instance tests use
    /// the independently checkable finite component equality above and below;
    /// an incomplete result in this raw lane must therefore remain fail-closed.
    #[test]
    #[timeout(30000)]
    fn raw_seq_r4_view_indirection_fails_closed_if_incomplete() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        let seq_funcs = encoder
            .seq_state
            .funcs_clone()
            .expect("seq funcs initialized");

        let seq_sort = encoder.get_seq_sort();
        encoder.assert_seq_reverse_axioms(&seq_sort, &seq_funcs);

        // Declare base and view variables (simulating View encoding)
        let result_view = encoder
            .get_or_declare_var("result_view", seq_sort.clone())
            .expect("result_view");
        let produced_view = encoder
            .get_or_declare_var("produced_view", seq_sort.clone())
            .expect("produced_view");
        let result_prime = encoder
            .get_or_declare_var("result_prime", seq_sort.clone())
            .expect("result_prime");
        let produced_prime = encoder
            .get_or_declare_var("produced_prime", seq_sort.clone())
            .expect("produced_prime");
        let result_prime_view = encoder
            .get_or_declare_var("result_prime_view", seq_sort.clone())
            .expect("result_prime_view");
        let produced_prime_view = encoder
            .get_or_declare_var("produced_prime_view", seq_sort.clone())
            .expect("produced_prime_view");
        let x = encoder.get_or_declare_var("x", Sort::Int).expect("x");

        // View identities: result_prime == result_prime_view, etc.
        let result_view_identity = encoder.solver.eq(result_prime, result_prime_view);
        encoder.assert_term(result_view_identity);
        let produced_view_identity = encoder.solver.eq(produced_prime, produced_prime_view);
        encoder.assert_term(produced_view_identity);

        // Invariant: result_view == reverse(produced_view)
        let rev_produced_view = encoder
            .solver
            .apply(&seq_funcs.seq_reverse, &[produced_view]);
        let invariant = encoder.solver.eq(result_view, rev_produced_view);
        encoder.assert_term(invariant);

        // Body effect: produced_prime == push_back(produced_view, x)
        let pb = encoder
            .solver
            .apply(&seq_funcs.seq_push_back, &[produced_view, x]);
        let produced_effect = encoder.solver.eq(produced_prime, pb);
        encoder.assert_term(produced_effect);

        // Body effect: result_prime == push_front(result_view, x)
        let pf = encoder
            .solver
            .apply(&seq_funcs.seq_push_front, &[result_view, x]);
        let result_effect = encoder.solver.eq(result_prime, pf);
        encoder.assert_term(result_effect);

        // Negate primed invariant: result_prime_view != reverse(produced_prime_view)
        let rev_produced_prime_view = encoder
            .solver
            .apply(&seq_funcs.seq_reverse, &[produced_prime_view]);
        let goal_neg = encoder
            .solver
            .neq(result_prime_view, rev_produced_prime_view);
        encoder.assert_term(goal_neg);

        let solve_result = encoder.check_sat();
        let unknown_reason = encoder
            .solver
            .unknown_reason()
            .map(|reason| format!("{reason:?}"));
        assert!(
            matches!(solve_result, SolveResult::Unsat(_))
                || (matches!(solve_result, SolveResult::Unknown)
                    && unknown_reason.as_deref() == Some("Incomplete")),
            "the non-authoritative raw native-Seq view-indirection diagnostic may prove UNSAT or \
             fail closed only as Incomplete, got {solve_result:?} ({unknown_reason:?})"
        );
    }

    /// Ground R4 instances should close the same view-indirection preservation
    /// shape without relying on the quantified reverse axiom. This is the
    /// solver-stable path used by #2116 loop proofs when `push_back(...)` is
    /// present in the body effect and ext_eq already consumes quantifier budget.
    #[test]
    #[timeout(30000)]
    fn ground_r4_instance_closes_preservation_with_view_indirection() {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        encoder.ensure_seq_functions();
        let seq_funcs = encoder
            .seq_state
            .funcs_clone()
            .expect("seq funcs initialized");

        let seq_sort = encoder.get_seq_sort();
        let result_view = encoder
            .get_or_declare_var("result_view", seq_sort.clone())
            .expect("result_view");
        let produced_view = encoder
            .get_or_declare_var("produced_view", seq_sort.clone())
            .expect("produced_view");
        let result_prime = encoder
            .get_or_declare_var("result_prime", seq_sort.clone())
            .expect("result_prime");
        let produced_prime = encoder
            .get_or_declare_var("produced_prime", seq_sort.clone())
            .expect("produced_prime");
        let result_prime_view = encoder
            .get_or_declare_var("result_prime_view", seq_sort.clone())
            .expect("result_prime_view");
        let produced_prime_view = encoder
            .get_or_declare_var("produced_prime_view", seq_sort.clone())
            .expect("produced_prime_view");
        let x = encoder.get_or_declare_var("x", Sort::Int).expect("x");

        let rv_id1 = encoder.solver.eq(result_prime, result_prime_view);
        encoder.assert_term(rv_id1);
        let rv_id2 = encoder.solver.eq(produced_prime, produced_prime_view);
        encoder.assert_term(rv_id2);

        let rev_produced_view = encoder
            .solver
            .apply(&seq_funcs.seq_reverse, &[produced_view]);
        let inv = encoder.solver.eq(result_view, rev_produced_view);
        encoder.assert_term(inv);

        let push_back = encoder
            .solver
            .apply(&seq_funcs.seq_push_back, &[produced_view, x]);
        encoder.register_standard_ground_application(
            "seq_push_back",
            push_back,
            vec![produced_view, x],
        );
        encoder.assert_eq(produced_prime, push_back);

        let push_front = encoder
            .solver
            .apply(&seq_funcs.seq_push_front, &[result_view, x]);
        encoder.assert_eq(result_prime, push_front);

        let asserted = encoder.assert_standard_ground_instances();
        assert!(
            asserted >= 2,
            "seq_push_back should emit at least len+1 and R4 ground instances, got {asserted}"
        );

        let rev_produced_prime_view = encoder
            .solver
            .apply(&seq_funcs.seq_reverse, &[produced_prime_view]);
        encoder.register_standard_ground_application(
            "seq_reverse",
            rev_produced_prime_view,
            vec![produced_prime_view],
        );
        let goal_equality =
            encoder.seq_aware_equality_term(result_prime_view, rev_produced_prime_view);
        let goal_neg = encoder.solver.not(goal_equality);
        encoder.assert_term(goal_neg);

        let solve_result = encoder.check_sat();
        assert!(
            matches!(solve_result, SolveResult::Unsat(_)),
            "ground R4 instance should close preservation with view indirection, got {solve_result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn ground_reverse_index_proves_last_maps_to_first() {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();

        let len_s = method_call(view(var("s")), "len", vec![]);
        let reverse_s = method_call(view(var("s")), "reverse", vec![]);
        let reverse_last = method_call(reverse_s, "index_logic", vec![sub(len_s.clone(), int(1))]);
        let s_first = method_call(view(var("s")), "index_logic", vec![int(0)]);
        let goal = eq(reverse_last, s_first);
        let len_positive = gt(len_s, int(0));

        encoder.register_sort_hints(&[len_positive.clone(), goal.clone()]);
        let len_positive_term = encoder
            .encode_pure(&len_positive)
            .expect("encode s.len() > 0");
        encoder.assert_term(len_positive_term);
        let goal_term = encoder
            .encode_pure(&goal)
            .expect("encode reverse last index goal");

        assert!(
            encoder
                .ground_pool_for_test()
                .entries_for("seq_reverse")
                .is_some(),
            "encoding reverse(s) should register a seq_reverse ground entry"
        );

        let asserted = encoder.assert_standard_ground_instances();
        assert!(
            asserted >= 3,
            "reverse index proof should emit len, direct index, and observed-index ground facts, got {asserted}"
        );

        let not_goal = encoder.solver.not(goal_term);
        encoder.assert_term(not_goal);

        let solve_result = encoder.check_sat();
        assert!(
            matches!(solve_result, SolveResult::Unsat(_)),
            "ground reverse index instance should prove s.len()>0 => reverse(s)[len(s)-1] == s[0], got {solve_result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn ground_subsequence_of_reverse_index_feeds_reverse_index_instance() {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();

        let len_s = method_call(view(var("s")), "len", vec![]);
        let reverse_s = method_call(view(var("s")), "reverse", vec![]);
        let reverse_slice = method_call(reverse_s, "subsequence", vec![int(0), len_s.clone()]);
        let slice_last = method_call(
            reverse_slice,
            "index_logic",
            vec![sub(len_s.clone(), int(1))],
        );
        let s_first = method_call(view(var("s")), "index_logic", vec![int(0)]);
        let goal = eq(slice_last, s_first);
        let len_positive = gt(len_s, int(0));

        encoder.register_sort_hints(&[len_positive.clone(), goal.clone()]);
        let len_positive_term = encoder
            .encode_pure(&len_positive)
            .expect("encode s.len() > 0");
        encoder.assert_term(len_positive_term);
        let goal_term = encoder
            .encode_pure(&goal)
            .expect("encode subsequence(reverse(s)) index goal");

        assert!(
            encoder
                .ground_pool_for_test()
                .entries_for("seq_subsequence")
                .is_some(),
            "encoding subsequence(reverse(s), 0, len(s)) should register a seq_subsequence ground entry"
        );
        assert!(
            encoder
                .ground_pool_for_test()
                .entries_for("seq_reverse")
                .is_some(),
            "encoding nested reverse should register a seq_reverse ground entry"
        );

        let asserted = encoder.assert_standard_ground_instances();
        assert!(
            asserted >= 5,
            "subsequence(reverse(s)) proof should emit subsequence and reverse ground facts, got {asserted}"
        );

        let not_goal = encoder.solver.not(goal_term);
        encoder.assert_term(not_goal);

        let solve_result = encoder.check_sat();
        assert!(
            matches!(solve_result, SolveResult::Unsat(_)),
            "subsequence index ground instance should feed reverse index proof, got {solve_result:?}"
        );
    }

    /// Minimal R1 test: reverse(seq_empty) != seq_empty should be UNSAT.
    #[test]
    #[timeout(30000)]
    fn r1_axiom_reverse_empty_is_empty() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        let seq_funcs = encoder.seq_state.funcs_clone().expect("seq funcs");
        let seq_sort = encoder.get_seq_sort();
        encoder.assert_seq_reverse_axioms(&seq_sort, &seq_funcs);

        let rev_empty = encoder
            .solver
            .apply(&seq_funcs.seq_reverse, &[seq_funcs.seq_empty]);
        let equality = encoder.seq_aware_equality_term(rev_empty, seq_funcs.seq_empty);
        let neq = encoder.solver.not(equality);
        encoder.assert_term(neq);

        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "R1: reverse(seq_empty) == seq_empty should make neq UNSAT, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn encoding_reverse_registers_ground_entry_and_quantified_axioms() {
        // Encoding `reverse(s)` registers a ground entry (for E-graph-local
        // finite instances) AND asserts the quantified reverse axiom family
        // (R1/R2/R4/R5 in the production path; R3 is skipped there for E-matching
        // cost). The quantified axioms are required so paths that never accumulate
        // ground push_back/push_front entries — e.g. the `reverse_ghost_ref` /
        // `to_owned_seq` borrowed-element seq — do not leave `seq_reverse`
        // effectively uninterpreted (which produced spurious SAT). Asserting these
        // VALID Seq theorems is completeness-only / monotone. (#1581)
        let mut encoder = AYEncoder::new_pure_with_quantifiers();

        let reverse_s = method_call(view(var("s")), "reverse", vec![]);
        let _ = encoder
            .encode_pure(&reverse_s)
            .expect("reverse(s) should encode");

        assert!(
            encoder
                .ground_pool_for_test()
                .entries_for("seq_reverse")
                .is_some(),
            "encoding reverse(s) should register a seq_reverse ground entry"
        );
        assert!(
            encoder
                .solver
                .assertions()
                .iter()
                .any(|assertion| assertion_contains_quantified_seq_reverse(&encoder, *assertion)),
            "encoding reverse(s) should assert the quantified seq_reverse axioms"
        );
    }

    #[test]
    #[timeout(30000)]
    fn ground_r1_empty_alias_closes_without_reverse_forall() {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        encoder.ensure_seq_functions();
        let seq_funcs = encoder.seq_state.funcs_clone().expect("seq funcs");

        let rev_empty = encoder
            .solver
            .apply(&seq_funcs.seq_reverse, &[seq_funcs.seq_empty]);
        encoder.register_standard_ground_application(
            "seq_reverse",
            rev_empty,
            vec![seq_funcs.seq_empty],
        );

        let asserted = encoder.assert_standard_ground_instances();
        assert!(
            asserted >= 1,
            "reverse(empty) ground instance should be asserted"
        );
        assert!(
            encoder
                .solver
                .assertions()
                .iter()
                .all(|assertion| !assertion_contains_quantified_seq_reverse(&encoder, *assertion)),
            "reverse(empty) ground proof should not assert quantified seq_reverse axioms"
        );

        let equality = encoder.seq_aware_equality_term(rev_empty, seq_funcs.seq_empty);
        let neq = encoder.solver.not(equality);
        encoder.assert_term(neq);

        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "ground R1 reverse(empty) == empty should make neq UNSAT, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn ground_r5_instance_closes_push_front_dual() {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        encoder.ensure_seq_functions();
        let seq_funcs = encoder.seq_state.funcs_clone().expect("seq funcs");
        let seq_sort = encoder.get_seq_sort();

        let s = encoder
            .get_or_declare_var("r5_s", seq_sort)
            .expect("declare r5_s");
        let x = encoder
            .get_or_declare_var("r5_x", Sort::Int)
            .expect("declare r5_x");
        let push_front = encoder.solver.apply(&seq_funcs.seq_push_front, &[s, x]);
        encoder.register_standard_ground_application("seq_push_front", push_front, vec![s, x]);

        let rev_push_front = encoder.solver.apply(&seq_funcs.seq_reverse, &[push_front]);
        encoder.register_standard_ground_application(
            "seq_reverse",
            rev_push_front,
            vec![push_front],
        );
        let rev_s = encoder.solver.apply(&seq_funcs.seq_reverse, &[s]);
        let push_back_rev = encoder.solver.apply(&seq_funcs.seq_push_back, &[rev_s, x]);

        let asserted = encoder.assert_standard_ground_instances();
        assert!(
            asserted >= 1,
            "push_front dual ground reverse instance should be asserted"
        );

        let equality = encoder.seq_aware_equality_term(rev_push_front, push_back_rev);
        let neq = encoder.solver.not(equality);
        encoder.assert_term(neq);

        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "ground R5 reverse(push_front(s, x)) == push_back(reverse(s), x) should close, got {result:?}"
        );
    }

    /// Tests R1 axiom (reverse(empty) == empty) via encode_pure path (#1581).
    ///
    /// Setup: result_view == seq_empty, produced_view == seq_empty,
    /// negate: result_view != reverse(produced_view).
    /// Should be UNSAT via R1.
    #[test]
    #[timeout(30000)]
    fn r1_axiom_closes_initialization_at_encoder_level() {
        let mut encoder = AYEncoder::new();

        // Encode init facts via encode_pure
        let seq_empty_fn = PureExpr::LogicFnCall {
            name: "seq_empty".to_string(),
            args: vec![],
        };
        let init1 = eq(view(var("result")), seq_empty_fn.clone());
        let init2 = eq(view(var("produced")), seq_empty_fn);
        let invariant_expr = eq(
            view(var("result")),
            method_call(view(var("produced")), "reverse", vec![]),
        );

        // Register sort hints
        encoder.register_sort_hints(&[init1.clone(), init2.clone(), invariant_expr.clone()]);

        // Encode and assert init facts
        let init1_term = encoder.encode_pure(&init1).expect("encode init1");
        encoder.assert_term(init1_term);
        let init2_term = encoder.encode_pure(&init2).expect("encode init2");
        encoder.assert_term(init2_term);

        // Encode and negate invariant
        let inv_term = encoder
            .encode_pure(&invariant_expr)
            .expect("encode invariant");
        let neg_inv = encoder.solver.not(inv_term);
        encoder.assert_term(neg_inv);

        let solve_result = encoder.check_sat();
        assert!(
            matches!(solve_result, SolveResult::Unsat(_)),
            "R1 axiom should close initialization proof, got {solve_result:?}"
        );
    }

    /// Diagnostic: does the E-graph chain prove concat equality for ext_eq
    /// preservation? (#2116, #2465)
    ///
    /// Given:
    ///   produced_prime = push_back(produced, v)
    ///   push_front(iter_prime, v) = iter         (transition fact)
    ///   concat(push_back(produced, v), iter_prime)
    ///     = concat(produced, push_front(iter_prime, v))  (ground bridge)
    ///
    /// Goal: concat(produced_prime, iter_prime) = concat(produced, iter)
    ///
    /// This chain is the critical path for ext_eq preservation proofs.
    /// Tests at the raw SMT level to isolate solver capability.
    #[test]
    #[timeout(30000)]
    fn concat_equality_chain_for_ext_eq_preservation() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        let seq_funcs = encoder.seq_state.funcs_clone().expect("seq funcs");
        let seq_sort = encoder.get_seq_sort();

        // Declare variables
        let produced = encoder
            .get_or_declare_var("produced", seq_sort.clone())
            .expect("produced");
        let produced_prime = encoder
            .get_or_declare_var("produced_prime", seq_sort.clone())
            .expect("produced_prime");
        let iter = encoder
            .get_or_declare_var("iter", seq_sort.clone())
            .expect("iter");
        let iter_prime = encoder
            .get_or_declare_var("iter_prime", seq_sort.clone())
            .expect("iter_prime");
        let v = encoder.get_or_declare_var("v", Sort::Int).expect("v");

        // Body effect: produced_prime = push_back(produced, v)
        let push_back = encoder
            .solver
            .apply(&seq_funcs.seq_push_back, &[produced, v]);
        let eff = encoder.solver.eq(produced_prime, push_back);
        encoder.assert_term(eff);

        // Transition fact: iter = push_front(iter_prime, v)
        let push_front = encoder
            .solver
            .apply(&seq_funcs.seq_push_front, &[iter_prime, v]);
        let trans = encoder.solver.eq(iter, push_front);
        encoder.assert_term(trans);

        // Ground bridge: concat(push_back(produced, v), iter_prime)
        //              = concat(produced, push_front(iter_prime, v))
        let lhs = encoder
            .solver
            .apply(&seq_funcs.seq_concat, &[push_back, iter_prime]);
        let rhs = encoder
            .solver
            .apply(&seq_funcs.seq_concat, &[produced, push_front]);
        let bridge = encoder.solver.eq(lhs, rhs);
        encoder.assert_term(bridge);

        // Negate goal: concat(produced_prime, iter_prime) != concat(produced, iter)
        let concat_new = encoder
            .solver
            .apply(&seq_funcs.seq_concat, &[produced_prime, iter_prime]);
        let concat_old = encoder
            .solver
            .apply(&seq_funcs.seq_concat, &[produced, iter]);
        let goal_neg = encoder.solver.neq(concat_new, concat_old);
        encoder.assert_term(goal_neg);

        let solve_result = encoder.check_sat();
        assert!(
            matches!(solve_result, SolveResult::Unsat(_)),
            "E-graph chain should prove concat equality for ext_eq preservation, got {solve_result:?}"
        );
    }

    /// Full ext_eq preservation through encode_pure, including Tseitin
    /// variables, congruence bridge, and ground axioms. (#2116, #2465)
    ///
    /// Tests the complete encoding path to diagnose whether quantified
    /// axioms or shape constraints prevent the solver from closing the proof.
    #[test]
    #[timeout(30000)]
    fn ext_eq_preservation_through_encode_pure() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        // The full invariant set
        let concat = method_call(view(var("produced")), "concat", vec![view(var("iter"))]);
        let ext_eq_inv = method_call(view(var("original")), "ext_eq", vec![concat]);
        let reverse_inv = eq(
            view(var("result")),
            method_call(view(var("produced")), "reverse", vec![]),
        );
        let produced_effect = method_call(view(var("produced")), "push_back", vec![var("v")]);
        let result_effect = method_call(view(var("result")), "push_front_ghost", vec![var("v")]);
        let transition = eq(
            view(var("iter")),
            method_call(view(var("iter_prime")), "push_front_ghost", vec![var("v")]),
        );

        // Primed invariants
        let concat_prime = method_call(
            view(var("produced_prime")),
            "concat",
            vec![view(var("iter_prime"))],
        );
        let ext_eq_inv_prime = method_call(view(var("original")), "ext_eq", vec![concat_prime]);
        let reverse_inv_prime = eq(
            view(var("result_prime")),
            method_call(view(var("produced_prime")), "reverse", vec![]),
        );

        // Register sort hints for ALL expressions
        let all_exprs = vec![
            ext_eq_inv.clone(),
            reverse_inv.clone(),
            produced_effect.clone(),
            result_effect.clone(),
            transition.clone(),
            ext_eq_inv_prime.clone(),
            reverse_inv_prime.clone(),
        ];
        encoder.register_sort_hints(&all_exprs);

        // Step 1: Assert current invariants
        let ext_eq_term = encoder.encode_pure(&ext_eq_inv).expect("encode ext_eq_inv");
        encoder.assert_term(ext_eq_term);
        let rev_term = encoder
            .encode_pure(&reverse_inv)
            .expect("encode reverse_inv");
        encoder.assert_term(rev_term);

        // Step 2: Encode body effects and create prime variables
        let seq_sort = encoder.get_seq_sort();
        let pb_term = encoder
            .encode_pure(&produced_effect)
            .expect("encode push_back");
        let pf_term = encoder
            .encode_pure(&result_effect)
            .expect("encode push_front");

        let produced_prime = encoder
            .get_or_declare_var("produced_prime", seq_sort.clone())
            .expect("produced_prime");
        let result_prime = encoder
            .get_or_declare_var("result_prime", seq_sort.clone())
            .expect("result_prime");
        let _iter_prime = encoder
            .get_or_declare_var("iter_prime", seq_sort.clone())
            .expect("iter_prime");

        // Assert body effect equalities
        let eff1 = encoder.eq_term(produced_prime, pb_term);
        encoder.assert_term(eff1);
        let eff2 = encoder.eq_term(result_prime, pf_term);
        encoder.assert_term(eff2);

        // Step 3: Assert transition fact
        let trans_term = encoder.encode_pure(&transition).expect("encode transition");
        encoder.assert_term(trans_term);

        // Step 4: Encode primed invariants (creates ext_eq_new + congruence bridge)
        encoder.register_sort_hints(&[ext_eq_inv_prime.clone(), reverse_inv_prime.clone()]);
        let ext_eq_prime_term = encoder
            .encode_pure(&ext_eq_inv_prime)
            .expect("encode ext_eq_prime");
        let _rev_prime_term = encoder
            .encode_pure(&reverse_inv_prime)
            .expect("encode reverse_prime");

        // Step 5: Assert ground axioms (creates push_back-concat bridge)
        let ground_count = encoder.assert_standard_ground_instances();
        eprintln!("ground instances asserted: {ground_count}");

        // Step 6: Negate ONLY the ext_eq primed invariant (isolate from reverse)
        let negated_ext_eq = encoder.solver.not(ext_eq_prime_term);
        encoder.assert_term(negated_ext_eq);

        let solve_result = encoder.check_sat();
        eprintln!("ext_eq-only preservation solve result: {solve_result:?}");
        assert!(
            matches!(solve_result, SolveResult::Unsat(_)),
            "ext_eq preservation alone should close via congruence bridge + ground axioms, got {solve_result:?}"
        );
    }

    /// Minimal ext_eq preservation test: no reverse invariant, no result
    /// body effect, no pointwise quantifier. Isolates whether the direct
    /// chain propagation axiom + shape constraints suffice. (#2116)
    #[test]
    #[timeout(30000)]
    fn ext_eq_preservation_minimal_no_pointwise() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        // Invariant: ext_eq(original@, produced@.concat(iter@))
        let concat = method_call(view(var("produced")), "concat", vec![view(var("iter"))]);
        let ext_eq_inv = method_call(view(var("original")), "ext_eq", vec![concat]);
        let produced_effect = method_call(view(var("produced")), "push_back", vec![var("v")]);
        let transition = eq(
            view(var("iter")),
            method_call(view(var("iter_prime")), "push_front_ghost", vec![var("v")]),
        );

        // Primed invariant
        let concat_prime = method_call(
            view(var("produced_prime")),
            "concat",
            vec![view(var("iter_prime"))],
        );
        let ext_eq_inv_prime = method_call(view(var("original")), "ext_eq", vec![concat_prime]);

        // Register sort hints
        encoder.register_sort_hints(&[
            ext_eq_inv.clone(),
            produced_effect.clone(),
            transition.clone(),
            ext_eq_inv_prime.clone(),
        ]);

        // Manually construct ext_eq_old WITHOUT the pointwise quantifier:
        // Just create the Tseitin variable and forward length axiom.
        let _seq_funcs = encoder.ensure_seq_theory();

        // Encode the concat for the old invariant
        let original_view_term = encoder
            .encode_pure(&view(var("original")))
            .expect("encode original_view");
        let concat_old_term = encoder
            .encode_pure(&method_call(
                view(var("produced")),
                "concat",
                vec![view(var("iter"))],
            ))
            .expect("encode concat_old");

        // Manually create ext_eq Tseitin for old invariant
        let ext_eq_old = encoder.solver.fresh_var("ext_eq_old", Sort::Bool);
        let len_r = encoder.seq_len_term(original_view_term).expect("len_r");
        let len_o = encoder.seq_len_term(concat_old_term).expect("len_o");
        let len_eq = encoder.eq_term(len_r, len_o);
        let fwd_len = encoder.solver.implies(ext_eq_old, len_eq);
        encoder.assert_solver_term("ext_eq/fwd_len", fwd_len);

        // Reverse Tseitin (term equality => ext_eq)
        let terms_equal = encoder.eq_term(original_view_term, concat_old_term);
        let rev_eq = encoder.solver.implies(terms_equal, ext_eq_old);
        encoder.assert_solver_term("ext_eq/rev_term_eq", rev_eq);

        // Register in ext_eq_registry
        encoder.encoding_cache.ext_eq_registry_push((
            original_view_term,
            concat_old_term,
            ext_eq_old,
        ));

        // Register the old concat as a ground application
        let produced_view_term = encoder
            .vars_for_test()
            .get("produced_view")
            .copied()
            .expect("produced_view");
        let iter_view_term = encoder.var_term("iter_view").expect("iter_view");
        encoder.register_standard_ground_application(
            "seq_concat",
            concat_old_term,
            vec![produced_view_term, iter_view_term],
        );

        // Assert ext_eq_old = true (invariant holds)
        encoder.assert_term(ext_eq_old);

        // Encode body effect: push_back(produced_view, v)
        let seq_sort = encoder.get_seq_sort();
        let pb_term = encoder
            .encode_pure(&produced_effect)
            .expect("encode push_back");

        // Create prime variables
        let produced_prime = encoder
            .get_or_declare_var("produced_prime", seq_sort.clone())
            .expect("produced_prime");
        let _iter_prime = encoder
            .get_or_declare_var("iter_prime", seq_sort.clone())
            .expect("iter_prime");

        // Assert body effect
        let eff1 = encoder.eq_term(produced_prime, pb_term);
        encoder.assert_term(eff1);

        // Assert transition fact
        let trans_term = encoder.encode_pure(&transition).expect("encode transition");
        encoder.assert_term(trans_term);

        // Encode primed ext_eq (will create bridge via registry)
        encoder.register_sort_hints(&[ext_eq_inv_prime.clone()]);
        let ext_eq_prime_term = encoder
            .encode_pure(&ext_eq_inv_prime)
            .expect("encode ext_eq_prime");

        // Assert ground instances (includes preservation chain)
        let ground_count = encoder.assert_standard_ground_instances();
        eprintln!("ground instances (no-pointwise): {ground_count}");

        // Negate ext_eq_new
        let negated = encoder.solver.not(ext_eq_prime_term);
        encoder.assert_term(negated);

        let solve_result = encoder.check_sat();
        eprintln!("no-pointwise preservation result: {solve_result:?}");
        assert!(
            matches!(solve_result, SolveResult::Unsat(_)),
            "ext_eq preservation without pointwise should close via chain propagation, got {solve_result:?}"
        );
    }

    /// Micro-test: can ay-dpll evaluate theory equality atoms in
    /// implications? (#2116 diagnostic)
    #[test]
    #[timeout(5000)]
    fn ay_dpll_theory_equality_atom_propagation() {
        let mut encoder = AYEncoder::new();
        let seq_sort = encoder.get_seq_sort();
        let a = encoder
            .get_or_declare_var("a", seq_sort.clone())
            .expect("a");
        let b = encoder
            .get_or_declare_var("b", seq_sort.clone())
            .expect("b");
        let c = encoder.solver.fresh_var("c", Sort::Bool);

        // Assert a = b
        let eq_ab = encoder.solver.eq(a, b);
        encoder.assert_term(eq_ab);

        // Assert eq(a, b) => c
        let eq_atom = encoder.solver.eq(a, b);
        let impl_term = encoder.solver.implies(eq_atom, c);
        encoder.assert_term(impl_term);

        // Assert NOT c
        let not_c = encoder.solver.not(c);
        encoder.assert_term(not_c);

        let result = encoder.check_sat();
        eprintln!("theory eq atom propagation: {result:?}");
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "ay-dpll should propagate theory equality atoms, got {result:?}"
        );
    }

    /// Diagnostic: can ay-dpll evaluate congruence-derived equality atoms?
    /// Tests: assert a=a', b=b', then check eq(concat(a,b), concat(a',b'))
    /// in an implication. (#2116 diagnostic)
    #[test]
    #[timeout(5000)]
    fn ay_dpll_congruence_derived_equality_atom() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let seq_funcs = encoder.ensure_seq_theory();
        let seq_sort = encoder.get_seq_sort();

        let a = encoder
            .get_or_declare_var("a", seq_sort.clone())
            .expect("a");
        let a_prime = encoder
            .get_or_declare_var("a_prime", seq_sort.clone())
            .expect("a_prime");
        let b = encoder
            .get_or_declare_var("b", seq_sort.clone())
            .expect("b");
        let b_prime = encoder
            .get_or_declare_var("b_prime", seq_sort.clone())
            .expect("b_prime");

        // Create concat terms
        let concat_ab = encoder.solver.apply(&seq_funcs.seq_concat, &[a, b]);
        let concat_ab_prime = encoder
            .solver
            .apply(&seq_funcs.seq_concat, &[a_prime, b_prime]);

        // Assert a = a' and b = b' (direct)
        let eq_a = encoder.solver.eq(a, a_prime);
        encoder.assert_term(eq_a);
        let eq_b = encoder.solver.eq(b, b_prime);
        encoder.assert_term(eq_b);

        // Create Bool variable for the bridge
        let bridge_var = encoder.solver.fresh_var("bridge", Sort::Bool);

        // Assert eq(concat(a,b), concat(a',b')) => bridge_var
        let concat_eq = encoder.solver.eq(concat_ab, concat_ab_prime);
        let impl_term = encoder.solver.implies(concat_eq, bridge_var);
        encoder.assert_term(impl_term);

        // Assert NOT bridge_var
        let not_bridge = encoder.solver.not(bridge_var);
        encoder.assert_term(not_bridge);

        let result = encoder.check_sat();
        eprintln!("congruence-derived eq atom: {result:?}");
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "ay-dpll should propagate congruence-derived equality atoms, got {result:?}"
        );
    }

    /// Diagnostic: same as above but equality is TRANSITIVE (a=f(x), a'=f(x)).
    /// Tests whether congruence works through function application. (#2116)
    #[test]
    #[timeout(5000)]
    fn ay_dpll_transitive_congruence_equality_atom() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let seq_funcs = encoder.ensure_seq_theory();
        let seq_sort = encoder.get_seq_sort();

        let a = encoder
            .get_or_declare_var("a", seq_sort.clone())
            .expect("a");
        let a_prime = encoder
            .get_or_declare_var("a_prime", seq_sort.clone())
            .expect("a_prime");
        let b = encoder
            .get_or_declare_var("b", seq_sort.clone())
            .expect("b");
        let b_prime = encoder
            .get_or_declare_var("b_prime", seq_sort.clone())
            .expect("b_prime");
        let x = encoder.get_or_declare_var("x", Sort::Int).expect("x");

        // a_prime = push_back(a, x) [body effect analog]
        let pb = encoder.solver.apply(&seq_funcs.seq_push_back, &[a, x]);
        let eq_ap = encoder.solver.eq(a_prime, pb);
        encoder.assert_term(eq_ap);

        // b = push_front(b_prime, x) [transition analog]
        let pf = encoder
            .solver
            .apply(&seq_funcs.seq_push_front, &[b_prime, x]);
        let eq_b = encoder.solver.eq(b, pf);
        encoder.assert_term(eq_b);

        // Push_back-concat bridge: concat(pb, b') = concat(a, pf)
        let concat_old = encoder.solver.apply(&seq_funcs.seq_concat, &[a, b]);
        let concat_new = encoder
            .solver
            .apply(&seq_funcs.seq_concat, &[a_prime, b_prime]);
        let concat_lhs = encoder.solver.apply(&seq_funcs.seq_concat, &[pb, b_prime]);
        let concat_rhs = encoder.solver.apply(&seq_funcs.seq_concat, &[a, pf]);
        let bridge_eq = encoder.solver.eq(concat_lhs, concat_rhs);
        encoder.assert_term(bridge_eq);

        // Bridge: eq(concat_old, concat_new) => result_var
        let result_var = encoder.solver.fresh_var("result", Sort::Bool);
        let concat_eq = encoder.solver.eq(concat_old, concat_new);
        let impl_term = encoder.solver.implies(concat_eq, result_var);
        encoder.assert_term(impl_term);

        // Assert NOT result_var
        let not_result = encoder.solver.not(result_var);
        encoder.assert_term(not_result);

        let result = encoder.check_sat();
        eprintln!("transitive congruence eq atom: {result:?}");
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "ay-dpll should chain transitive congruence for equality atoms, got {result:?}"
        );
    }

    /// Diagnostic: same transitive chain but using encode_pure (shape constraints).
    /// This isolates whether shape constraints from push_back/concat encoding
    /// prevent congruence closure from chaining. (#2116)
    fn transitive_congruence_with_shape_constraints(
        seq_aware: bool,
    ) -> (SolveResult, Option<String>) {
        let mut encoder = AYEncoder::new_with_quantifiers();

        // Use encode_pure to create terms WITH shape constraints
        let produced_view = view(var("produced"));
        let iter_view_expr = view(var("iter"));
        let produced_prime_view = view(var("produced_prime"));
        let iter_prime_view = view(var("iter_prime"));

        // Register sort hints
        let concat_old_expr = method_call(
            produced_view.clone(),
            "concat",
            vec![iter_view_expr.clone()],
        );
        let concat_new_expr = method_call(
            produced_prime_view.clone(),
            "concat",
            vec![iter_prime_view.clone()],
        );
        let push_back_expr = method_call(produced_view.clone(), "push_back", vec![var("v")]);
        let push_front_expr =
            method_call(iter_prime_view.clone(), "push_front_ghost", vec![var("v")]);
        encoder.register_sort_hints(&[
            concat_old_expr.clone(),
            concat_new_expr.clone(),
            push_back_expr.clone(),
            push_front_expr.clone(),
        ]);

        // Encode all terms (creates shape constraints)
        let concat_old_term = encoder.encode_pure(&concat_old_expr).expect("concat_old");
        let concat_new_term = encoder.encode_pure(&concat_new_expr).expect("concat_new");
        let pb_term = encoder.encode_pure(&push_back_expr).expect("push_back");
        let pf_term = encoder.encode_pure(&push_front_expr).expect("push_front");

        // concat_new reads produced_prime's VIEW, so the body effect must
        // relate that same carrier to push_back. Equating only the owner left
        // produced_prime_view unconstrained and made the raw query SAT.
        let produced_prime_view_term = encoder
            .encode_pure(&produced_prime_view)
            .expect("produced_prime view");
        let eff = if seq_aware {
            encoder.seq_aware_equality_term(produced_prime_view_term, pb_term)
        } else {
            encoder.solver.eq(produced_prime_view_term, pb_term)
        };
        encoder.assert_term(eff);

        // Use the exact view carrier concat_old reads for the transition too.
        let iter_view_term = encoder.encode_pure(&iter_view_expr).expect("iter view");
        let trans = if seq_aware {
            encoder.seq_aware_equality_term(iter_view_term, pf_term)
        } else {
            encoder.solver.eq(iter_view_term, pf_term)
        };
        encoder.assert_term(trans);

        // Push_back-concat bridge (manually asserted, same as ground pool):
        // concat(push_back(produced_view, v), iter_prime_view) =
        // concat(produced_view, push_front(iter_prime_view, v))
        let seq_funcs = encoder.seq_state.funcs_clone().expect("seq funcs");
        let produced_view_term = encoder.var_term("produced_view").expect("pv");
        let iter_prime_view_term = encoder.var_term("iter_prime_view").expect("ipv");
        let concat_lhs = encoder
            .solver
            .apply(&seq_funcs.seq_concat, &[pb_term, iter_prime_view_term]);
        let concat_rhs = encoder
            .solver
            .apply(&seq_funcs.seq_concat, &[produced_view_term, pf_term]);
        let bridge_eq = if seq_aware {
            // The finite production lane materializes the authenticated ground
            // preservation bridge directly over the observed concat results.
            // Raw carrier congruence below is retained as an independent EUF
            // cross-check; the finite bridge remains production proof authority.
            encoder.seq_aware_equality_term(concat_old_term, concat_new_term)
        } else {
            encoder.solver.eq(concat_lhs, concat_rhs)
        };
        encoder.assert_term(bridge_eq);

        // Now check: eq(concat_old, concat_new) => result_var
        let result_var = encoder.solver.fresh_var("result", Sort::Bool);
        let concat_eq = if seq_aware {
            encoder.seq_aware_equality_term(concat_old_term, concat_new_term)
        } else {
            encoder.solver.eq(concat_old_term, concat_new_term)
        };
        let impl_term = encoder.solver.implies(concat_eq, result_var);
        encoder.assert_term(impl_term);

        // Assert NOT result_var
        let not_result = encoder.solver.not(result_var);
        encoder.assert_term(not_result);

        let result = encoder.check_sat();
        let unknown_reason = encoder
            .solver
            .unknown_reason()
            .map(|reason| format!("{reason:?}"));
        (result, unknown_reason)
    }

    #[test]
    #[timeout(30000)]
    fn raw_seq_transitive_congruence_with_shape_constraints_fails_closed_if_incomplete() {
        let (result, unknown_reason) = transitive_congruence_with_shape_constraints(false);
        assert!(
            matches!(result, SolveResult::Unsat(_))
                || (matches!(result, SolveResult::Unknown)
                    && unknown_reason.as_deref() == Some("Incomplete")),
            "the non-authoritative raw native-Seq diagnostic may prove UNSAT or fail closed only \
             as Incomplete, got {result:?} ({unknown_reason:?})"
        );
    }

    #[test]
    #[timeout(30000)]
    fn seq_aware_transitive_congruence_with_shape_constraints_is_certified() {
        let (result, unknown_reason) = transitive_congruence_with_shape_constraints(true);
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "the production finite extensional lane must certify the same chain, got {result:?} \
             ({unknown_reason:?})"
        );
    }

    /// Diagnostic: check if individual arg equality atoms work with shape
    /// constraints. If eq(a_new, pb_app) propagates even with shapes,
    /// we can decompose the bridge into per-arg conditions. (#2116)
    #[test]
    #[timeout(30000)]
    fn ay_dpll_per_arg_equality_with_shape_constraints() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        let produced_view = view(var("produced"));
        let produced_prime_view = view(var("produced_prime"));
        let push_back_expr = method_call(produced_view.clone(), "push_back", vec![var("v")]);

        encoder.register_sort_hints(&[
            produced_view.clone(),
            produced_prime_view.clone(),
            push_back_expr.clone(),
        ]);

        // Declare produced_prime as Seq BEFORE encoding (so view creates Seq-sorted var)
        let seq_sort = encoder.get_seq_sort();
        let produced_prime = encoder
            .get_or_declare_var("produced_prime", seq_sort.clone())
            .expect("pp");

        // Encode push_back WITH shape constraints
        let pb_term = encoder.encode_pure(&push_back_expr).expect("push_back");

        // Encode produced_prime_view (now produced_prime exists with Seq sort)
        let _pp_view = encoder.encode_pure(&produced_prime_view).expect("pp_view");

        // Body effect: produced_prime = push_back(produced_view, v)
        let eff = encoder.solver.eq(produced_prime, pb_term);
        encoder.assert_term(eff);

        // Get produced_prime_view term
        let pp_view_term = encoder.var_term("produced_prime_view").expect("ppv");
        let pp_sort = encoder.solver.get_sort(pp_view_term);
        let pb_sort = encoder.solver.get_sort(pb_term);
        eprintln!("pp_view sort: {pp_sort:?}, pb sort: {pb_sort:?}");

        // Check: eq(produced_prime_view, pb_term) => result_var
        let result_var = encoder.solver.fresh_var("result", Sort::Bool);
        let arg_eq = encoder.eq_term(pp_view_term, pb_term);
        let impl_term = encoder.solver.implies(arg_eq, result_var);
        encoder.assert_term(impl_term);

        // Assert NOT result_var
        let not_result = encoder.solver.not(result_var);
        encoder.assert_term(not_result);

        let result = encoder.check_sat();
        eprintln!("per-arg equality with shape constraints: {result:?}");
        eprintln!(
            "per-arg equality {}",
            if matches!(result, SolveResult::Unsat(_)) {
                "WORKS"
            } else {
                "BLOCKED"
            }
        );
    }

    /// Diagnostic: TWO theory atom conditions in one clause with shapes.
    /// Tests: (eq(a,a') AND eq(b,b')) => result. (#2116)
    #[test]
    #[timeout(30000)]
    fn ay_dpll_two_conditions_with_shape_constraints() {
        let mut encoder = AYEncoder::new_with_quantifiers();

        // Register sort hints
        let all_exprs = [
            view(var("produced")),
            view(var("produced_prime")),
            view(var("iter")),
            view(var("iter_prime")),
            method_call(view(var("produced")), "push_back", vec![var("v")]),
            method_call(view(var("iter_prime")), "push_front_ghost", vec![var("v")]),
        ];
        encoder.register_sort_hints(&all_exprs);

        // Declare ALL vars as Seq BEFORE encoding (so view creates Seq-sorted vars)
        let seq_sort = encoder.get_seq_sort();
        let _p = encoder
            .get_or_declare_var("produced", seq_sort.clone())
            .expect("p");
        let _pp = encoder
            .get_or_declare_var("produced_prime", seq_sort.clone())
            .expect("pp");
        let _it = encoder
            .get_or_declare_var("iter", seq_sort.clone())
            .expect("it");
        let _ip = encoder
            .get_or_declare_var("iter_prime", seq_sort.clone())
            .expect("ip");

        // Encode with shape constraints
        let pb_term = encoder
            .encode_pure(&method_call(
                view(var("produced")),
                "push_back",
                vec![var("v")],
            ))
            .expect("push_back");
        let pf_term = encoder
            .encode_pure(&method_call(
                view(var("iter_prime")),
                "push_front_ghost",
                vec![var("v")],
            ))
            .expect("push_front");

        // Encode view terms
        let _ppv = encoder
            .encode_pure(&view(var("produced_prime")))
            .expect("ppv");
        let _iv = encoder.encode_pure(&view(var("iter"))).expect("iv");

        // Body effect: produced_prime = pb_term
        let pp = encoder.var_term("produced_prime").unwrap();
        let eff = encoder.solver.eq(pp, pb_term);
        encoder.assert_term(eff);

        // Transition: iter_view = pf_term
        let iv = encoder.var_term("iter_view").unwrap();
        let trans = encoder.solver.eq(iv, pf_term);
        encoder.assert_term(trans);

        // Get terms
        let ppv = encoder.var_term("produced_prime_view").unwrap();
        let iter_view = encoder.var_term("iter_view").unwrap();

        // TWO conditions: (ppv = pb) AND (pf = iter_view) => result
        let result_var = encoder.solver.fresh_var("result", Sort::Bool);
        let cond1 = encoder.eq_term(ppv, pb_term);
        let cond2 = encoder.eq_term(pf_term, iter_view);
        let ant = encoder.solver.and(cond1, cond2);
        let impl_term = encoder.solver.implies(ant, result_var);
        encoder.assert_term(impl_term);

        // Assert NOT result
        let not_result = encoder.solver.not(result_var);
        encoder.assert_term(not_result);

        let result = encoder.check_sat();
        eprintln!("two conditions with shapes: {result:?}");
        eprintln!(
            "two conditions {}",
            if matches!(result, SolveResult::Unsat(_)) {
                "WORKS"
            } else {
                "BLOCKED"
            }
        );
    }
}
