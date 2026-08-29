// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Seq (logical sequence) encoding: normalization, axioms,
//! shape constraints, and index-mut synthesis.
//!
//! Extracted from `seq.rs` as part of #1669 structural decomposition.

#[cfg(test)]
mod seq_encoding_tests {
    use std::{borrow::Cow, collections::HashSet, sync::Arc};

    use ay_dpll::api::{FuncDecl, SolveResult, Sort, Term, TermKind};
    use ntest::timeout;
    use trust_wp_core::formula::{intern_sort_name, BinOp, ExprSort, MatchArm, Pattern, PureExpr};

    use crate::{
        encoder::{
            seq::{collect_view_names_as_seq, expr_produces_seq, normalize_seq_receiver_for_scan},
            AYEncoder, SeqValue,
        },
        tests::helpers::{
            add, and, deref, eq, final_expr, ge, implies, int, logic_fn_call, lt, method_call, var,
            var_with_sort, view,
        },
    };

    fn term_contains_app(encoder: &AYEncoder, term: Term, expected: &str) -> bool {
        matches!(encoder.solver.term_kind(term), TermKind::App { name, .. } if name == expected)
            || encoder
                .solver
                .term_children(term)
                .into_iter()
                .any(|child| term_contains_app(encoder, child, expected))
    }

    fn term_contains_native_seq_equality(encoder: &AYEncoder, term: Term) -> bool {
        if matches!(encoder.solver.term_kind(term), TermKind::App { ref name, num_args: 2 } if name == "=")
        {
            let children = encoder.solver.term_children(term);
            if children.iter().any(|child| {
                crate::encoder::sort_context::is_seq_family_sort(&encoder.solver.get_sort(*child))
            }) {
                return true;
            }
        }
        encoder
            .solver
            .term_children(term)
            .into_iter()
            .any(|child| term_contains_native_seq_equality(encoder, child))
    }

    fn assertions_contain_direct_equality(encoder: &AYEncoder, lhs: Term, rhs: Term) -> bool {
        encoder.solver.assertions().iter().any(|assertion| {
            if !matches!(
                encoder.solver.term_kind(*assertion),
                TermKind::App { ref name, num_args: 2 } if name == "="
            ) {
                return false;
            }
            let children = encoder.solver.term_children(*assertion);
            matches!(children.as_slice(), [left, right]
                if (*left == lhs && *right == rhs) || (*left == rhs && *right == lhs))
        })
    }

    fn finite_seq_projector_assertion_trace() -> Vec<String> {
        let mut encoder = AYEncoder::new_with_quantifiers();
        encoder.force_uninterpreted_seq_sort_for_mixed_datatype();
        encoder.ensure_seq_functions();
        let seq_sort = encoder.get_seq_sort();
        for name in ["projector_a", "projector_b", "projector_c", "projector_d"] {
            let seq = encoder.solver.declare_const(name, seq_sort.clone());
            encoder.seq_offset_term(seq).unwrap();
            encoder.seq_array_term(seq).unwrap();
            encoder.seq_len_term(seq).unwrap();
        }
        encoder
            .solver
            .assertions()
            .iter()
            .map(|term| encoder.solver.format_term(*term))
            .collect()
    }

    fn assert_scan_borrowed(expr: &PureExpr) {
        assert!(matches!(
            normalize_seq_receiver_for_scan(expr),
            Cow::Borrowed(_)
        ));
    }

    fn assert_encode_borrowed(expr: &PureExpr) {
        assert!(matches!(
            AYEncoder::normalize_seq_receiver(expr),
            Cow::Borrowed(_)
        ));
    }

    fn assert_scan_wrapped(expr: &PureExpr, context: &str) {
        let normalized = normalize_seq_receiver_for_scan(expr);
        assert!(
            matches!(normalized, Cow::Owned(_)),
            "{context} should be wrapped for pre-scan"
        );
        assert_eq!(
            normalized.into_owned(),
            PureExpr::View(Arc::new(expr.clone()))
        );
    }

    fn assert_encode_wrapped(expr: &PureExpr, context: &str) {
        let normalized = AYEncoder::normalize_seq_receiver(expr);
        assert!(
            matches!(normalized, Cow::Owned(_)),
            "{context} should be wrapped for encoding"
        );
        assert_eq!(
            normalized.into_owned(),
            PureExpr::View(Arc::new(expr.clone()))
        );
    }

    #[test]
    #[timeout(30000)]
    fn normalize_seq_receiver_helpers_preserve_seq_shaped_receivers() {
        let base_view = PureExpr::View(Arc::new(PureExpr::Var("v".to_string(), None)));
        let push_back = PureExpr::MethodCall {
            receiver: Arc::new(base_view.clone()),
            method: "push_back".to_string(),
            args: vec![PureExpr::Int(1)],
        };
        let len_call = PureExpr::MethodCall {
            receiver: Arc::new(base_view.clone()),
            method: "len".to_string(),
            args: vec![],
        };
        let old_view = PureExpr::Old(Arc::new(base_view.clone()));
        let old_push_back = PureExpr::Old(Arc::new(push_back.clone()));
        let final_seq_empty = final_expr(logic_fn_call("seq_empty", vec![]));
        let raw_var = PureExpr::Var("raw".to_string(), None);
        let old_raw = PureExpr::Old(Arc::new(raw_var.clone()));

        assert_scan_borrowed(&base_view);
        assert_scan_borrowed(&push_back);
        assert_scan_borrowed(&old_view);
        assert_scan_borrowed(&old_push_back);
        assert_scan_borrowed(&final_seq_empty);

        assert_scan_wrapped(&raw_var, "non-view receiver");
        assert_scan_wrapped(&old_raw, "non-seq old receiver");
        assert_scan_wrapped(&len_call, "non-push_back method receiver");

        assert_encode_borrowed(&base_view);
        assert_encode_borrowed(&push_back);
        assert_encode_borrowed(&old_view);
        assert_encode_borrowed(&old_push_back);
        assert_encode_borrowed(&final_seq_empty);

        assert_encode_wrapped(&raw_var, "non-view receiver");
        assert_encode_wrapped(&old_raw, "non-seq old receiver");
        assert_encode_wrapped(&len_call, "non-push_back method receiver");
    }

    #[test]
    #[timeout(30000)]
    fn expr_produces_seq_tracks_nested_shapes() {
        let push_back = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "v".to_string(),
                None,
            )))),
            method: "push_back".to_string(),
            args: vec![PureExpr::Int(1)],
        };
        let len_call = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "v".to_string(),
                None,
            )))),
            method: "len".to_string(),
            args: vec![],
        };
        let tail_call = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "v".to_string(),
                None,
            )))),
            method: "tail".to_string(),
            args: vec![],
        };
        let match_expr = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("tag".to_string(), None)),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: PureExpr::Int(0),
                },
                MatchArm {
                    pattern: Pattern::Binding("x".to_string()),
                    body: push_back.clone(),
                },
            ],
        };
        let wrapped_push = PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Final(
            Arc::new(push_back.clone()),
        )))));

        assert!(expr_produces_seq(&push_back));
        assert!(expr_produces_seq(&PureExpr::LogicFnCall {
            name: "seq".to_string(),
            args: vec![PureExpr::Int(0)],
        }));
        assert!(expr_produces_seq(&wrapped_push));
        assert!(expr_produces_seq(&PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(PureExpr::Int(0)),
            Arc::new(push_back.clone())
        )));
        assert!(expr_produces_seq(&match_expr));
        assert!(expr_produces_seq(&PureExpr::Let {
            var: "tmp".to_string(),
            value: Arc::new(PureExpr::Int(7)),
            body: Arc::new(push_back),
        }));
        assert!(expr_produces_seq(&tail_call));

        assert!(!expr_produces_seq(&len_call));
        assert!(!expr_produces_seq(&PureExpr::Var("x".to_string(), None)));
    }

    /// Verify `expr_produces_seq` recognizes `concat`, `seq_empty`, `Seq::empty`,
    /// `reverse`, `subsequence`, LetAssume, and rejects non-Seq operations (#1380 AC1).
    #[test]
    #[timeout(30000)]
    fn expr_produces_seq_recognizes_all_seq_constructors() {
        let v = PureExpr::View(Arc::new(PureExpr::Var("v".to_string(), None)));
        let mc = |m: &str| PureExpr::MethodCall {
            receiver: Arc::new(v.clone()),
            method: m.to_string(),
            args: vec![],
        };
        let lfn = |n: &str| PureExpr::LogicFnCall {
            name: n.to_string(),
            args: vec![],
        };
        // Seq-producing methods and logic fns
        for expr in [mc("concat"), mc("reverse"), mc("subsequence")] {
            assert!(expr_produces_seq(&expr), "{expr:?} should produce Seq");
        }
        for expr in [lfn("seq_empty"), lfn("Seq::empty")] {
            assert!(expr_produces_seq(&expr), "{expr:?} should produce Seq");
        }
        // LetAssume propagation
        assert!(expr_produces_seq(&PureExpr::LetAssume {
            assumption: Arc::new(PureExpr::Bool(true)),
            body: Arc::new(lfn("seq_empty")),
        }));
        // Negative cases
        assert!(!expr_produces_seq(&mc("get")));
        assert!(!expr_produces_seq(&PureExpr::Int(42)));
        assert!(!expr_produces_seq(&lfn("other_fn")));
    }

    /// Verify the production finite projector for `seq_empty` has length 0.
    ///
    /// Raw UF projector applications are deliberately outside the observed
    /// finite lane; callers must use `seq_len_term` to obtain its stable,
    /// certified component.
    #[test]
    #[timeout(30000)]
    fn encode_seq_empty_produces_valid_empty_seq() {
        let mut encoder = AYEncoder::new();
        let empty = encoder.encode_seq_empty();

        let len = encoder
            .seq_len_term(empty)
            .expect("empty length should use the observed component");
        let zero = encoder.solver.int_const(0);
        let len_neq = encoder.solver.neq(len, zero);
        encoder.assert_term(len_neq);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "len(seq_empty) != 0 should be unsatisfiable (axiom forces len == 0); got: {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn collect_view_names_as_seq_recurses_through_wrappers_and_branches() {
        let expr = PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "lhs".to_string(),
                None,
            )))),
            Arc::new(PureExpr::Match {
                scrutinee: Arc::new(PureExpr::Var("tag".to_string(), None)),
                arms: vec![
                    MatchArm {
                        pattern: Pattern::Wildcard,
                        body: PureExpr::Old(Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                            "hist".to_string(),
                            None,
                        ))))),
                    },
                    MatchArm {
                        pattern: Pattern::Binding("x".to_string()),
                        body: PureExpr::Let {
                            var: "tmp".to_string(),
                            value: Arc::new(PureExpr::Int(0)),
                            body: Arc::new(PureExpr::Deref(Arc::new(PureExpr::View(Arc::new(
                                PureExpr::Final(Arc::new(PureExpr::Var("res".to_string(), None))),
                            ))))),
                        },
                    },
                ],
            }),
        );

        let mut names = HashSet::new();
        collect_view_names_as_seq(&expr, &mut names);

        assert!(names.contains("lhs_view"));
        assert!(names.contains("old_hist_view"));
        assert!(names.contains("hist_view"));
        assert!(names.contains("final_res_view"));
        assert_eq!(names.len(), 4);
    }

    pub(crate) fn seq_symbols(
        encoder: &mut AYEncoder,
    ) -> (
        FuncDecl,
        FuncDecl,
        FuncDecl,
        FuncDecl,
        FuncDecl,
        FuncDecl,
        Term,
    ) {
        encoder.ensure_seq_functions();
        let seq_funcs = encoder
            .seq_state
            .funcs()
            .expect("ensure_seq_functions should initialize seq funcs");
        (
            seq_funcs.seq_len.clone(),
            seq_funcs.seq_index_logic.clone(),
            seq_funcs.seq_push_back.clone(),
            seq_funcs.seq_contains.clone(),
            seq_funcs.seq_subsequence.clone(),
            seq_funcs.seq_concat.clone(),
            seq_funcs.seq_empty,
        )
    }

    fn assert_seq_contains_axioms_for_test(encoder: &mut AYEncoder) {
        let seq_sort = encoder.get_seq_sort();
        let seq_funcs = encoder
            .seq_state
            .funcs()
            .expect("seq funcs should be initialized")
            .clone();
        encoder.assert_seq_contains_axioms(&seq_sort, &seq_funcs);
    }

    fn assert_seq_concat_axioms_for_test(encoder: &mut AYEncoder) {
        let seq_sort = encoder.get_seq_sort();
        let seq_funcs = encoder
            .seq_state
            .funcs()
            .expect("seq funcs should be initialized")
            .clone();
        encoder.assert_seq_concat_axioms(&seq_sort, &seq_funcs);
    }

    #[test]
    #[timeout(30000)]
    fn ensure_seq_theory_leaves_operation_axioms_lazy_until_used() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        assert!(
            !encoder.seq_state.get_axioms_asserted(),
            "initializing Seq theory alone must not assert get axioms"
        );
        assert!(
            !encoder.seq_state.contains_axioms_asserted(),
            "initializing Seq theory alone must not assert recursive membership axioms"
        );
        assert!(
            !encoder.seq_state.concat_axioms_asserted(),
            "initializing Seq theory alone must not assert concat axioms"
        );

        let get_expr = method_call(view(var("s")), "get", vec![int(0)]);
        encoder
            .encode_pure(&get_expr)
            .expect("Seq get should encode");
        assert!(
            encoder.seq_state.get_axioms_asserted(),
            "encoding a real Seq get call must demand get axioms"
        );

        let mut encoder = AYEncoder::new();
        let contains_expr = method_call(view(var("s")), "contains", vec![int(1)]);
        encoder
            .encode_pure(&contains_expr)
            .expect("Seq contains should encode");
        assert!(
            encoder.seq_state.contains_axioms_asserted(),
            "encoding a real Seq contains call must demand membership axioms"
        );

        let mut encoder = AYEncoder::new();
        let concat_expr = method_call(view(var("s")), "concat", vec![view(var("t"))]);
        encoder
            .encode_pure(&concat_expr)
            .expect("Seq concat should encode");
        assert!(
            encoder.seq_state.concat_axioms_asserted(),
            "encoding a real Seq concat call must demand concat axioms"
        );
    }

    #[test]
    fn finite_concat_setup_keeps_ground_queries_quantifier_free() {
        let mut encoder = AYEncoder::new();
        let seq_sort = encoder.get_seq_sort();
        let funcs = encoder.ensure_seq_theory();

        encoder.assert_seq_concat_axioms(&seq_sort, &funcs);

        assert!(encoder.seq_state.concat_axioms_asserted());
        assert!(encoder
            .solver
            .assertions()
            .iter()
            .all(|term| encoder.solver.term_kind(*term) != TermKind::Forall));
    }

    #[test]
    #[timeout(30000)]
    fn seq_axiom_contains_empty_is_false() {
        let mut encoder = AYEncoder::new();
        let (_, _, _, seq_contains, _, _, seq_empty) = seq_symbols(&mut encoder);
        assert_seq_contains_axioms_for_test(&mut encoder);
        let probe = encoder
            .solver
            .declare_const("__seq_contains_probe", Sort::Int);
        let contains = encoder.solver.apply(&seq_contains, &[seq_empty, probe]);
        let true_term = encoder.solver.bool_const(true);
        let violation = encoder.solver.eq(contains, true_term);

        encoder.assert_term(violation);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "contains(seq_empty, x) = true should violate axiom 9, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn seq_axiom_contains_push_back_matches_membership_rule() {
        let mut encoder = AYEncoder::new();
        let (_, _, seq_push_back, seq_contains, _, _, seq_empty) = seq_symbols(&mut encoder);
        assert_seq_contains_axioms_for_test(&mut encoder);

        let pushed = encoder
            .solver
            .declare_const("__seq_contains_pushed", Sort::Int);
        let query = encoder
            .solver
            .declare_const("__seq_contains_query", Sort::Int);
        let with_push = encoder.solver.apply(&seq_push_back, &[seq_empty, pushed]);
        let lhs = encoder.solver.apply(&seq_contains, &[with_push, query]);
        let query_is_pushed = encoder.solver.eq(query, pushed);
        let prior_contains = encoder.solver.apply(&seq_contains, &[seq_empty, query]);
        let rhs = encoder.solver.or(query_is_pushed, prior_contains);
        let violation = encoder.solver.neq(lhs, rhs);

        encoder.assert_term(violation);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "contains(push_back(s, v), x) mismatch should violate axiom 10, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn seq_axiom_subsequence_len_matches_clamped_range() {
        // Build concrete [10,20,30], subsequence(1,3), check len == 2.
        // Uses encode_pure to exercise Array+Length path (#1317).
        let base = method_call(
            method_call(
                method_call(view(var("v")), "push_back", vec![int(10)]),
                "push_back",
                vec![int(20)],
            ),
            "push_back",
            vec![int(30)],
        );
        let subseq = method_call(base, "subsequence", vec![int(1), int(3)]);
        let len_subseq = method_call(subseq, "len", vec![]);
        let formula = eq(len_subseq, int(2));

        let mut encoder = AYEncoder::new();
        let formula_term = encoder.encode_pure(&formula).expect("encode_pure");
        let negated = encoder.solver.not(formula_term);
        encoder.assert_term(negated);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "len(subsequence([10,20,30], 1, 3)) should equal 2, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn seq_axiom_subsequence_index_uses_from_plus_offset() {
        // subsequence([10,20,30], 1, 3).index_logic(0) == 20 &&
        // subsequence([10,20,30], 1, 3).index_logic(1) == 30
        // Uses encode_pure to exercise Array+Length path (#1317).
        // Build from seq_empty (concrete len=0, offset=0) so the solver can
        // resolve array positions without quantified subsequence axioms.
        let empty = PureExpr::LogicFnCall {
            name: "seq_empty".to_string(),
            args: vec![],
        };
        let base = method_call(
            method_call(
                method_call(empty, "push_back", vec![int(10)]),
                "push_back",
                vec![int(20)],
            ),
            "push_back",
            vec![int(30)],
        );
        let subseq = method_call(base, "subsequence", vec![int(1), int(3)]);
        let idx0 = method_call(subseq.clone(), "index_logic", vec![int(0)]);
        let idx1 = method_call(subseq, "index_logic", vec![int(1)]);
        let formula = and(eq(idx0, int(20)), eq(idx1, int(30)));

        let mut encoder = AYEncoder::new();
        let formula_term = encoder.encode_pure(&formula).expect("encode_pure");
        let negated = encoder.solver.not(formula_term);
        encoder.assert_term(negated);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "subsequence index should use from+offset, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn seq_axiom_concat_right_index_uses_len_left_offset() {
        let mut encoder = AYEncoder::new();
        let left = var_with_sort("concat_left", ExprSort::Seq);
        let right = var_with_sort("concat_right", ExprSort::Seq);
        let right_idx = var("concat_right_index");
        let left_len = method_call(left.clone(), "len", vec![]);
        let right_len = method_call(right.clone(), "len", vec![]);
        let concat = method_call(left, "concat", vec![right.clone()]);
        let concat_offset = add(left_len, right_idx.clone());
        let concat_idx = method_call(concat, "index_logic", vec![concat_offset]);
        let right_only_idx = method_call(right, "index_logic", vec![right_idx.clone()]);
        let in_bounds = and(ge(right_idx.clone(), int(0)), lt(right_idx, right_len));
        let axiom_instance = implies(in_bounds, eq(concat_idx, right_only_idx));

        encoder.register_sort_hints(std::slice::from_ref(&axiom_instance));
        let axiom_term = encoder
            .encode_pure(&axiom_instance)
            .expect("right-side concat index law should encode through production projectors");
        let violation = encoder.solver.not(axiom_term);

        encoder.assert_term(violation);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "right-side concat indexing should enforce axiom 17, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn seq_axiom_set_write_read_same() {
        // set(push_back(empty, 42), 0, 99).index_logic(0) == 99
        // Uses encode_pure to exercise Array+Length path (#1317).
        // Build from seq_empty (concrete len=0, offset=0) so the solver can
        // resolve the updated slot without quantified set axioms.
        let empty = PureExpr::LogicFnCall {
            name: "seq_empty".to_string(),
            args: vec![],
        };
        let base = method_call(empty, "push_back", vec![int(42)]);
        let updated = method_call(base, "set", vec![int(0), int(99)]);
        let read_back = method_call(updated, "index_logic", vec![int(0)]);
        let formula = eq(read_back, int(99));

        let mut encoder = AYEncoder::new();
        let formula_term = encoder.encode_pure(&formula).expect("encode_pure");
        let negated = encoder.solver.not(formula_term);
        encoder.assert_term(negated);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "index(set(s, 0, 99), 0) should equal 99, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn seq_axiom_set_frame_preserves_other_indices() {
        // set([10, 20], 0, 99).index_logic(1) == 20
        // Uses encode_pure to exercise Array+Length path (#1317).
        // Build from seq_empty (concrete len=0, offset=0) so the solver can
        // resolve array positions without quantified set-frame axioms.
        let empty = PureExpr::LogicFnCall {
            name: "seq_empty".to_string(),
            args: vec![],
        };
        let base = method_call(
            method_call(empty, "push_back", vec![int(10)]),
            "push_back",
            vec![int(20)],
        );
        let updated = method_call(base, "set", vec![int(0), int(99)]);
        let read_at_1 = method_call(updated, "index_logic", vec![int(1)]);
        let formula = eq(read_at_1, int(20));

        let mut encoder = AYEncoder::new();
        let formula_term = encoder.encode_pure(&formula).expect("encode_pure");
        let negated = encoder.solver.not(formula_term);
        encoder.assert_term(negated);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "index(set(s, 0, v), 1) should equal 20, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn seq_axiom_set_preserves_length() {
        // len(set(push_back(empty, 5), 0, 99)) == len(push_back(empty, 5))
        // Uses encode_pure to exercise Array+Length path (#1317).
        let base = method_call(view(var("v")), "push_back", vec![int(5)]);
        let updated = method_call(base.clone(), "set", vec![int(0), int(99)]);
        let len_updated = method_call(updated, "len", vec![]);
        let len_base = method_call(base, "len", vec![]);
        let formula = eq(len_updated, len_base);

        let mut encoder = AYEncoder::new();
        let formula_term = encoder.encode_pure(&formula).expect("encode_pure");
        let negated = encoder.solver.not(formula_term);
        encoder.assert_term(negated);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "len(set(s, i, v)) should equal len(s), got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn index_mut_pattern_accepts_methodcall_receiver_view_final() {
        let index_side = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
                PureExpr::Var("a".to_string(), None),
            ))))),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(2)],
        };
        let value_side = PureExpr::Int(3);

        let (target_name, idx_expr, val_expr) =
            AYEncoder::extract_index_mut_pattern(&index_side, &value_side, None)
                .expect("expected MethodCall(View(Final(..))) pattern to match");

        assert_eq!(target_name, "final_a_view");
        assert_eq!(idx_expr, &PureExpr::Int(2));
        assert_eq!(val_expr, &PureExpr::Int(3));
    }

    #[test]
    #[timeout(30000)]
    fn index_mut_pattern_accepts_view_wrapped_methodcall_final_receiver() {
        let index_side = PureExpr::View(Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "a".to_string(),
                None,
            )))),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(2)],
        }));
        let value_side = PureExpr::Int(3);

        let (target_name, idx_expr, val_expr) =
            AYEncoder::extract_index_mut_pattern(&index_side, &value_side, None)
                .expect("expected View(MethodCall(Final(..))) pattern to match");

        assert_eq!(target_name, "final_a_view");
        assert_eq!(idx_expr, &PureExpr::Int(2));
        assert_eq!(val_expr, &PureExpr::Int(3));
    }

    #[test]
    #[timeout(30000)]
    fn index_mut_seq_value_synthesizes_for_view_wrapped_methodcall() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();

        let seq_sort = encoder.get_seq_sort();
        let source_term = encoder
            .get_or_declare_var("a_view", seq_sort.clone())
            .expect("declare a_view");
        let target_term = encoder
            .get_or_declare_var("final_a_view", seq_sort)
            .expect("declare final_a_view");

        let seq_empty = encoder
            .seq_state
            .funcs()
            .expect("seq functions initialized")
            .seq_empty;
        let source_value = encoder
            .seq_state
            .get_seq_value_cloned(&seq_empty)
            .expect("seq_empty SeqValue registered");
        encoder
            .seq_state
            .insert_seq_value(source_term, source_value);

        let assumption = PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                    "a".to_string(),
                    None,
                )))),
                method: "index_logic".to_string(),
                args: vec![PureExpr::Int(2)],
            }))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(3)),
        );

        encoder
            .try_synthesize_index_mut_seq_value(&assumption, None)
            .expect("index_mut synthesis should not fail");

        assert!(
            encoder.seq_state.has_seq_value(&target_term),
            "IndexMut SeqValue synthesis should register final_a_view for \
             View(MethodCall(Final(..))) assumptions"
        );
        assert!(
            encoder.seq_state.needs_index_ground_terms(),
            "IndexMut synthesis must enable needs_index_ground_terms (#1640)"
        );
    }

    #[test]
    #[timeout(30000)]
    fn index_mut_synthesis_enables_ground_terms_flag() {
        // Verify that try_synthesize_index_mut_seq_value sets
        // needs_index_ground_terms = true so that subsequent
        // seq_index_term calls emit bridge ground instances (#1640).
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        assert!(
            !encoder.seq_state.needs_index_ground_terms(),
            "flag should start false"
        );

        let seq_sort = encoder.get_seq_sort();
        let source_term = encoder
            .get_or_declare_var("a_view", seq_sort.clone())
            .expect("declare a_view");
        let _target_term = encoder
            .get_or_declare_var("final_a_view", seq_sort)
            .expect("declare final_a_view");

        // Seed source SeqValue from seq_empty.
        let seq_empty = encoder
            .seq_state
            .funcs()
            .expect("seq functions initialized")
            .seq_empty;
        let source_value = encoder
            .seq_state
            .get_seq_value_cloned(&seq_empty)
            .expect("seq_empty SeqValue registered");
        encoder
            .seq_state
            .insert_seq_value(source_term, source_value);

        // MethodCall { receiver: View(Final(...)), method: "index_logic" }
        let assumption = PureExpr::BinOp(
            Arc::new(PureExpr::MethodCall {
                receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Final(Arc::new(
                    PureExpr::Var("a".to_string(), None),
                ))))),
                method: "index_logic".to_string(),
                args: vec![PureExpr::Int(0)],
            }),
            BinOp::Eq,
            Arc::new(PureExpr::Int(42)),
        );

        encoder
            .try_synthesize_index_mut_seq_value(&assumption, None)
            .expect("index_mut synthesis should not fail");
        assert!(
            encoder.seq_state.needs_index_ground_terms(),
            "flag must be true after IndexMut synthesis"
        );
    }

    #[test]
    #[timeout(30000)]
    fn seq_index_term_prefers_seq_index_logic_uf_when_ground_terms_enabled() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        let seq_sort = encoder.get_seq_sort();
        let seq_term = encoder
            .get_or_declare_var("x_view", seq_sort)
            .expect("declare x_view");
        encoder.seq_state.set_needs_index_ground_terms();
        let zero = encoder.solver.int_const(0);
        let seq_index_logic = encoder
            .seq_state
            .funcs()
            .expect("seq functions initialized")
            .seq_index_logic
            .clone();

        let indexed = encoder
            .seq_index_term(seq_term, zero)
            .expect("seq_index_term should encode");
        let expected = encoder.solver.apply(&seq_index_logic, &[seq_term, zero]);

        assert_eq!(
            indexed, expected,
            "ground-term mode should return the triggerable seq_index_logic UF"
        );
    }

    #[test]
    #[timeout(30000)]
    fn seq_index_term_returns_error_for_seq_sorted_index_fallback_path() {
        // Regression test for #1554 (fallback path): seq_index_term should
        // return an EncodingError instead of panicking when the index argument
        // has Seq sort. This test exercises the UF projector fallback path
        // (no SeqValue entry in the registry).
        let mut encoder = AYEncoder::new();
        let (_, _, seq_push_back, _, _, _, seq_empty) = seq_symbols(&mut encoder);

        // Build a sequence via raw UF apply (no SeqValue registration)
        let val = encoder.solver.int_const(42);
        let seq = encoder.solver.apply(&seq_push_back, &[seq_empty, val]);

        // Create a Seq-sorted "index" term
        let seq_sort = encoder.get_seq_sort();
        let bad_index = encoder.solver.fresh_var("bad_seq_index", seq_sort);

        let result = encoder.seq_index_term(seq, bad_index);
        assert!(
            result.is_err(),
            "seq_index_term should return error for Seq-sorted index (fallback path)"
        );
    }

    #[test]
    #[timeout(30000)]
    fn seq_index_term_returns_error_for_seq_sorted_index_fast_path() {
        // Regression test for #1554 (fast path): seq_index_term should return
        // an EncodingError instead of panicking when the index argument has
        // Seq sort. This test exercises the fast path where the receiver has
        // a concrete SeqValue in the registry.
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();

        // Register a concrete SeqValue for seq_empty (already done by
        // ensure_seq_functions), so the fast path is exercised.
        let seq_empty = encoder
            .seq_state
            .funcs()
            .expect("seq funcs initialized")
            .seq_empty;

        // Create a Seq-sorted "index" term
        let seq_sort = encoder.get_seq_sort();
        let bad_index = encoder.solver.fresh_var("bad_seq_index_fast", seq_sort);

        let result = encoder.seq_index_term(seq_empty, bad_index);
        assert!(
            result.is_err(),
            "seq_index_term should return error for Seq-sorted index (fast path)"
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("sort") || err_msg.contains("Sort"),
            "error message should mention sort mismatch: {err_msg}"
        );
    }

    /// Sort mismatch in Seq carrier is repaired via `PhantomVariableUpgrade`
    /// (#2567), so len==0 synthesis succeeds after repair instead of
    /// propagating a shape-constraint error.
    #[test]
    #[timeout(30000)]
    fn len_zero_synthesis_repairs_sort_mismatch_via_phantom_upgrade() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        encoder
            .get_or_declare_var("x_view", Sort::Int)
            .expect("declare x_view as Int");

        let assumption = eq(method_call(view(var("x")), "len", vec![]), int(0));
        let result = encoder.try_synthesize_len_zero_seq_value(&assumption, None);
        assert!(
            result.is_ok(),
            "len==0 synthesis repairs Int→Seq sort mismatch via PhantomVariableUpgrade"
        );
    }

    /// Reference-like Seq annotations should still trigger len==0 synthesis.
    /// Slice receivers arrive as `Ref(Seq)` rather than raw `Seq`, so the
    /// len-zero bridge must accept the reference wrapper and seed the concrete
    /// empty `SeqValue` instead of falling back to the aux-bridge path.
    #[test]
    #[timeout(30000)]
    fn len_zero_synthesis_accepts_reference_like_seq_annotations() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();

        let expr = eq(
            method_call(
                view(var_with_sort("x", ExprSort::Ref(Box::new(ExprSort::Seq)))),
                "len",
                vec![],
            ),
            int(0),
        );

        let result = encoder.try_synthesize_len_zero_seq_value(&expr, None);
        assert!(
            result.is_ok(),
            "Ref(Seq) annotation should still synthesize a concrete empty SeqValue"
        );

        let target = encoder.var_term("x_view").expect("x_view");
        assert!(
            encoder.has_seq_value(target),
            "x_view should be registered as a concrete empty SeqValue"
        );
    }

    #[test]
    #[timeout(30000)]
    fn asserted_len_zero_synthesis_records_exact_finite_length() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        let expr = eq(method_call(view(var("x")), "len", vec![]), int(0));

        encoder
            .try_synthesize_asserted_len_zero_seq_value(&expr, None)
            .expect("asserted len==0 synthesis should succeed");

        let target = encoder.var_term("x_view").expect("x_view");
        assert_eq!(
            encoder
                .seq_state
                .get_seq_value(&target)
                .and_then(|value| value.known_len),
            Some(0),
            "an asserted zero length is exact finite metadata"
        );
    }

    #[test]
    #[timeout(30000)]
    fn len_zero_synthesis_accepts_vec_datatype_and_reconciles_existing_seq_value() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();

        let seq_sort = encoder.get_seq_sort();
        let target = encoder
            .get_or_declare_var("x_view", seq_sort)
            .expect("declare x_view");
        let zero = encoder.solver.int_const(0);
        let stale_len = encoder.solver.fresh_var("preexisting_len", Sort::Int);
        let stale_arr = encoder.solver.const_array(Sort::Int, zero);
        encoder.insert_seq_value(
            target,
            crate::encoder::SeqValue {
                arr: stale_arr,
                len: stale_len,
                offset: zero,
                known_len: None,
            },
        );

        let expr = eq(
            method_call(
                view(var_with_sort(
                    "x",
                    ExprSort::Datatype(intern_sort_name("std::vec::Vec")),
                )),
                "len",
                vec![],
            ),
            int(0),
        );

        encoder
            .try_synthesize_len_zero_seq_value(&expr, None)
            .expect("Vec datatype len==0 synthesis should not fail");

        let synthesized = encoder
            .seq_state
            .get_seq_value_cloned(&target)
            .expect("x_view should have a synthesized SeqValue");
        assert_eq!(synthesized.len, stale_len);
        assert_eq!(synthesized.known_len, None);

        let nonzero = encoder.solver.neq(stale_len, zero);
        encoder.assert_term(nonzero);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "explicit len==0 must constrain, not replace, an existing Seq component; got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn chained_push_back_reconstruction_proves_indexed_elements() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();

        let vec_sort = ExprSort::Datatype(intern_sort_name("std::vec::Vec"));
        let x = var_with_sort("x", vec_sort);
        let x_view = view(x.clone());
        let final_x_view = view(final_expr(x.clone()));
        let final_final_x_view = view(final_expr(final_expr(x)));

        let requires = vec![
            eq(
                final_final_x_view.clone(),
                method_call(final_x_view.clone(), "push_back", vec![int(1)]),
            ),
            eq(
                final_x_view,
                method_call(x_view.clone(), "push_back", vec![int(0)]),
            ),
            eq(method_call(x_view, "len", vec![]), int(0)),
        ];

        encoder
            .try_reconstruct_chained_push_back_chain(&requires, None)
            .expect("chained push_back reconstruction should not fail");

        let target = encoder
            .var_term("final_x_final_view")
            .expect("final_x_final_view should be declared");
        let synthesized = encoder
            .seq_state
            .get_seq_value_cloned(&target)
            .expect("final_x_final_view should have reconstructed SeqValue");
        assert_eq!(synthesized.len, encoder.solver.int_const(2));

        let zero = encoder.solver.int_const(0);
        let one = encoder.solver.int_const(1);
        let idx0 = encoder
            .seq_index_term(target, zero)
            .expect("index 0 should encode");
        let idx1 = encoder
            .seq_index_term(target, one)
            .expect("index 1 should encode");
        let idx0_ok = encoder.eq_term(idx0, zero);
        let idx1_ok = encoder.eq_term(idx1, one);
        let both = encoder.solver.and(idx0_ok, idx1_ok);
        let negated = encoder.solver.not(both);
        encoder.assert_term(negated);

        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "reconstructed chained push_back SeqValue should prove [0, 1], got {result:?}"
        );
    }

    /// Build the `create_arr` precondition shape (5 chained `push_back`s) with
    /// the push_back assumptions ordered BEFORE the base `len() == 0` fact, the
    /// scrambled order the driver actually emits. This is the
    /// `index_range::create_arr` reproduction: without pre-seeding the ground
    /// chain, the per-assumption encoding emits symbolic-index store shape
    /// constraints whose Array reasoning times out in ay. The pre-seed pass
    /// materializes the ground store-chain first.
    fn create_arr_requires() -> Vec<PureExpr> {
        let vec_sort = ExprSort::Datatype(intern_sort_name("std::vec::Vec"));
        let x = var_with_sort("x", vec_sort);
        let v0 = view(x.clone());
        let v1 = view(final_expr(x.clone()));
        let v2 = view(final_expr(final_expr(x.clone())));
        let v3 = view(final_expr(final_expr(final_expr(x.clone()))));
        let v4 = view(final_expr(final_expr(final_expr(final_expr(x.clone())))));
        let v5 = view(final_expr(final_expr(final_expr(final_expr(final_expr(
            x.clone(),
        ))))));
        // push_back assumptions FIRST (intentionally before the len==0 base),
        // and in scrambled order, to mirror the real driver output.
        vec![
            eq(v5, method_call(v4.clone(), "push_back", vec![int(4)])),
            eq(
                v2.clone(),
                method_call(v1.clone(), "push_back", vec![int(1)]),
            ),
            eq(v4, method_call(v3.clone(), "push_back", vec![int(3)])),
            eq(v1, method_call(v0.clone(), "push_back", vec![int(0)])),
            eq(v3, method_call(v2, "push_back", vec![int(2)])),
            eq(method_call(v0, "len", vec![]), int(0)),
        ]
    }

    /// Setup mirror of `setup_verification_encoder`: pre-seed the ground chain,
    /// then encode every requirement (which now resolves push_back receivers
    /// against the concrete registry), then run the post-pass reconstruction
    /// (a no-op for the pre-seeded base).
    fn encode_create_arr_requires(encoder: &mut AYEncoder, requires: &[PureExpr]) {
        encoder
            .preseed_long_chained_push_back_chain(requires, None)
            .expect("pre-seed chained push_back reconstruction should not fail");
        for req in requires {
            let term = encoder.encode_pure(req).expect("requirement should encode");
            let term = encoder.coerce_bool_operand(term);
            encoder.assert_term(term);
            encoder
                .try_synthesize_len_zero_seq_value(req, None)
                .expect("len-zero synthesis should not fail");
        }
        encoder
            .try_reconstruct_chained_push_back_chain(requires, None)
            .expect("post-pass chained push_back reconstruction should not fail");
    }

    /// SOUNDNESS + capability: the genuine `create_arr` postcondition
    /// (`result@.len() == 5` and `result[k]@ == k` for k in 0..5) is UNSAT
    /// when negated — i.e., entailed — and the pre-seed ordering does not
    /// regress this.
    #[test]
    #[timeout(60000)]
    fn create_arr_chain_proves_len_and_indices() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        let requires = create_arr_requires();
        encode_create_arr_requires(&mut encoder, &requires);

        let target = encoder
            .var_term("final_x_final_final_final_final_view")
            .expect("final view carrier should be declared");

        // len == 5
        let five = encoder.solver.int_const(5);
        let len_term = encoder.seq_len_term(target).expect("len should encode");
        let mut goal = encoder.eq_term(len_term, five);
        // result[k] == k for k in 0..5
        for k in 0..5 {
            let k_term = encoder.solver.int_const(k);
            let idx = encoder
                .seq_index_term(target, k_term)
                .expect("index should encode");
            let idx_ok = encoder.eq_term(idx, k_term);
            goal = encoder.solver.and(goal, idx_ok);
        }
        let negated = encoder.solver.not(goal);
        encoder.assert_term(negated);

        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "create_arr chain should prove len==5 && result[k]==k, got {result:?}"
        );
    }

    /// FALSE-ACCEPT GUARD: a WRONG postcondition must NOT be provable. With the
    /// exact same ground chain, `result@.len() == 6` is genuinely SAT (the
    /// chain has length 5), so its negation must remain satisfiable — the
    /// pre-seed must never let ay prove a false goal.
    #[test]
    #[timeout(60000)]
    fn create_arr_chain_does_not_prove_wrong_len() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        let requires = create_arr_requires();
        encode_create_arr_requires(&mut encoder, &requires);

        let target = encoder
            .var_term("final_x_final_final_final_final_view")
            .expect("final view carrier should be declared");
        let six = encoder.solver.int_const(6);
        let len_term = encoder.seq_len_term(target).expect("len should encode");
        // Negation of the FALSE goal `len == 6`: `len != 6`. Since len is truly
        // 5, `len != 6` is valid, so the solver must NOT report Unsat (that
        // would mean it proved the false `len == 6`).
        let wrong = encoder.eq_term(len_term, six);
        let negated = encoder.solver.not(wrong);
        encoder.assert_term(negated);

        let result = encoder.check_sat();
        assert!(
            !matches!(result, SolveResult::Unsat(_)),
            "pre-seed must not let ay prove the false goal len==6; got {result:?}"
        );
    }

    /// FALSE-ACCEPT GUARD: a wrong indexed element (`result[2]@ == 9`) must not
    /// be provable. The genuine element is 2, so the negation must stay SAT.
    #[test]
    #[timeout(60000)]
    fn create_arr_chain_does_not_prove_wrong_index() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        let requires = create_arr_requires();
        encode_create_arr_requires(&mut encoder, &requires);

        let target = encoder
            .var_term("final_x_final_final_final_final_view")
            .expect("final view carrier should be declared");
        let two = encoder.solver.int_const(2);
        let nine = encoder.solver.int_const(9);
        let idx2 = encoder
            .seq_index_term(target, two)
            .expect("index 2 should encode");
        let wrong = encoder.eq_term(idx2, nine);
        let negated = encoder.solver.not(wrong);
        encoder.assert_term(negated);

        let result = encoder.check_sat();
        assert!(
            !matches!(result, SolveResult::Unsat(_)),
            "pre-seed must not let ay prove the false goal result[2]==9; got {result:?}"
        );
    }

    /// ITE branch conditions also need the len-zero bridge because returned
    /// `Option` bodies are often encoded as `if self.len() == 0 { None } else { ... }`.
    #[test]
    #[timeout(30000)]
    fn ite_condition_len_zero_synthesizes_seq_value() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();

        let expr = PureExpr::Ite(
            Arc::new(eq(method_call(view(var("x")), "len", vec![]), int(0))),
            Arc::new(PureExpr::Bool(true)),
            Arc::new(PureExpr::Bool(false)),
        );

        let _ = encoder.encode_pure(&expr).expect("ITE should encode");

        let x_view_term = encoder
            .var_term("x_view")
            .expect("x_view should be declared");
        assert!(
            encoder.seq_state_for_test().has_seq_value(&x_view_term),
            "len-zero ITE condition should seed a concrete SeqValue for x_view"
        );
    }

    #[test]
    #[timeout(30000)]
    fn ite_len_zero_condition_does_not_escape_the_selected_branch() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        let expr = PureExpr::Ite(
            Arc::new(eq(method_call(view(var("x")), "len", vec![]), int(0))),
            Arc::new(PureExpr::Bool(true)),
            Arc::new(PureExpr::Bool(false)),
        );

        let term = encoder.encode_pure(&expr).expect("ITE should encode");
        let false_branch = encoder.solver.not(term);
        encoder.assert_term(false_branch);

        let result = encoder.check_sat();
        assert!(
            !matches!(result, SolveResult::Unsat(_)),
            "speculatively encoding len(x)==0 must not make the condition globally true: {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn match_arm_len_zero_does_not_overwrite_existing_seq_value() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();

        let seq_sort = encoder.get_seq_sort();
        let a_view_term = encoder
            .get_or_declare_var("a_view", seq_sort)
            .expect("declare a_view");
        let zero = encoder.solver.int_const(0);
        let stale_len = encoder.solver.int_const(9);
        let stale_arr = encoder.solver.const_array(Sort::Int, zero);
        encoder.seq_state.insert_seq_value(
            a_view_term,
            crate::encoder::SeqValue {
                arr: stale_arr,
                len: stale_len,
                offset: zero,
                known_len: Some(9),
            },
        );

        let expr = PureExpr::Match {
            scrutinee: Arc::new(int(0)),
            arms: vec![MatchArm {
                pattern: Pattern::Wildcard,
                body: eq(method_call(view(var("a")), "len", vec![]), int(0)),
            }],
        };

        let _ = encoder.encode_pure(&expr).expect("match expression");
        let after_len = encoder
            .seq_len_term(a_view_term)
            .expect("a_view length after match encoding");

        assert_eq!(
            after_len, stale_len,
            "inactive/catch-all match arm encoding must not reseed a_view as empty"
        );
    }

    /// `seq_len_term_with_source` should report the source chosen for the
    /// receiver so the aux bridge path is visible during debug tracing.
    #[test]
    #[timeout(30000)]
    fn seq_len_term_reports_concrete_alias_and_aux_sources() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();

        let zero = encoder.solver.int_const(0);
        let empty_arr = encoder.solver.const_array(Sort::Int, zero);
        let seq_sort = encoder.get_seq_sort();

        let concrete = encoder
            .solver
            .declare_const("concrete_seq", seq_sort.clone());
        encoder.seq_state.insert_seq_value(
            concrete,
            crate::encoder::SeqValue {
                arr: empty_arr,
                len: zero,
                offset: zero,
                known_len: Some(0),
            },
        );
        let (concrete_len, concrete_source) = encoder
            .seq_len_term_with_source(concrete)
            .expect("concrete seq len should resolve");
        assert_eq!(concrete_len, zero);
        assert_eq!(
            concrete_source,
            crate::encoder::seq::SeqLenSource::ConcreteSeqValue
        );

        let raw_vec = encoder
            .solver
            .declare_const("raw_vec", Sort::Uninterpreted("std::vec::Vec".to_string()));
        let coerced = encoder.coerce_to_seq(raw_vec);
        encoder.seq_state.insert_seq_value(
            coerced,
            crate::encoder::SeqValue {
                arr: empty_arr,
                len: zero,
                offset: zero,
                known_len: Some(0),
            },
        );
        let (alias_len, alias_source) = encoder
            .seq_len_term_with_source(raw_vec)
            .expect("alias-backed seq len should resolve");
        assert_eq!(alias_len, zero);
        assert_eq!(
            alias_source,
            crate::encoder::seq::SeqLenSource::AliasBackedSeqValue
        );

        let bridge_seq = encoder.solver.declare_const("bridge_seq", seq_sort);
        let (aux_len, aux_source) = encoder
            .seq_len_term_with_source(bridge_seq)
            .expect("unknown seq len should bridge through the fallback source");
        assert_eq!(
            aux_source,
            crate::encoder::seq::SeqLenSource::AuxLenFallback
        );
        assert!(
            encoder
                .seq_state_for_test()
                .get_seq_len_aux(&bridge_seq)
                .is_some(),
            "fallback should cache the chosen len term"
        );
        assert!(
            !format!("{aux_len:?}").contains("__seq_len_aux_"),
            "fallback should not materialize a synthetic __seq_len_aux_* symbol"
        );
        assert!(
            encoder.seq_state_for_test().has_seq_value(&bridge_seq),
            "aux fallback should also cache a SeqValue bridge for downstream array/offset access"
        );

        let (cached_len, cached_source) = encoder
            .seq_len_term_with_source(bridge_seq)
            .expect("cached fallback len should resolve");
        assert_eq!(cached_len, aux_len);
        assert_eq!(
            cached_source,
            crate::encoder::seq::SeqLenSource::ConcreteSeqValue
        );
    }

    #[test]
    #[timeout(30000)]
    fn all_logic_seq_len_fallback_uses_proxy_for_arithmetic_bounds() {
        let mut encoder = AYEncoder::new_all();
        encoder.ensure_seq_functions();

        let seq_sort = encoder.get_seq_sort();
        let first = encoder
            .solver
            .declare_const("all_logic_seq_first", seq_sort.clone());
        let second = encoder
            .solver
            .declare_const("all_logic_seq_second", seq_sort);
        let (first_len, source) = encoder
            .seq_len_term_with_source(first)
            .expect("unknown All-logic seq len should resolve through proxy");
        let (second_len, _) = encoder
            .seq_len_term_with_source(second)
            .expect("second unknown All-logic seq len should resolve through proxy");

        assert!(encoder.use_seq_len_proxies());
        assert_eq!(source, crate::encoder::seq::SeqLenSource::AuxLenFallback);

        let cached = encoder
            .seq_state_for_test()
            .get_seq_len_aux(&first)
            .expect("proxy-backed len should be cached for the receiver");
        assert_eq!(cached, first_len);

        let same_receiver = encoder.seq_aware_equality_term(first, second);
        let different_lengths = encoder.solver.neq(first_len, second_len);
        encoder.assert_term(same_receiver);
        encoder.assert_term(different_lengths);
        assert!(encoder.solver.assertions().iter().all(|term| {
            !term_contains_app(&encoder, *term, "seq_len")
                && !term_contains_app(&encoder, *term, "seq_offset")
                && !term_contains_native_seq_equality(&encoder, *term)
        }));
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "finite Seq equality must include the length component; got {result:?}"
        );
    }

    #[test]
    fn uflia_uses_finite_projectors_only_outside_quantifier_bodies() {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        encoder.ensure_seq_functions();
        let seq_sort = encoder.get_seq_sort();
        let ground = encoder
            .solver
            .declare_const("uflia_ground_seq", seq_sort.clone());
        let ground_len = encoder.seq_len_term(ground).unwrap();

        assert!(encoder.use_seq_len_proxies());
        assert!(
            encoder
                .solver
                .format_term(ground_len)
                .contains("seq_len_proxy"),
            "ground UFLIA Seq length must use a finite proxy"
        );

        let bound = encoder.solver.declare_const("uflia_bound_seq", seq_sort);
        encoder.quantifier_state.inc_quantifier_depth();
        let bound_len = encoder.seq_len_term(bound).unwrap();
        encoder.quantifier_state.dec_quantifier_depth();
        let rendered = encoder.solver.format_term(bound_len);
        assert!(
            rendered.contains("seq_len") && !rendered.contains("seq_len_proxy"),
            "UFLIA quantifier bodies must retain receiver-dependent projectors, got {rendered}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn finite_zero_length_seq_equality_ignores_unobservable_storage() {
        let mut encoder = AYEncoder::new_all();
        encoder.ensure_seq_functions();
        let seq_sort = encoder.get_seq_sort();
        let first = encoder
            .solver
            .declare_const("zero_len_first", seq_sort.clone());
        let second = encoder.solver.declare_const("zero_len_second", seq_sort);

        let equality = encoder.seq_aware_equality_term(first, second);
        let first_len = encoder.seq_len_term(first).unwrap();
        let second_len = encoder.seq_len_term(second).unwrap();
        let zero = encoder.solver.int_const(0);
        let first_empty = encoder.solver.eq(first_len, zero);
        let second_empty = encoder.solver.eq(second_len, zero);
        encoder.assert_term(first_empty);
        encoder.assert_term(second_empty);

        let negated = encoder.solver.not(equality);
        encoder.assert_term(negated);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "zero-length sequences must compare equal without storage equality, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn finite_zero_length_seq_equality_does_not_constrain_backing_storage() {
        let mut encoder = AYEncoder::new_all();
        encoder.ensure_seq_functions();
        let seq_sort = encoder.get_seq_sort();
        let first = encoder
            .solver
            .declare_const("zero_storage_first", seq_sort.clone());
        let second = encoder
            .solver
            .declare_const("zero_storage_second", seq_sort);

        let equality = encoder.seq_aware_equality_term(first, second);
        let first_len = encoder.seq_len_term(first).unwrap();
        let second_len = encoder.seq_len_term(second).unwrap();
        let first_array = encoder.seq_array_term(first).unwrap();
        let second_array = encoder.seq_array_term(second).unwrap();
        let first_offset = encoder.seq_offset_term(first).unwrap();
        let second_offset = encoder.seq_offset_term(second).unwrap();
        let zero = encoder.solver.int_const(0);
        let first_empty = encoder.solver.eq(first_len, zero);
        let second_empty = encoder.solver.eq(second_len, zero);
        let different_arrays = encoder.solver.neq(first_array, second_array);
        let different_offsets = encoder.solver.neq(first_offset, second_offset);
        encoder.assert_term(equality);
        encoder.assert_term(first_empty);
        encoder.assert_term(second_empty);
        encoder.assert_term(different_arrays);
        encoder.assert_term(different_offsets);

        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Sat),
            "empty Seq equality must leave unobservable storage unconstrained, got {result:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn auflia_ground_seq_projectors_are_finite_and_congruent() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        encoder.force_uninterpreted_seq_sort_for_mixed_datatype();
        encoder.ensure_seq_functions();

        let seq_sort = encoder.get_seq_sort();
        let first = encoder
            .solver
            .declare_const("aufliaseq_first", seq_sort.clone());
        let second = encoder.solver.declare_const("aufliaseq_second", seq_sort);
        let first_len = encoder.seq_len_term(first).unwrap();
        let second_len = encoder.seq_len_term(second).unwrap();
        let first_offset = encoder.seq_offset_term(first).unwrap();
        let second_offset = encoder.seq_offset_term(second).unwrap();
        let first_array = encoder.seq_array_term(first).unwrap();
        let second_array = encoder.seq_array_term(second).unwrap();

        assert!(encoder.use_seq_len_proxies());
        for proxy in [first_len, second_len, first_offset, second_offset] {
            assert!(
                matches!(encoder.solver.term_kind(proxy), TermKind::Var { .. }),
                "expected a finite ground Int proxy, got {}",
                encoder.solver.format_term(proxy)
            );
        }
        for proxy in [first_array, second_array] {
            assert!(
                matches!(encoder.solver.term_kind(proxy), TermKind::Var { .. }),
                "expected a finite ground Array proxy, got {}",
                encoder.solver.format_term(proxy)
            );
        }
        assert!(encoder.solver.assertions().iter().all(|term| {
            !term_contains_app(&encoder, *term, "seq_len")
                && !term_contains_app(&encoder, *term, "seq_offset")
                && !term_contains_app(&encoder, *term, "seq_array")
                && !term_contains_native_seq_equality(&encoder, *term)
        }));

        let same_receiver = encoder.seq_aware_equality_term(first, second);
        let different_lengths = encoder.solver.neq(first_len, second_len);
        encoder.assert_term(same_receiver);
        encoder.assert_term(different_lengths);
        assert!(encoder
            .solver
            .assertions()
            .iter()
            .all(|term| !term_contains_native_seq_equality(&encoder, *term)));
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "AUFLIA finite Seq equality must be extensional; got {result:?}"
        );
    }

    #[test]
    fn finite_proxy_component_closure_materializes_authenticated_seq_alias() {
        let mut encoder = AYEncoder::new_all();
        encoder.ensure_seq_functions();
        let seq_sort = encoder.get_seq_sort();
        let first = encoder
            .solver
            .declare_const("component_alias_first", seq_sort.clone());
        let second = encoder
            .solver
            .declare_const("component_alias_second", seq_sort);

        let authenticated = encoder.seq_aware_equality_term(first, second);
        encoder.assert_term(authenticated);
        assert!(!assertions_contain_direct_equality(&encoder, first, second));

        encoder.assert_seq_component_aliases_from_assertions();
        assert!(
            assertions_contain_direct_equality(&encoder, first, second),
            "an asserted finite semantic equality should materialize one bounded carrier alias"
        );
    }

    #[test]
    fn finite_proxy_component_closure_rejects_negated_semantic_equality() {
        let mut encoder = AYEncoder::new_all();
        encoder.ensure_seq_functions();
        let seq_sort = encoder.get_seq_sort();
        let first = encoder
            .solver
            .declare_const("negated_alias_first", seq_sort.clone());
        let second = encoder
            .solver
            .declare_const("negated_alias_second", seq_sort);

        let equality = encoder.seq_aware_equality_term(first, second);
        let negated = encoder.solver.not(equality);
        encoder.assert_term(negated);
        encoder.assert_seq_component_aliases_from_assertions();
        assert!(
            !assertions_contain_direct_equality(&encoder, first, second),
            "a negated semantic equality must never authenticate a carrier alias"
        );
    }

    #[test]
    fn finite_proxy_component_closure_rejects_partial_or_stale_aliases() {
        let mut encoder = AYEncoder::new_all();
        encoder.ensure_seq_functions();
        let seq_sort = encoder.get_seq_sort();
        let first = encoder
            .solver
            .declare_const("partial_alias_first", seq_sort.clone());
        let stale_sort = seq_sort.clone();
        let second = encoder
            .solver
            .declare_const("partial_alias_second", seq_sort);
        let stale = encoder
            .solver
            .declare_const("partial_alias_stale", stale_sort);
        let first_array = encoder.seq_array_term(first).unwrap();
        let second_array = encoder.seq_array_term(second).unwrap();
        let first_len = encoder.seq_len_term(first).unwrap();
        let second_len = encoder.seq_len_term(second).unwrap();
        let first_offset = encoder.seq_offset_term(first).unwrap();
        let _second_offset = encoder.seq_offset_term(second).unwrap();
        let stale_offset = encoder.seq_offset_term(stale).unwrap();
        let same_array = encoder.eq_term(first_array, second_array);
        let same_len = encoder.eq_term(first_len, second_len);
        let unrelated_offset = encoder.eq_term(first_offset, stale_offset);
        encoder.assert_term(same_array);
        encoder.assert_term(same_len);
        encoder.assert_term(unrelated_offset);

        encoder.assert_seq_component_aliases_from_assertions();
        assert!(
            !assertions_contain_direct_equality(&encoder, first, second),
            "a stale or partial component match must not authenticate the Seq carrier"
        );
    }

    #[test]
    fn first_branch_local_seq_value_does_not_escape_its_guard() {
        let mut encoder = AYEncoder::new_all();
        let seq_sort = encoder.get_seq_sort();
        let carrier = encoder
            .solver
            .declare_const("branch_local_seq_carrier", seq_sort);
        let condition = encoder
            .solver
            .declare_const("branch_local_seq_condition", Sort::Bool);
        let not_condition = encoder.solver.not(condition);
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let then_array = encoder
            .solver
            .fresh_var("branch_local_then_array", array_sort.clone());
        let else_array = encoder
            .solver
            .fresh_var("branch_local_else_array", array_sort);
        let zero = encoder.solver.int_const(0);
        let one = encoder.solver.int_const(1);

        {
            let _guard = encoder.push_path_condition(condition);
            encoder.insert_seq_value(
                carrier,
                SeqValue {
                    arr: then_array,
                    len: zero,
                    offset: zero,
                    known_len: Some(0),
                },
            );
        }
        let anchor = encoder
            .get_seq_value_cloned(carrier)
            .expect("branch-local SeqValue anchor");
        assert_ne!(anchor.len, zero, "branch value escaped as global anchor");
        assert_eq!(
            anchor.known_len, None,
            "branch-local length escaped globally"
        );

        // Outside the first arm, its length must remain unconstrained. The old
        // implementation made this probe false by storing literal zero as the
        // global carrier length.
        encoder.push_scope().expect("push outside-branch probe");
        encoder.assert_term(not_condition);
        let anchor_nonzero = encoder.solver.neq(anchor.len, zero);
        encoder.assert_term(anchor_nonzero);
        assert_eq!(encoder.check_sat(), SolveResult::Sat);
        encoder.pop_scope().expect("pop outside-branch probe");

        {
            let _guard = encoder.push_path_condition(not_condition);
            encoder.insert_seq_value(
                carrier,
                SeqValue {
                    arr: else_array,
                    len: one,
                    offset: zero,
                    known_len: Some(1),
                },
            );
        }

        for (path, wrong_len) in [(condition, one), (not_condition, zero)] {
            encoder.push_scope().expect("push guarded refinement probe");
            encoder.assert_term(path);
            let wrong = encoder.solver.eq(anchor.len, wrong_len);
            encoder.assert_term(wrong);
            assert!(matches!(encoder.check_sat(), SolveResult::Unsat(_)));
            encoder.pop_scope().expect("pop guarded refinement probe");
        }
    }

    #[test]
    fn finite_seq_projectors_are_stable_and_leave_unobserved_apps_untouched() {
        let mut encoder = AYEncoder::new_all();
        encoder.ensure_seq_functions();
        let seq_sort = encoder.get_seq_sort();
        let observed = encoder
            .solver
            .declare_const("observed_projector_seq", seq_sort.clone());
        let unobserved = encoder
            .solver
            .declare_const("unobserved_projector_seq", seq_sort);

        let len = encoder.seq_len_term(observed).unwrap();
        let offset = encoder.seq_offset_term(observed).unwrap();
        let array = encoder.seq_array_term(observed).unwrap();
        assert_eq!(encoder.seq_len_term(observed).unwrap(), len);
        assert_eq!(encoder.seq_offset_term(observed).unwrap(), offset);
        assert_eq!(encoder.seq_array_term(observed).unwrap(), array);
        assert!(encoder
            .seq_state_for_test()
            .get_seq_len_aux(&unobserved)
            .is_none());
        assert!(encoder
            .seq_state_for_test()
            .get_seq_offset_aux(&unobserved)
            .is_none());
        assert!(encoder
            .seq_state_for_test()
            .get_seq_array_aux(&unobserved)
            .is_none());
    }

    #[test]
    #[timeout(30000)]
    fn finite_seq_projectors_remain_stable_after_concrete_refinement() {
        let mut encoder = AYEncoder::new_all();
        encoder.ensure_seq_functions();
        let seq_sort = encoder.get_seq_sort();
        let observed = encoder
            .solver
            .declare_const("refined_projector_seq", seq_sort);

        let proxy_len = encoder.seq_len_term(observed).unwrap();
        let proxy_offset = encoder.seq_offset_term(observed).unwrap();
        let proxy_array = encoder.seq_array_term(observed).unwrap();
        let zero = encoder.solver.int_const(0);
        let concrete_array = encoder.solver.const_array(Sort::Int, zero);

        encoder.insert_seq_value(
            observed,
            crate::encoder::SeqValue {
                arr: concrete_array,
                len: zero,
                offset: zero,
                known_len: Some(0),
            },
        );

        assert_eq!(encoder.seq_len_term(observed).unwrap(), proxy_len);
        assert_eq!(encoder.seq_offset_term(observed).unwrap(), proxy_offset);
        assert_eq!(encoder.seq_array_term(observed).unwrap(), proxy_array);

        for (component, disequality) in [
            ("length", encoder.solver.neq(proxy_len, zero)),
            ("offset", encoder.solver.neq(proxy_offset, zero)),
            ("array", encoder.solver.neq(proxy_array, concrete_array)),
        ] {
            encoder.push_scope().expect("push component probe");
            encoder.assert_term(disequality);
            let result = encoder.check_sat();
            encoder.pop_scope().expect("pop component probe");
            assert!(
                matches!(result, SolveResult::Unsat(_)),
                "refining a ground Seq must define its original {component} proxy; got {result:?}"
            );
        }
    }

    #[test]
    fn finite_seq_projector_assertion_order_is_deterministic() {
        let expected = finite_seq_projector_assertion_trace();
        for _ in 0..16 {
            assert_eq!(finite_seq_projector_assertion_trace(), expected);
        }
    }

    #[test]
    #[timeout(30000)]
    fn all_logic_seq_len_inside_quantifier_uses_parameter_dependent_projector() {
        let mut encoder = AYEncoder::new_all();
        encoder.ensure_seq_functions();

        let seq_sort = encoder.get_seq_sort();
        let s = encoder
            .solver
            .declare_const("all_logic_quantified_seq", seq_sort);

        encoder.quantifier_state.inc_quantifier_depth();
        let (len, source) = encoder
            .seq_len_term_with_source(s)
            .expect("quantified All-logic seq len should use the seq_len projector");
        encoder.quantifier_state.dec_quantifier_depth();

        let seq_funcs = encoder.seq_funcs();
        let seq_len_app = encoder.solver.apply(&seq_funcs.seq_len, &[s]);
        assert!(encoder.use_seq_len_proxies());
        assert_eq!(source, crate::encoder::seq::SeqLenSource::AuxLenFallback);
        assert_eq!(
            len, seq_len_app,
            "quantifier bodies must keep len(receiver) dependent on the receiver term"
        );
        assert!(
            encoder.seq_state_for_test().get_seq_len_aux(&s).is_none(),
            "quantified fallback must not cache a ground-level proxy for the receiver"
        );
        assert!(
            !format!("{len:?}").contains("seq_len_proxy"),
            "quantified fallback must not introduce a free seq_len_proxy term"
        );
    }

    #[test]
    #[timeout(30000)]
    fn all_logic_seq_len_inside_quantifier_keeps_receiver_dependent_projector() {
        let mut encoder = AYEncoder::new_all();
        encoder.ensure_seq_functions();

        let seq_sort = encoder.get_seq_sort();
        let s = encoder.solver.fresh_var("quantified_seq", seq_sort);

        encoder.quantifier_state.inc_quantifier_depth();
        let (len, source) = encoder
            .seq_len_term_with_source(s)
            .expect("quantified All-logic seq len should use the projector");
        encoder.quantifier_state.dec_quantifier_depth();

        assert!(encoder.use_seq_len_proxies());
        assert_eq!(source, crate::encoder::seq::SeqLenSource::AuxLenFallback);
        let rendered = encoder.solver.format_term(len);
        assert!(
            rendered.contains("seq_len"),
            "quantified seq len must remain receiver-dependent, got {rendered}"
        );
        assert!(
            !rendered.contains("seq_len_proxy"),
            "quantified seq len must not capture a fresh proxy constant, got {rendered}"
        );
        assert!(
            encoder.seq_state_for_test().get_seq_len_aux(&s).is_none(),
            "quantified seq len should not cache a ground proxy for the receiver"
        );
        assert!(
            !encoder.seq_state_for_test().has_seq_value(&s),
            "quantified seq len should not materialize a global SeqValue side table entry"
        );
    }

    /// Sort mismatch in Seq carrier is repaired via `PhantomVariableUpgrade`
    /// (#2567), so flat push_back chain reconstruction succeeds after repair.
    #[test]
    #[timeout(30000)]
    fn flat_push_back_chain_reconstruction_repairs_sort_mismatch_via_phantom_upgrade() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        encoder
            .get_or_declare_var("final_x_view", Sort::Int)
            .expect("declare final_x_view as Int");

        let requires = vec![
            eq(method_call(view(var("x")), "len", vec![]), int(0)),
            eq(
                view(PureExpr::Final(Arc::new(var("x")))),
                method_call(view(var("x")), "push_back", vec![int(1)]),
            ),
            eq(
                view(PureExpr::Final(Arc::new(var("x")))),
                method_call(view(var("x")), "push_back", vec![int(2)]),
            ),
        ];
        let result = encoder.try_reconstruct_flat_push_back_chain(&requires, None);
        assert!(
            result.is_ok(),
            "flat push_back chain reconstruction repairs sort mismatch via PhantomVariableUpgrade"
        );
    }

    #[test]
    #[timeout(30000)]
    fn index_mut_synthesis_propagates_shape_constraint_errors() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();

        let seq_sort = encoder.get_seq_sort();
        let source_term = encoder
            .get_or_declare_var("a_view", seq_sort)
            .expect("declare a_view as Seq");
        encoder
            .get_or_declare_var("final_a_view", Sort::Int)
            .expect("declare final_a_view as Int");

        let seq_empty = encoder
            .seq_state
            .funcs()
            .expect("seq funcs initialized")
            .seq_empty;
        let source_value = encoder
            .seq_state
            .get_seq_value_cloned(&seq_empty)
            .expect("seq_empty SeqValue registered");
        encoder
            .seq_state
            .insert_seq_value(source_term, source_value);

        let assumption = eq(
            method_call(
                view(PureExpr::Final(Arc::new(var("a")))),
                "index_logic",
                vec![int(0)],
            ),
            int(1),
        );
        let result = encoder.try_synthesize_index_mut_seq_value(&assumption, None);
        assert!(
            result.is_err(),
            "index_mut synthesis must propagate shape-constraint sort mismatches"
        );
    }

    #[test]
    #[timeout(30000)]
    fn encode_seq_push_back_propagates_receiver_sort_errors() {
        let mut encoder = AYEncoder::new();
        let bad_receiver = encoder
            .get_or_declare_var("not_seq", Sort::Int)
            .expect("declare Int receiver");
        let value = encoder.solver.int_const(7);

        let result = encoder.encode_seq_push_back(bad_receiver, value);
        assert!(
            result.is_err(),
            "encode_seq_push_back must return errors instead of silently dropping them"
        );
    }

    /// Phase 5 (#2124): verify the intermediate state expression produced by
    /// the MIR extraction's `deref_exprs` update. After `a[i] = x`, the
    /// extraction stores `View(Deref(Var("a"))).set(i, x)` in deref_exprs.
    /// Subsequent reads at the same index should return `x`.
    ///
    /// Uses concrete indices to avoid quantifier-dependent encoding paths.
    #[test]
    #[timeout(30000)]
    fn intermediate_state_set_then_read_same_index_verifies() {
        // Model: View(Deref(Var("a"))).set(0, 42)
        // This is the expression shape stored in deref_exprs after `a[0] = 42`.
        let intermediate = method_call(view(deref(var("a"))), "set", vec![int(0), int(42)]);
        // Read back at the same index via the Seq's index_logic.
        // In the actual pipeline, the subsequent `a[0]` read produces:
        //   View(intermediate).index_logic(0)  — but since `intermediate`
        // is already a Seq-level expression (result of .set()), the read is:
        //   intermediate.index_logic(0)
        let read_back = method_call(intermediate, "index_logic", vec![int(0)]);
        // The postcondition: set(s, 0, 42).index_logic(0) == 42
        let formula = eq(read_back, int(42));

        let mut encoder = AYEncoder::new();
        // The Seq sort hints must cover a_current and a_current_view so the
        // encoder maps View(Deref(Var("a"))) to a Seq variable.
        encoder.record_sort_hint(
            "a_current".to_string(),
            trust_wp_core::formula::ExprSort::Seq,
        );
        encoder.record_sort_hint(
            "a_current_view".to_string(),
            trust_wp_core::formula::ExprSort::Seq,
        );
        encoder.register_sort_hints(std::slice::from_ref(&formula));
        let formula_term = encoder.encode_pure(&formula).expect("encode_pure");
        let negated = encoder.solver.not(formula_term);
        encoder.assert_term(negated);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "set(View(Deref(a)), 0, 42).index_logic(0) should equal 42 (#2124 Phase 5), got {result:?}"
        );
    }

    /// #2242 fix validation: fresh constants with known_len trigger pointwise
    /// select decomposition, making negated seq literal postconditions SAT.
    #[test]
    #[timeout(30000)]
    fn diag_2242_fresh_constants_pointwise_decomp() {
        let mut encoder = AYEncoder::new();
        encoder.ensure_seq_functions();
        let seq_sort = encoder.get_seq_sort();

        let a_view = encoder
            .get_or_declare_var("a_view", seq_sort.clone())
            .expect("a_view");
        let a_fv = encoder
            .get_or_declare_var("a_final_view", seq_sort.clone())
            .expect("a_fv");

        // Build seq(0,0,0,0) as fresh constant with known_len
        let zero = encoder.solver.int_const(0);
        let base_arr = encoder.solver.const_array(Sort::Int, zero);
        let idx0 = encoder.solver.int_const(0);
        let idx1 = encoder.solver.int_const(1);
        let idx2 = encoder.solver.int_const(2);
        let idx3 = encoder.solver.int_const(3);
        let arr_0000 = encoder.solver.store(base_arr, idx0, zero);
        let arr_0000 = encoder.solver.store(arr_0000, idx1, zero);
        let arr_0000 = encoder.solver.store(arr_0000, idx2, zero);
        let arr_0000 = encoder.solver.store(arr_0000, idx3, zero);
        let len_4 = encoder.solver.int_const(4);
        let pre_const = encoder
            .solver
            .declare_const("__seq_lit_pre", seq_sort.clone());
        encoder.seq_state.insert_seq_value(
            pre_const,
            crate::encoder::SeqValue {
                arr: arr_0000,
                len: len_4,
                offset: zero,
                known_len: Some(4),
            },
        );

        // Decompose precondition: a_view == pre_const (pointwise)
        let pre_eq = encoder
            .try_decompose_seq_equality(a_view, pre_const)
            .expect("decompose pre")
            .expect("should decompose pre");
        encoder.assert_term(pre_eq);

        // Build seq(0,1,1,0) as fresh constant with known_len
        let one = encoder.solver.int_const(1);
        let arr_0110 = encoder.solver.store(base_arr, idx0, zero);
        let arr_0110 = encoder.solver.store(arr_0110, idx1, one);
        let arr_0110 = encoder.solver.store(arr_0110, idx2, one);
        let arr_0110 = encoder.solver.store(arr_0110, idx3, zero);
        let post_const = encoder.solver.declare_const("__seq_lit_post", seq_sort);
        encoder.seq_state.insert_seq_value(
            post_const,
            crate::encoder::SeqValue {
                arr: arr_0110,
                len: len_4,
                offset: zero,
                known_len: Some(4),
            },
        );

        // Decompose postcondition (pointwise), then negate
        let post_eq = encoder
            .try_decompose_seq_equality(a_fv, post_const)
            .expect("decompose post")
            .expect("should decompose post");
        let negated = encoder.solver.not(post_eq);
        encoder.assert_term(negated);
        encoder.set_timeout(Some(std::time::Duration::from_secs(2)));

        let result = encoder.check_sat();
        assert!(
            !matches!(result, SolveResult::Unsat(_)),
            "#2242: pointwise decomposed negation must be SAT: {result:?}"
        );
    }
}
