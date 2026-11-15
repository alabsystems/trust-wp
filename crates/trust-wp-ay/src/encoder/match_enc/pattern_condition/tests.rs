// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, SolveResult, Sort};
use ntest::timeout;
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_field_logic_fn_name, ExprSort, Pattern,
};

use super::*;
use crate::{
    encoder::{
        match_enc::SwitchTarget,
        unsoundness::{self, UnsoundnessCategory},
    },
    tests::helpers::bool_expr,
};

fn shape_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "Shape".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Circle".to_string(),
                fields: vec![DatatypeField {
                    name: "shape_circle_0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Square".to_string(),
                fields: vec![DatatypeField {
                    name: "shape_square_0".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    }
}

fn pair_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "Pair".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Both".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "pair_both_fst".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "pair_both_snd".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            DatatypeConstructor {
                name: "Empty".to_string(),
                fields: vec![],
            },
        ],
    }
}

fn pair_with_bool_head_datatype() -> DatatypeSort {
    let mut datatype = pair_datatype();
    datatype.constructors[0].fields[0].sort = Sort::Bool;
    datatype
}

#[test]
fn int_tuple_getter_range_collisions_are_signature_isolated() {
    fn assert_order(first: Sort, second: Sort) {
        let mut encoder = AYEncoder::new();
        let name = tuple_field_logic_fn_name(0);

        let first_decl = encoder.get_or_declare_tuple_getter(&name, &Sort::Int, &first);
        let second_decl = encoder.get_or_declare_tuple_getter(&name, &Sort::Int, &second);

        assert_eq!(first_decl.domain(), &[Sort::Int]);
        assert_eq!(first_decl.range(), &first);
        assert_eq!(second_decl.domain(), &[Sort::Int]);
        assert_eq!(second_decl.range(), &second);
        assert_ne!(
            first_decl.name(),
            second_decl.name(),
            "different tuple element sorts must not share a native declaration identity"
        );

        let first_again = encoder.get_or_declare_tuple_getter(&name, &Sort::Int, &first);
        let second_again = encoder.get_or_declare_tuple_getter(&name, &Sort::Int, &second);
        assert_eq!(first_again.name(), first_decl.name());
        assert_eq!(second_again.name(), second_decl.name());
    }

    assert_order(Sort::Int, Sort::Bool);
    assert_order(Sort::Bool, Sort::Int);
}

fn list_datatype_with_structural_fields() -> DatatypeSort {
    DatatypeSort {
        name: "List".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "list_cons_0".to_string(),
                        sort: Sort::Uninterpreted("Tuple2".to_string()),
                    },
                    DatatypeField {
                        name: "list_cons_1".to_string(),
                        sort: Sort::Uninterpreted("List".to_string()),
                    },
                ],
            },
            DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
        ],
    }
}

fn hashmap_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "MyHashMap".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "MyHashMap".to_string(),
            fields: vec![],
        }],
    }
}

fn stale_inferred_list_datatype() -> DatatypeSort {
    DatatypeSort {
        name: "List".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "list_cons_0".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "list_cons_1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
        ],
    }
}

fn tuple2_sort() -> Sort {
    Sort::Uninterpreted("Tuple2".to_string())
}

fn seq_sort() -> Sort {
    Sort::Uninterpreted("Seq".to_string())
}

fn none_pattern() -> Pattern {
    Pattern::Constructor {
        name: "None".to_string(),
        inner: None,
    }
}

fn some_binding_pattern(name: &str) -> Pattern {
    Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(Pattern::Binding(name.to_string()))),
    }
}

/// Does a tuple-field getter with this `(domain) -> range` signature exist?
///
/// Both sides are compared in TERM-SORT form via `Sort::as_term_sort()` (which
/// lowers `Datatype(d)` to `Uninterpreted(d.name)` — the spelling the term
/// store actually uses). The encoder is free to declare a getter's range either
/// way for the same sort, and it does: the `OptionSeq` getter is declared with
/// the uninterpreted spelling while the `OptionInt` getter is declared as
/// `Datatype(OptionInt)`. Comparing the declared side raw would make this
/// predicate answer `false` for a declaration that is present and correct (see
/// `tuple_none_field_still_uses_option_int_without_non_int_evidence`).
/// Normalising the declared side is exactly ay's own sort identity, so this
/// neither accepts a getter of a different sort nor loosens the name match.
fn tuple_getter_decl_exists(
    encoder: &AYEncoder,
    index: usize,
    domain: &Sort,
    range: &Sort,
) -> bool {
    let getter_name = tuple_field_logic_fn_name(index);
    let smt_name = trust_wp_core::logic::logic_fn_smt_name(&getter_name);
    let domain = domain.as_term_sort();
    let range = range.as_term_sort();
    encoder.logic_funcs_iter().any(|(decl_name, decl)| {
        (decl_name == &smt_name
            || decl_name
                .strip_prefix(&smt_name)
                .is_some_and(|suffix| suffix.starts_with("__placeholder_")))
            && decl
                .domain()
                .iter()
                .map(Sort::as_term_sort)
                .eq(std::iter::once(domain.clone()))
            && decl.range().as_term_sort() == range
    })
}

fn option_payload_sort(datatype: &DatatypeSort) -> Sort {
    datatype
        .constructors
        .iter()
        .find_map(|ctor| ctor.fields.first())
        .expect("Option datatype should have a Some payload")
        .sort
        .clone()
}

fn seed_option_seq_tuple_getter_from_some_binding(
    encoder: &mut AYEncoder,
    scrutinee: ay_dpll::api::Term,
    tuple_sort: &Sort,
) -> DatatypeSort {
    encoder.ensure_datatype_declared(&SwitchTarget::OptionInt.datatype());
    let option_seq = encoder.stdlib_option_datatype_for_payload_sort(seq_sort());
    encoder.ensure_datatype_declared(&option_seq);
    encoder.record_sort_hint("s2".to_string(), ExprSort::Seq);

    let some_arm_pattern = Pattern::Tuple(vec![
        Pattern::Binding("s1".to_string()),
        some_binding_pattern("s2"),
    ]);
    encoder
        .pattern_bindings(scrutinee, &some_arm_pattern, None, Some(tuple_sort), None)
        .expect("sibling Some binding should seed the tuple getter sort");

    assert!(
        tuple_getter_decl_exists(encoder, 1, tuple_sort, &Sort::Datatype(option_seq.clone())),
        "Some(s2) with a Seq binding should establish an OptionSeq tuple getter"
    );

    option_seq
}

#[test]
#[timeout(30000)]
fn pattern_condition_accessor_uses_actual_scrutinee_sort_when_hint_is_stale() {
    let mut encoder = AYEncoder::new();
    let list = list_datatype_with_structural_fields();
    let hashmap = hashmap_datatype();
    encoder.ensure_datatype_declared(&list);
    encoder.ensure_datatype_declared(&hashmap);

    let scrutinee = encoder
        .solver
        .declare_const("self_current", Sort::Datatype(hashmap));
    let pattern = Pattern::Constructor {
        name: "List::Cons".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![
            Pattern::Wildcard,
            Pattern::Wildcard,
        ]))),
    };

    let result = encoder.encode_pattern_condition_with_sort(
        scrutinee,
        &pattern,
        Some(&list),
        Some(&Sort::Datatype(list.clone())),
        None,
    );

    assert!(
        result.is_ok(),
        "stale List sort hint must not declare a pattern accessor applied to a MyHashMap scrutinee: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn tuple_none_field_uses_option_seq_getter_from_sibling_some_binding() {
    let mut encoder = AYEncoder::new();
    let tuple_sort = tuple2_sort();
    let scrutinee = encoder.solver.declare_const("pair", tuple_sort.clone());
    let option_seq =
        seed_option_seq_tuple_getter_from_some_binding(&mut encoder, scrutinee, &tuple_sort);

    let none_arm_pattern = Pattern::Tuple(vec![Pattern::Binding("s".to_string()), none_pattern()]);
    let cond = encoder
        .encode_pattern_condition_with_sort(
            scrutinee,
            &none_arm_pattern,
            None,
            Some(&tuple_sort),
            None,
        )
        .expect("None tuple arm should encode with sibling OptionSeq evidence");

    assert!(
        tuple_getter_decl_exists(
            &encoder,
            1,
            &tuple_sort,
            &Sort::Datatype(option_seq.clone())
        ),
        "None arm should reuse the OptionSeq tuple getter"
    );
    assert!(
        !tuple_getter_decl_exists(
            &encoder,
            1,
            &tuple_sort,
            &Sort::Datatype(SwitchTarget::OptionInt.datatype())
        ),
        "bare None must not introduce a default OptionInt getter when OptionSeq evidence exists"
    );

    let getter = encoder.get_or_declare_tuple_getter(
        &tuple_field_logic_fn_name(1),
        &tuple_sort,
        &Sort::Datatype(option_seq.clone()),
    );
    let field = encoder
        .safe_apply("test_option_seq_tuple_getter", &getter, &[scrutinee])
        .expect("OptionSeq tuple getter should apply");
    let seq_value = encoder
        .solver
        .declare_const("seq_value", option_payload_sort(&option_seq));
    let some_seq = encoder
        .safe_datatype_constructor("test option seq some", &option_seq, "Some", &[seq_value])
        .expect("OptionSeq::Some should encode");
    let field_is_some = encoder.eq_term(field, some_seq);
    encoder.assert_term(field_is_some);
    encoder.assert_term(cond);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "a tuple whose OptionSeq field is Some must not satisfy the None arm"
    );
}

#[test]
#[timeout(30000)]
fn tuple_none_field_still_uses_option_int_without_non_int_evidence() {
    let mut encoder = AYEncoder::new();
    let tuple_sort = tuple2_sort();
    let scrutinee = encoder.solver.declare_const("int_pair", tuple_sort.clone());
    let option_int = SwitchTarget::OptionInt.datatype();

    let pattern = Pattern::Tuple(vec![Pattern::Binding("i".to_string()), none_pattern()]);
    let cond = encoder
        .encode_pattern_condition_with_sort(scrutinee, &pattern, None, Some(&tuple_sort), None)
        .expect("Option<Int> None tuple arm should encode");

    assert!(
        tuple_getter_decl_exists(
            &encoder,
            1,
            &tuple_sort,
            &Sort::Datatype(option_int.clone())
        ),
        "without stronger context, bare None should keep the historical OptionInt getter"
    );

    let getter = encoder.get_or_declare_tuple_getter(
        &tuple_field_logic_fn_name(1),
        &tuple_sort,
        &Sort::Datatype(option_int.clone()),
    );
    let field = encoder
        .safe_apply("test_option_int_tuple_getter", &getter, &[scrutinee])
        .expect("OptionInt tuple getter should apply");
    let seven = encoder.solver.int_const(7);
    let some_int = encoder
        .safe_datatype_constructor("test option int some", &option_int, "Some", &[seven])
        .expect("OptionInt::Some should encode");
    let field_is_some = encoder.eq_term(field, some_int);
    encoder.assert_term(field_is_some);
    encoder.assert_term(cond);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "a tuple whose OptionInt field is Some must not satisfy the None arm"
    );
}

#[test]
#[timeout(30000)]
fn unrelated_option_int_tuple_getter_cannot_make_option_seq_none_arm_match() {
    let mut encoder = AYEncoder::new();
    let tuple_sort = tuple2_sort();
    let scrutinee = encoder.solver.declare_const("seq_pair", tuple_sort.clone());
    let option_int = SwitchTarget::OptionInt.datatype();
    encoder.ensure_datatype_declared(&option_int);

    let option_int_getter = encoder.get_or_declare_tuple_getter(
        &tuple_field_logic_fn_name(1),
        &tuple_sort,
        &Sort::Datatype(option_int.clone()),
    );
    let option_int_field = encoder
        .safe_apply(
            "test_unrelated_option_int_getter",
            &option_int_getter,
            &[scrutinee],
        )
        .expect("unrelated OptionInt tuple getter should apply");
    let none_int = encoder
        .safe_datatype_constructor("test option int none", &option_int, "None", &[])
        .expect("OptionInt::None should encode");
    let int_field_is_none = encoder.eq_term(option_int_field, none_int);
    encoder.assert_term(int_field_is_none);

    let option_seq =
        seed_option_seq_tuple_getter_from_some_binding(&mut encoder, scrutinee, &tuple_sort);
    let none_arm_pattern = Pattern::Tuple(vec![Pattern::Wildcard, none_pattern()]);
    let cond = encoder
        .encode_pattern_condition_with_sort(
            scrutinee,
            &none_arm_pattern,
            None,
            Some(&tuple_sort),
            None,
        )
        .expect("None tuple arm should prefer OptionSeq evidence over unrelated OptionInt");

    let option_seq_getter = encoder.get_or_declare_tuple_getter(
        &tuple_field_logic_fn_name(1),
        &tuple_sort,
        &Sort::Datatype(option_seq.clone()),
    );
    let option_seq_field = encoder
        .safe_apply(
            "test_related_option_seq_getter",
            &option_seq_getter,
            &[scrutinee],
        )
        .expect("OptionSeq tuple getter should apply");
    let seq_value = encoder
        .solver
        .declare_const("other_seq_value", option_payload_sort(&option_seq));
    let some_seq = encoder
        .safe_datatype_constructor("test option seq some", &option_seq, "Some", &[seq_value])
        .expect("OptionSeq::Some should encode");
    let seq_field_is_some = encoder.eq_term(option_seq_field, some_seq);
    encoder.assert_term(seq_field_is_some);
    encoder.assert_term(cond);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "the None arm must inspect the OptionSeq getter, not an unrelated OptionInt getter"
    );
}

#[test]
#[timeout(30000)]
fn multi_field_bindings_use_scrutinee_datatype_field_sorts_over_stale_inference() {
    let mut encoder = AYEncoder::new();
    let actual = list_datatype_with_structural_fields();
    let stale = stale_inferred_list_datatype();
    encoder.ensure_datatype_declared(&actual);

    let scrutinee = encoder
        .solver
        .declare_const("l", Sort::Datatype(actual.clone()));
    let pattern = Pattern::Constructor {
        name: "List::Cons".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![
            Pattern::Binding("head".to_string()),
            Pattern::Binding("tail".to_string()),
        ]))),
    };

    let bindings = encoder
        .pattern_bindings(
            scrutinee,
            &pattern,
            Some(&stale),
            Some(&Sort::Datatype(stale.clone())),
            None,
        )
        .expect("selector binding should use actual scrutinee datatype sorts");

    assert_eq!(bindings.len(), 2);
    assert_eq!(bindings[0].0, "head");
    assert_eq!(bindings[0].2, Sort::Uninterpreted("Tuple2".to_string()));
    assert_eq!(bindings[1].0, "tail");
    assert_eq!(bindings[1].2, Sort::Uninterpreted("List".to_string()));
}

#[test]
#[timeout(30000)]
fn test_multi_field_constructor_direct_binding_uses_first_native_selector() {
    let mut encoder = AYEncoder::new();
    let datatype = pair_datatype();
    encoder.ensure_datatype_declared(&datatype);

    let one = encoder.solver.int_const(1);
    let zero = encoder.solver.int_const(0);
    let scrutinee = encoder
        .solver
        .datatype_constructor(&datatype, "Both", &[one, zero]);
    let pattern = Pattern::Constructor {
        name: "Pair::Both".to_string(),
        inner: Some(Box::new(Pattern::Binding("a".to_string()))),
    };

    let bindings = encoder
        .pattern_bindings(
            scrutinee,
            &pattern,
            Some(&datatype),
            Some(&Sort::Datatype(datatype.clone())),
            None,
        )
        .expect("multi-field direct binding should use native selector");

    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].0, "a");
    assert_eq!(bindings[0].2, Sort::Int);

    let first_field_eq = encoder.eq_term(bindings[0].1, one);
    let not_first_field = encoder.solver.not(first_field_eq);
    encoder.solver.assert_term(not_first_field);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "direct binding for Pair::Both(a, _) must be tied to the first native selector"
    );
}

#[test]
#[timeout(30000)]
fn test_multi_field_constructor_binding_uses_declared_datatype_when_inferred_sort_drifts() {
    let mut encoder = AYEncoder::new();
    let declared_datatype = pair_with_bool_head_datatype();
    let inferred_datatype = pair_datatype();
    encoder.ensure_datatype_declared(&declared_datatype);

    let head = encoder.solver.bool_const(true);
    let tail = encoder.solver.int_const(0);
    let scrutinee = encoder
        .solver
        .datatype_constructor(&declared_datatype, "Both", &[head, tail]);
    let pattern = Pattern::Constructor {
        name: "Pair::Both".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![
            Pattern::Binding("head".to_string()),
            Pattern::Wildcard,
        ]))),
    };

    let bindings = encoder
        .pattern_bindings(
            scrutinee,
            &pattern,
            Some(&inferred_datatype),
            Some(&Sort::Datatype(declared_datatype.clone())),
            None,
        )
        .expect("multi-field binding should prefer the declared selector sort");

    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].0, "head");
    assert_eq!(bindings[0].2, Sort::Bool);

    let not_head = encoder.solver.not(bindings[0].1);
    encoder.solver.assert_term(not_head);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "binding must be tied to the declared Bool selector, not the stale inferred Int field"
    );
}

#[test]
#[timeout(30000)]
fn test_constructor_equality_without_explicit_scrutinee_sort_uses_actual_datatype_sort() {
    unsoundness::reset();
    let before = unsoundness::snapshot();

    let mut encoder = AYEncoder::new();
    let datatype = shape_datatype();
    encoder.ensure_datatype_declared(&datatype);

    let one = encoder.solver.int_const(1);
    let scrutinee = encoder
        .solver
        .datatype_constructor(&datatype, "Circle", &[one]);
    let pattern = Pattern::Constructor {
        name: "Circle".to_string(),
        inner: Some(Box::new(Pattern::Literal(bool_expr(true)))),
    };

    let condition = encoder
        .encode_pattern_condition_with_sort(scrutinee, &pattern, Some(&datatype), None, None)
        .expect("constructor equality should recover the scrutinee datatype sort");

    assert_eq!(encoder.solver.get_sort(condition), Sort::Bool);

    let negated = encoder.solver.not(condition);
    encoder.solver.assert_term(negated);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Circle(1) should satisfy Circle(true) after Bool->Int coercion without datatype demotion"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert_eq!(
        delta.get(&UnsoundnessCategory::SortFallbackToInt).copied(),
        None,
        "constructor equality should preserve the datatype family when the solver already knows the scrutinee sort: {delta:?}"
    );

    unsoundness::reset();
}

/// Regression: when a `Pattern::Binding` inside a constructor pattern shadows
/// an outer variable (parameter), payload-sort inference must NOT inherit the
/// outer variable's sort. The binding is fresh and scoped to the arm.
///
/// The shape, from `reference/creusot/tests/should_succeed/lang/or_pat.rs`:
///
/// ```text
/// #[logic]
/// #[ensures(x == (None, None) ==> result == 1i32)]
/// pub fn f(x: (Option<i32>, Option<i32>)) -> i32 {
///     match x {
///         (Some(x), None) | (None, Some(x)) => x,  // inner `x` shadows the parameter
///         _ => 1i32,
///     }
/// }
/// ```
///
/// Reading the outer parameter `x: Tuple2` from the var-sort registry in
/// `infer_pattern_payload_sort(Some(Binding("x")))` would produce
/// `Option<Tuple2>` as the tuple element sort and break the match encoding.
/// Payload-sort inference therefore consults only sort *hints* (which describe
/// expected binding payload sorts), never the var-sort registry. (#5 or_pat
/// shadowing)
#[test]
#[timeout(30000)]
fn outer_var_sort_does_not_leak_into_constructor_binding_payload_sort() {
    let mut encoder = AYEncoder::new();
    let tuple_sort = tuple2_sort();
    encoder.ensure_datatype_declared(&SwitchTarget::OptionInt.datatype());

    // Simulate the outer parameter `x: (Option<i32>, Option<i32>)` by
    // declaring a Tuple2-sorted variable named "x" before the match arm
    // bindings are encoded.
    let scrutinee = encoder.solver.declare_const("x", tuple_sort.clone());
    encoder.insert_var("x".to_string(), scrutinee);
    encoder.insert_var_sort("x".to_string(), tuple_sort.clone());

    // Arm pattern: `(Some(x), None)` — the inner `x` shadows the outer.
    let arm_pattern = Pattern::Tuple(vec![some_binding_pattern("x"), none_pattern()]);

    let bindings = encoder
        .pattern_bindings(scrutinee, &arm_pattern, None, Some(&tuple_sort), None)
        .expect("shadowing arm binding should encode without sort leak");

    // The arm binds exactly one variable, `x`, to the payload of the first
    // tuple element's `Some`. The recorded binding sort must NOT be the
    // outer Tuple2 sort — Tuple2-sorted bindings would force the tuple
    // getter into an `Option<Tuple2>` shape, breaking the encoding.
    assert_eq!(
        bindings.len(),
        1,
        "expected one binding from `(Some(x), None)`"
    );
    let (name, _term, sort) = &bindings[0];
    assert_eq!(name, "x");
    assert_ne!(
        *sort, tuple_sort,
        "binding `x` (shadowing outer Tuple2 parameter) must not inherit the outer sort"
    );

    // Critical anti-leak invariant: no tuple getter should be declared with
    // an `Option<Tuple2>` range. The bug surfaced when payload-sort inference
    // returned the outer `x: Tuple2` sort, which `infer_tuple_element_sort`
    // then wrapped into `Option<Tuple2>` — producing a getter that operated
    // on an entirely fictional element type and broke the rest of the match
    // encoding. (#5 or_pat shadowing)
    let option_tuple2 = encoder.stdlib_option_datatype_for_payload_sort(tuple_sort.clone());
    assert!(
        !tuple_getter_decl_exists(&encoder, 0, &tuple_sort, &Sort::Datatype(option_tuple2)),
        "shadowing must not establish an Option<Tuple2> tuple getter (outer-sort leak)"
    );
}

// --- #prophecy-slots (Fix B M2): carrier-tuple payload binder sorts ---

/// The M2 mechanism, pinned at its narrowest point: destructuring
/// `Some((a, b))` on an `Option<(&mut T, &mut [T])>` scrutinee must bind `a`
/// at the mutref RECORD sort (a real prophecy carrier), not at the `Int` the
/// punned `Tuple2` lowering would hand back. `b` is a `legacy` element (the
/// driver cannot resolve a slice referent) and keeps the legacy inference —
/// the lane lowers only what it can lower exactly.
#[test]
#[timeout(30000)]
fn m2_carrier_tuple_payload_binds_the_element_at_the_record_sort() {
    let mut encoder = AYEncoder::new_all();
    let carrier = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
    let tuple_name = crate::encoder::sort_context::sort_mapping::mutref_carrier_tuple_sort_name(&[
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        None,
    ])
    .expect("a tuple with a &mut element mints a carrier sort");
    let tuple_sort = Sort::Uninterpreted(tuple_name);

    let family = crate::encoder::match_enc::stdlib_option_datatype_for_payload(tuple_sort.clone());
    encoder.ensure_datatype_declared(&family);
    assert!(
        encoder.has_datatype_decl(&family.name),
        "the carrier-tuple Option family must declare cleanly"
    );

    let scrutinee = encoder
        .get_or_declare_var("o", Sort::Datatype(family.clone()))
        .expect("declare the option carrier");

    let pattern = Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![
            Pattern::Binding("a".to_string()),
            Pattern::Binding("b".to_string()),
        ]))),
    };
    let bindings = encoder
        .pattern_bindings(
            scrutinee,
            &pattern,
            Some(&family),
            Some(&Sort::Datatype(family.clone())),
            None,
        )
        .expect("carrier-tuple payload destructuring must encode");

    let sort_of = |name: &str| {
        bindings
            .iter()
            .find(|(n, _, _)| n == name)
            .map(|(_, _, s)| s.clone())
            .unwrap_or_else(|| panic!("binding {name} missing"))
    };
    assert_eq!(
        sort_of("a").as_term_sort(),
        carrier.as_term_sort(),
        "the &mut element must bind at the mutref record sort (the prophecy slot)"
    );
    assert_ne!(
        sort_of("b").as_term_sort(),
        carrier.as_term_sort(),
        "a `legacy` element must NOT be silently retargeted onto a carrier"
    );

    // The binder term is a real carrier: both definitional accessors exist.
    let a_term = bindings
        .iter()
        .find(|(n, _, _)| n == "a")
        .map(|(_, t, _)| *t)
        .expect("binding a");
    assert!(
        encoder.is_mut_ref_sorted(a_term),
        "the bound element term must BE the carrier, so `*a`/`^a` project"
    );
    assert!(
        encoder
            .mut_ref_component_projection(a_term, true)
            .expect("projection must encode")
            .is_some(),
        "`^a` must have a definitional projection on the carrier element"
    );
}

/// Over-refusal control for the same shape: a tuple with NO `&mut` element
/// keeps the legacy `Tuple2` lowering, so nothing outside the carrier class
/// changes sorts.
#[test]
#[timeout(30000)]
fn m2_plain_tuple_payload_keeps_the_legacy_lowering() {
    let mut encoder = AYEncoder::new_all();
    let carrier = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
    let tuple_sort = Sort::Uninterpreted("Tuple2".to_string());
    let family = crate::encoder::match_enc::stdlib_option_datatype_for_payload(tuple_sort);
    encoder.ensure_datatype_declared(&family);
    let scrutinee = encoder
        .get_or_declare_var("o", Sort::Datatype(family.clone()))
        .expect("declare the option carrier");

    let pattern = Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![
            Pattern::Binding("a".to_string()),
            Pattern::Binding("b".to_string()),
        ]))),
    };
    let bindings = encoder
        .pattern_bindings(
            scrutinee,
            &pattern,
            Some(&family),
            Some(&Sort::Datatype(family.clone())),
            None,
        )
        .expect("plain tuple payload destructuring must encode");
    for (name, _, sort) in &bindings {
        assert_ne!(
            sort.as_term_sort(),
            carrier.as_term_sort(),
            "plain tuple element {name} must not acquire a carrier sort"
        );
    }
}

// --- #prophecy-slots (Fix B M3): the carrier-Option payload-getter bridge ---

/// Declare the `Option<&mut i32>` carrier family and a scrutinee at it.
fn m3_carrier_option_scrutinee(encoder: &mut AYEncoder) -> (DatatypeSort, Sort, Term) {
    let carrier = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
    let family = crate::encoder::match_enc::stdlib_option_datatype_for_payload(carrier.clone());
    encoder.ensure_datatype_declared(&family);
    let scrutinee = encoder
        .get_or_declare_var("o", Sort::Datatype(family.clone()))
        .expect("declare the carrier option scrutinee");
    (family, carrier, scrutinee)
}

/// Apply the GOAL lane's spelling of the payload projection: the positional
/// getter the driver's substitution pipeline mints (`prophecy_carrier_getter_return_sort`
/// is what types it, so this is the same symbol byte for byte).
fn m3_goal_lane_payload(encoder: &mut AYEncoder, family: &DatatypeSort, scrutinee: Term) -> Term {
    let receiver_sort = Sort::Datatype(family.clone());
    let range = encoder
        .prophecy_carrier_getter_return_sort(0, std::slice::from_ref(&receiver_sort))
        .expect("the driver types tuple_get_0 at the carrier payload for this family");
    let getter_name = tuple_field_logic_fn_name(0);
    let getter = encoder.get_or_declare_tuple_getter(&getter_name, &receiver_sort, &range);
    encoder
        .safe_apply("m3_goal_lane", &getter, &[scrutinee])
        .expect("goal-lane getter application")
}

/// THE M3 PIN. The premise lane binds the `Some` payload through the native
/// datatype selector; the driver's goal lane reaches the same payload through
/// the positional getter. Before the bridge those are two unrelated symbols
/// and `^` proved on one says nothing about `^` asserted on the other. With
/// the bridge the two lanes are connected, so a final-side fact established
/// on the binder discharges the same fact stated on the goal spelling.
#[test]
#[timeout(30000)]
fn m3_carrier_option_payload_getter_bridge_connects_the_two_lanes() {
    let mut encoder = AYEncoder::new_all();
    let (family, _carrier, scrutinee) = m3_carrier_option_scrutinee(&mut encoder);

    // The `Some` arm is taken (the bridge is tester-guarded).
    let tester = encoder
        .solver
        .try_datatype_tester(
            &crate::encoder::match_enc::datatype_constructor_name(&family, "Some"),
            scrutinee,
        )
        .expect("tester");
    encoder.assert_term(tester);

    // Premise lane: the match binder, plus a final-side fact about it.
    let pattern = Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(Pattern::Binding("r".to_string()))),
    };
    let bindings = encoder
        .pattern_bindings(
            scrutinee,
            &pattern,
            Some(&family),
            Some(&Sort::Datatype(family.clone())),
            None,
        )
        .expect("carrier payload destructuring must encode");
    let r = bindings
        .iter()
        .find(|(n, _, _)| n == "r")
        .map(|(_, t, _)| *t)
        .expect("binding r");
    let premise_final = encoder
        .mut_ref_component_projection(r, true)
        .expect("projection encodes")
        .expect("the binder IS a carrier, so `^r` projects");
    let seven = encoder.solver.int_const(7);
    let premise = encoder.eq_term(premise_final, seven);
    encoder.assert_term(premise);

    // Goal lane: the same `^r`, spelled through the positional getter.
    let goal_payload = m3_goal_lane_payload(&mut encoder, &family, scrutinee);
    let goal_final = encoder
        .mut_ref_component_projection(goal_payload, true)
        .expect("projection encodes")
        .expect("the goal-lane payload is the same carrier sort");
    let goal = encoder.eq_term(goal_final, seven);
    let negated = encoder.solver.not(goal);
    encoder.assert_term(negated);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "the guarded ground bridge must connect the native selector and the \
         positional getter, so `^r` established on the binder discharges the \
         same fact on the goal spelling"
    );
}

/// GUARD PIN: the bridge is vacuous off the `Some` variant. On the `None`
/// branch it must assert nothing about the getter — an unguarded equality
/// there would be a fact about a term that denotes nothing.
#[test]
#[timeout(30000)]
fn m3_carrier_option_payload_getter_bridge_is_vacuous_on_none() {
    let mut encoder = AYEncoder::new_all();
    let (family, _carrier, scrutinee) = m3_carrier_option_scrutinee(&mut encoder);

    let none_tester = encoder
        .solver
        .try_datatype_tester(
            &crate::encoder::match_enc::datatype_constructor_name(&family, "None"),
            scrutinee,
        )
        .expect("None tester");
    encoder.assert_term(none_tester);

    let pattern = Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(Pattern::Binding("r".to_string()))),
    };
    let bindings = encoder
        .pattern_bindings(
            scrutinee,
            &pattern,
            Some(&family),
            Some(&Sort::Datatype(family.clone())),
            None,
        )
        .expect("destructuring encodes");
    let r = bindings
        .iter()
        .find(|(n, _, _)| n == "r")
        .map(|(_, t, _)| *t)
        .expect("binding r");
    let goal_payload = m3_goal_lane_payload(&mut encoder, &family, scrutinee);
    let eq = encoder.eq_term(goal_payload, r);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "on the None branch the bridge must not force the getter onto the \
         selector — the guard is the whole reason it is sound"
    );
}

/// OVER-REACH CONTROL: a legacy `OptionInt` scrutinee is NOT a prophecy
/// carrier family, so the M3 bridge must mint NOTHING for it — no guard
/// clause and, decisively, no getter DECLARATION. This is what keeps the
/// bridge inert outside the carrier family. (It deliberately does not claim
/// the two spellings are unconnected: the legacy stdlib-Option lane has its
/// own, separate connections. The claim under test is that *this* bridge is
/// inert.)
#[test]
#[timeout(30000)]
fn m3_legacy_option_int_mints_no_payload_getter_bridge() {
    let getter_key = |domain: &Sort, range: &Sort| {
        AYEncoder::placeholder_smt_name(
            &trust_wp_core::logic::logic_fn_smt_name(&tuple_field_logic_fn_name(0)),
            std::slice::from_ref(&domain.as_term_sort()),
            &range.as_term_sort(),
        )
    };

    // Positive half: the carrier family DOES get the bridge, so its getter
    // declaration exists purely as a result of `pattern_bindings`.
    let mut encoder = AYEncoder::new_all();
    let (family, carrier, scrutinee) = m3_carrier_option_scrutinee(&mut encoder);
    let pattern = Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(Pattern::Binding("r".to_string()))),
    };
    encoder
        .pattern_bindings(
            scrutinee,
            &pattern,
            Some(&family),
            Some(&Sort::Datatype(family.clone())),
            None,
        )
        .expect("destructuring encodes");
    assert!(
        encoder.has_logic_func_decl(&getter_key(&Sort::Datatype(family), &carrier)),
        "the carrier family must mint the goal-lane getter through the bridge"
    );

    // Control half: the legacy family must not enter the lane at all.
    let mut encoder = AYEncoder::new_all();
    let family = SwitchTarget::OptionInt.datatype();
    encoder.ensure_datatype_declared(&family);
    let receiver_sort = Sort::Datatype(family.clone());
    assert!(
        encoder
            .prophecy_carrier_getter_return_sort(0, std::slice::from_ref(&receiver_sort))
            .is_none(),
        "OptionInt must never enter the prophecy-carrier getter lane"
    );
    let scrutinee = encoder
        .get_or_declare_var("o", receiver_sort.clone())
        .expect("declare OptionInt scrutinee");
    encoder
        .pattern_bindings(
            scrutinee,
            &pattern,
            Some(&family),
            Some(&receiver_sort),
            None,
        )
        .expect("destructuring encodes");
    assert!(
        !encoder.has_logic_func_decl(&getter_key(&receiver_sort, &Sort::Int)),
        "no M3 bridge — and therefore no getter declaration — may be minted \
         for a legacy Option family"
    );
}

// --- #prophecy-slots (Fix B M4): `*r` on a carrier binder is the CURRENT
//     projection, end to end through the match-arm encoder ---

use ay_dpll::api::Term as M4Term;
use trust_wp_core::formula::{BinOp as M4BinOp, MatchArm as M4MatchArm, PureExpr as M4Expr};

/// Declare the `Option<&mut i32>` carrier family, a scrutinee `o` at it, take
/// the `Some` branch, and bind the payload carrier to `(current=3, final=7,
/// id=1)`. Returns the encoder ready for an arm-body encoding.
fn m4_bound_carrier_option(encoder: &mut AYEncoder) -> DatatypeSort {
    let carrier = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
    let family = crate::encoder::match_enc::stdlib_option_datatype_for_payload(carrier.clone());
    encoder.ensure_datatype_declared(&family);
    let scrutinee = encoder
        .get_or_declare_var("o", Sort::Datatype(family.clone()))
        .expect("declare the carrier option scrutinee");
    let ctor = crate::encoder::match_enc::datatype_constructor_name(&family, "Some");
    let tester = encoder
        .solver
        .try_datatype_tester(&ctor, scrutinee)
        .expect("tester");
    encoder.assert_term(tester);

    let (selector_name, payload_sort) =
        AYEncoder::constructor_payload_selector(&family, "Some").expect("single-field Some");
    let (selector_name, payload_sort) = (selector_name.to_string(), payload_sort.clone());
    let payload = encoder
        .solver
        .try_datatype_selector(&selector_name, scrutinee, payload_sort)
        .expect("payload selector");
    let three = encoder.solver.int_const(3);
    let seven = encoder.solver.int_const(7);
    let one = encoder.solver.int_const(1);
    encoder
        .bind_whole_mut_ref(&carrier, &Sort::Int, payload, three, seven, one)
        .expect("bind the payload carrier's (current, final, id)");
    family
}

/// Encode `match o { Some(r) => <body>, _ => true }`.
fn m4_arm_body(encoder: &mut AYEncoder, body: M4Expr) -> M4Term {
    use std::sync::Arc;
    let expr = M4Expr::Match {
        scrutinee: Arc::new(M4Expr::Var("o".to_string(), None)),
        arms: vec![
            M4MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("r".to_string()))),
                },
                body,
            },
            M4MatchArm {
                pattern: Pattern::Wildcard,
                body: M4Expr::Bool(true),
            },
        ],
    };
    encoder.encode_pure(&expr).expect("match must encode")
}

fn m4_deref_r_eq(n: i64) -> M4Expr {
    use std::sync::Arc;
    M4Expr::BinOp(
        Arc::new(M4Expr::Deref(Arc::new(M4Expr::Var("r".to_string(), None)))),
        M4BinOp::Eq,
        Arc::new(M4Expr::Int(n)),
    )
}

/// THE M4 VC PIN. With the payload carrier bound to `(current=3, final=7)`,
/// the arm body `*r == 3` must be PROVABLE — i.e. `*r` denotes
/// `mut_ref_current(r)`. Before M4 the arm rewriter stripped the `Deref` off
/// the (unannotated) binder, so `*r` reached the equality as the whole
/// `(current, final, id)` record and the clause carried no current-value
/// content at all.
#[test]
#[timeout(30000)]
fn m4_carrier_binder_deref_denotes_the_current_projection() {
    let mut encoder = AYEncoder::new_all();
    let _family = m4_bound_carrier_option(&mut encoder);
    let body = m4_arm_body(&mut encoder, m4_deref_r_eq(3));
    let neg = encoder.solver.not(body);
    encoder.assert_term(neg);
    let res = encoder.check_sat();
    assert!(
        matches!(res, SolveResult::Unsat(_)),
        "`*r` must be the bound CURRENT component (3), got {res:?}"
    );
}

/// THE TEETH. The same shape must NOT make `*r == 7` provable: declining the
/// strip is only correct if it hands back `mut_ref_current(r)`, never the raw
/// carrier and never the final component. Asserting the body must be UNSAT
/// (3 != 7) — if `*r` had collapsed onto the carrier or fused with `^r`, this
/// would be satisfiable.
#[test]
#[timeout(30000)]
fn m4_carrier_binder_deref_is_not_the_final_component() {
    let mut encoder = AYEncoder::new_all();
    let _family = m4_bound_carrier_option(&mut encoder);
    let body = m4_arm_body(&mut encoder, m4_deref_r_eq(7));
    encoder.assert_term(body);
    let res = encoder.check_sat();
    assert!(
        matches!(res, SolveResult::Unsat(_)),
        "`*r == 7` must be refuted — `*r` is the current, never the final, \
         got {res:?}"
    );
}

/// Consistency control for the two pins above: the SAME encoder state with
/// the SAME arm body asserted positively at the true value is SAT. Without
/// this a contradictory base would make both UNSAT results meaningless.
#[test]
#[timeout(30000)]
fn m4_carrier_binder_deref_base_is_consistent() {
    let mut encoder = AYEncoder::new_all();
    let _family = m4_bound_carrier_option(&mut encoder);
    let body = m4_arm_body(&mut encoder, m4_deref_r_eq(3));
    encoder.assert_term(body);
    let res = encoder.check_sat();
    assert!(
        matches!(res, SolveResult::Sat),
        "the carrier-binder base must stay satisfiable, got {res:?}"
    );
}
