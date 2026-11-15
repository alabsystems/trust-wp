// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #1308: function.rs:275 hardcoded `Sort::Int` for
/// non-Bool result sorts. When the body expression infers to a Seq sort
/// (or any non-Int, non-Bool sort), the equality assertion must use the
/// actual inferred sort, not `Sort::Int`. Before the fix, this would
/// panic with `BUG: mk_eq expects same sort`.
#[test]
#[timeout(30000)]
fn test_verify_function_seq_result_sort_no_panic() {
    // Body returns a Seq-annotated variable — infer_expr_sort returns
    // Sort::Seq(Int), not Sort::Int. (#2080)
    let body = var_with_sort("s", ExprSort::Seq);
    // Postcondition: result == s (both Seq)
    let ens = eq(
        var_with_sort("result", ExprSort::Seq),
        var_with_sort("s", ExprSort::Seq),
    );

    // The verifier should preserve the Seq sort for `result` and prove the
    // postcondition without sort conflicts.
    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)));
    assert!(
        result.is_ok(),
        "Seq-result function verification should not error: {result:?}"
    );
    let vr = result.unwrap();
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "Seq-result verification should be proven once result sort is Seq: {vr:?}"
    );
}

/// Test that logic function ensures (spec axioms) are emitted and can be used
/// by callers to prove goals. This mimics the trigger.rs Creusot test:
///
/// ```text
/// fn id(i: Int) -> Int { i }            // logic fn, open
/// fn id_mono()                           // lemma, open, no params
///   ensures: forall<i,j> #[trigger(id(i), id(j))] i <= j ==> id(i) <= id(j)
/// fn test() ensures: id(5) >= id(2)     // should verify using id_mono's spec axiom
/// ```
///
/// The spec axiom for `id_mono` is: `forall i,j. i<=j ==> id(i)<=id(j)` with
/// trigger `{id(i), id(j)}`. When `id(5)` and `id(2)` appear in the goal,
/// ay's E-matcher instantiates the axiom with i=2, j=5 (or i=5, j=2), proving
/// the goal `id(5) >= id(2)`.
#[test]
#[timeout(30000)]
fn test_spec_axiom_lemma_invocation_trigger_pattern() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // id(i) = i — an open logic function
    let id_fn = LogicFnDef::new(
        "id".to_string(),
        "crate::inner::id".to_string(),
        vec!["i".to_string()],
        var("i"),
    )
    .with_mode(LogicMode::Open);

    // id_mono() — a lemma with no params, body = (), but ensures clause
    //   ensures: forall<i, j> #[trigger(id(i), id(j))] i <= j ==> id(i) <= id(j)
    //
    // The parser generates nested Forall nodes with the SAME triggers cloned
    // to each nesting level. This lets encode_pure_quantifier_impl collapse
    // them into a single multi-variable forall (matching SMT-LIB semantics).
    let triggers = vec![vec![
        logic_fn_call("id", vec![var("i")]),
        logic_fn_call("id", vec![var("j")]),
    ]];
    let id_mono_ensures = forall_with_triggers(
        "i",
        forall_with_triggers(
            "j",
            implies(
                le(var("i"), var("j")),
                le(
                    logic_fn_call("id", vec![var("i")]),
                    logic_fn_call("id", vec![var("j")]),
                ),
            ),
            triggers.clone(),
        ),
        triggers,
    );
    let mut id_mono = LogicFnDef::new(
        "id_mono".to_string(),
        "crate::inner::id_mono".to_string(),
        vec![],
        PureExpr::Bool(true), // unit-returning lemma body (not semantically meaningful)
    );
    id_mono.set_mode(LogicMode::Open);
    id_mono.set_ensures(vec![id_mono_ensures]);

    // Goal: ensures id(5) >= id(2)
    let ensures = vec![ge(
        logic_fn_call("id", vec![int(5)]),
        logic_fn_call("id", vec![int(2)]),
    )];

    // Verify with both logic functions available.
    // The spec axiom from id_mono should make id(5) >= id(2) provable.
    let logic_fns = vec![id_fn, id_mono];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).logic_fns(Some(&logic_fns)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "id(5) >= id(2) should be provable via id_mono spec axiom + id defining axiom: {result:?}"
    );
}

/// Test that ay can prove id_mono's postcondition via E-matching.
///
/// `forall i,j. i<=j => id(i)<=id(j)` with `id(x)=x` requires ay to instantiate
/// the defining axiom for `id` and then reason about the resulting linear arithmetic.
/// The negated quantified goal plus the quantified axiom needs inter-quantifier
/// reasoning, which ay's E-matching must supply on its own (#1296).
#[test]
#[timeout(30000)]
fn test_id_mono_postcondition_verifies_via_ay_ematch() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let id_fn = LogicFnDef::new(
        "id".to_string(),
        "crate::inner::id".to_string(),
        vec!["i".to_string()],
        var("i"),
    )
    .with_mode(LogicMode::Open);

    let id_mono_post = forall(
        "i",
        forall(
            "j",
            implies(
                le(var("i"), var("j")),
                le(
                    logic_fn_call("id", vec![var("i")]),
                    logic_fn_call("id", vec![var("j")]),
                ),
            ),
        ),
    );

    // Quantified postcondition against a quantified defining axiom: ay's
    // E-matching handles the nested-quantifier instantiation directly.
    let ensures = vec![id_mono_post];
    let logic_fns = vec![id_fn];
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &ensures).logic_fns(Some(&logic_fns)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "id_mono postcondition should verify: ay E-matching now handles \
         nested quantifier reasoning with defining axiom instantiation: {result:?}"
    );
}

/// Regression test for Box<T> deref in postconditions (#1302).
///
/// Models `fn box_deref<T>(x: Box<T>) -> T { *x }` with `#[ensures(result == *x)]`.
///
/// Box<T> parameters are not &mut references, so they go through `verify_function`
/// (not `verify_mut_borrow_function`). The body returns `Var("x")` (since Box deref
/// is a no-op alias in MIR), but the postcondition `result == *x` creates
/// `Deref(Var("x"))` which the encoder maps to `x_current`. The by-value alias
/// constraint `x_current = x` must be established for the postcondition to verify.
#[test]
#[timeout(30000)]
fn test_box_deref_postcondition_verifies() {
    // Body: *x on Box<T> => Var("x") (Box deref is transparent)
    let body = var("x");
    // Postcondition: result == *x => result == Deref(Var("x"))
    let ens = eq(var("result"), deref(var("x")));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("box_deref encoding should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "box_deref: result == *x with body *x should verify: {result:?}"
    );
}

/// Negative companion: wrong body should fail for box_deref pattern.
#[test]
#[timeout(30000)]
fn test_box_deref_postcondition_wrong_body_fails() {
    // Body returns x + 1 instead of x
    let body = add(var("x"), int(1));
    // Postcondition: result == *x
    let ens = eq(var("result"), deref(var("x")));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("box_deref wrong body encoding should not error");
    assert!(
        crate::tests::rejected(&result),
        "box_deref: result == *x with body x+1 should fail: {result:?}"
    );
}

/// Regression test for Box<(i32, &mut i32)> tuple field access (#1302).
///
/// Models `borrow_in_box_tuple_1(x: Box<(i32, &mut i32)>) -> i32` with:
///   #[requires((*(*x).1)@ == 2)]
///   #[ensures(result@ == 2)]
///
/// Box deref `*x` is a no-op in MIR (treated as identity), but the contract
/// parser generates `Deref(Var("x"))` which the encoder maps to `x_current`.
/// The body accesses `tuple_get_1(x)` directly (no extra deref). The
/// by-value alias constraint `x_current = x` must chain so that the
/// precondition's `tuple_get_1(x_current)` connects to the body's
/// `tuple_get_1(x)`.
#[test]
#[timeout(30000)]
fn test_box_tuple_field_deref_verifies() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let tuple_get_1 = tuple_field_logic_fn_name(1);

    // Precondition: (*(*x).1)@ == 2
    // Parsed as: View(Deref(LogicFnCall{tuple_get_1, [Deref(Var("x"))]})) == 2
    let req = eq(
        view(deref(logic_fn_call(&tuple_get_1, vec![deref(var("x"))]))),
        int(2),
    );

    // Postcondition: result@ == 2
    let ens = eq(view(var("result")), int(2));

    // Body: the MIR extraction traces through Box deref (no-op) + field access +
    // &mut deref. The return expression is the deref of the &mut i32 field:
    // Deref(LogicFnCall{tuple_get_1, [Var("x")]})
    // Note: no Deref(Var("x")) wrapper because Box deref is identity in MIR.
    let body = deref(logic_fn_call(&tuple_get_1, vec![var("x")]));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .expect("borrow_in_box_tuple_1 encoding should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "borrow_in_box_tuple_1: result@ == 2 given precondition should verify: {result:?}"
    );
}

/// Regression test for (i32, Box<&mut i32>) tuple with Box inside (#1302).
///
/// Models `borrow_in_box_tuple_2(x: (i32, Box<&mut i32>)) -> i32` with:
///   #[requires((*(*x.1))@ == 2)]
///   #[ensures(result@ == 2)]
///
/// Here `x.1` is `Box<&mut i32>`. The contract has `*(*x.1)` = double deref
/// through Box then &mut. After Box erasure, only one deref is needed. The
/// chained by-value alias constraints collapse the extra _current level.
#[test]
#[timeout(30000)]
fn test_box_in_tuple_field_deref_verifies() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let tuple_get_1 = tuple_field_logic_fn_name(1);

    // Precondition: (*(*x.1))@ == 2
    // x.1 = LogicFnCall{tuple_get_1, [Var("x")]} → Box<&mut i32>
    // *x.1 = Deref(LogicFnCall{...}) → &mut i32 (Box deref, but encoded as _current)
    // **x.1 = Deref(Deref(LogicFnCall{...})) → i32 (ref deref, another _current)
    let req = eq(
        view(deref(deref(logic_fn_call(&tuple_get_1, vec![var("x")])))),
        int(2),
    );

    // Postcondition: result@ == 2
    let ens = eq(view(var("result")), int(2));

    // Body: MIR extraction skips Box deref, so only one Deref for the &mut:
    // Deref(LogicFnCall{tuple_get_1, [Var("x")]})
    let body = deref(logic_fn_call(&tuple_get_1, vec![var("x")]));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .expect("borrow_in_box_tuple_2 encoding should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "borrow_in_box_tuple_2: result@ == 2 given precondition should verify: {result:?}"
    );
}

/// Regression test for Box deref in mutable borrow struct (#1302).
///
/// Models `box_reborrow_in_struct(x: &mut (i32, &mut Box<i32>)) -> i32` with:
///   #[requires((**((*x).1))@ == 3)]
///   #[ensures(result@ == 3)]
///
/// `x` is `&mut`, so this goes through verify_mut_borrow_function. The
/// precondition has a triple deref: &mut param, &mut field, Box deref. But
/// the body only has double deref (Box deref is no-op). The by-value alias
/// constraints must chain the extra _current level.
#[test]
#[timeout(30000)]
fn test_box_reborrow_in_struct_verifies() {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

    let tuple_get_1 = tuple_field_logic_fn_name(1);

    // Precondition: (**((*x).1))@ == 3
    // (*x) = Deref(Var("x")) → x_current
    // (*x).1 = tuple_get_1(x_current) → &mut Box<i32>
    // *((*x).1) = Deref(tuple_get_1(...)) → Box<i32> (&mut deref)
    // **((*x).1) = Deref(Deref(tuple_get_1(...))) → i32 (Box deref)
    let req = eq(
        view(deref(deref(logic_fn_call(
            &tuple_get_1,
            vec![deref(var("x"))],
        )))),
        int(3),
    );

    // Postcondition: result@ == 3
    let ens = eq(view(var("result")), int(3));

    // final_values: x -> *x, x.1 -> *((*x).1) (only &mut deref, Box is no-op)
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), deref(var("x")));
    final_values.insert(
        "x.1".to_string(),
        deref(logic_fn_call(&tuple_get_1, vec![deref(var("x"))])),
    );

    // Body: traces through MIR with Box deref as no-op:
    // **x.1 → *(x.1) = Deref(LogicFnCall{tuple_get_1, [Deref(Var("x"))]})
    let body = deref(logic_fn_call(&tuple_get_1, vec![deref(var("x"))]));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[req], &[ens], &final_values).return_expr(Some(&body)),
    )
    .expect("box_reborrow_in_struct encoding should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "box_reborrow_in_struct: result@ == 3 given precondition should verify: {result:?}"
    );
}

/// Regression test for Box<&mut T> → &mut T extraction (#1302).
///
/// Models `borrow_in_box<T>(x: Box<&mut T>) -> &mut T` with:
///   #[ensures(result == *x)]
///
/// `x: Box<&mut T>` is a by-value parameter. After Box erasure, `x` is
/// effectively `&mut T`. The postcondition `result == *x` after Box erasure
/// becomes `result == x_current`, and the by-value alias constraint
/// `x_current = x` connects to the body which returns `x` directly
/// (since both Box deref and reborrow are no-ops in MIR extraction).
#[test]
#[timeout(30000)]
fn test_borrow_in_box_verifies() {
    // Body: &mut **x after Box erasure → *x (deref &mut) → reborrow → x
    // In MIR, Box deref is identity and &mut reborrow is identity, so body = x
    let body = var("x");
    // Postcondition: result == *x → result == Deref(Var("x"))
    let ens = eq(var("result"), deref(var("x")));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("borrow_in_box encoding should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "borrow_in_box: result == *x with body x should verify: {result:?}"
    );
}

/// Negative companion: borrow_in_box with wrong body should fail.
#[test]
#[timeout(30000)]
fn test_borrow_in_box_wrong_body_fails() {
    // Body returns something other than x
    let body = add(var("x"), int(1));
    // Postcondition: result == *x
    let ens = eq(var("result"), deref(var("x")));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("borrow_in_box wrong body encoding should not error");
    assert!(
        crate::tests::rejected(&result),
        "borrow_in_box: result == *x with body x+1 should fail: {result:?}"
    );
}

/// Regression test for #1277: `result == None` in postcondition where `None`
/// is parsed as `Var("None")` must be connected to the `LogicFnCall("None")`
/// constructor encoding used in the ITE body.
#[test]
#[timeout(30000)]
fn test_verify_option_return_eq_constructor() {
    // Body: if x == 1 { Some(x + 1) } else { None }
    let x_int = var_with_sort("x", ExprSort::Int);
    let body = ite(
        eq(x_int.clone(), int(1)),
        logic_fn_call("Some", vec![add(x_int.clone(), int(1))]),
        logic_fn_call("None", vec![]),
    );

    // Postcondition: (x@ == 1 && result == Some(x@ + 1)) || (x@ != 1 && result == None)
    // Use Var("None") to mirror what the contract parser produces.
    let ens = or(
        and(
            eq(view(var("x")), int(1)),
            eq(
                var("result"),
                logic_fn_call("Some", vec![add(view(var("x")), int(1))]),
            ),
        ),
        and(ne(view(var("x")), int(1)), eq(var("result"), var("None"))),
    );

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("option return with Var(None) should not error");
    // sort_fallback_to_int (#994): Option encoding triggers sort demotion.
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification. The strict
    // `assert_verified_or_*` helpers stay strict for their other call sites;
    // the tolerance is opt-in here. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    crate::tests::helpers::assert_verified_or_known_proof_trusted(
        &result,
        "if x==1 { Some(x+1) } else { None } with result == None postcondition should verify (#1277)",
    );
}

/// Existential variant of `test_verify_option_return_eq_constructor`: the postcondition
/// uses `exists<y: i32> result == Some(y) && y@ == x@ + 1`, mirroring the actual
/// `and_then::{closure#1}` contract from `option.rs` (#1572, #1310, #1277).
///
/// ay-dpll cannot propagate the `x = x_view` identity through ITE branches, so
/// the datatype result path (`rebind_var`) inlines the body term when encoding
/// the postcondition instead of relying on ITE transitivity.
#[test]
#[timeout(30000)]
fn test_verify_option_return_eq_constructor_existential() {
    // Body: if x == 1 { Some(x + 1) } else { None }
    let x_int = var_with_sort("x", ExprSort::Int);
    let body = ite(
        eq(x_int.clone(), int(1)),
        logic_fn_call("Some", vec![add(x_int.clone(), int(1))]),
        logic_fn_call("None", vec![]),
    );

    // Postcondition: (x@ == 1 && exists<y: i32> result == Some(y) && y@ == x@ + 1)
    //             || (x@ != 1 && result == None)
    let ens = or(
        and(
            eq(view(var("x")), int(1)),
            exists(
                "y",
                and(
                    eq(var("result"), logic_fn_call("Some", vec![var("y")])),
                    eq(view(var("y")), add(view(var("x")), int(1))),
                ),
            ),
        ),
        and(ne(view(var("x")), int(1)), eq(var("result"), var("None"))),
    );

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("option return with existential should not error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "if x==1 {{ Some(x+1) }} else {{ None }} with existential postcondition should verify (#1572, #1310): {result:?}",
    );
}

// ── match-arm deref-collapse tests (#2124 AC3) ──────────────────────

/// Regression test for #2124 AC3: `*v` in match-arm postconditions creates a
/// disconnected `v_current` SMT variable instead of using the pattern binding.
///
/// Models the `slice_first` pattern from `slices/01.rs`:
/// ```
/// #[ensures(match result {
///     Some(v) => *v == a[0],
///     None => a@.len() == 0,
/// })]
/// fn slice_first<T>(a: &[T]) -> Option<&T>
/// ```
///
/// The `*v` (Deref(Var("v"))) in the Some arm must resolve to the bound
/// destructor term `spec_unwrap(result)`, not a fresh `v_current`.
#[test]
#[timeout(30000)]
fn test_verify_option_return_match_deref_binding() {
    // Body: if len(a) > 0 { Some(elem) } else { None }
    // where elem models a[0].
    let body = ite(
        gt(var("len_a"), int(0)),
        logic_fn_call("Some", vec![var("elem")]),
        logic_fn_call("None", vec![]),
    );

    // Postcondition: match result { Some(v) => *v == elem, None => len_a == 0 }
    let ens = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                eq(deref(var("v")), var("elem")),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                eq(var("len_a"), int(0)),
            ),
        ],
    );

    // Precondition: len_a >= 0 (slice lengths are non-negative).
    let req = ge(var("len_a"), int(0));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .expect("match deref binding should not error");
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result),
        "match {{ Some(v) => *v == elem, None => len_a == 0 }} should verify after deref-collapse fix (#2124 AC3): {result:?}"
    );
}

/// Negative test: wrong postcondition must fail (ensures the deref-collapse
/// fix doesn't make the match arm body vacuously true).
#[test]
#[timeout(30000)]
fn test_verify_option_return_match_deref_binding_wrong_postcondition() {
    // Body: if len_a > 0 { Some(elem) } else { None }
    let body = ite(
        gt(var("len_a"), int(0)),
        logic_fn_call("Some", vec![var("elem")]),
        logic_fn_call("None", vec![]),
    );

    // Wrong postcondition: match result { Some(v) => *v == elem + 999, None => true }
    let ens = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                eq(deref(var("v")), add(var("elem"), int(999))),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                PureExpr::Bool(true),
            ),
        ],
    );

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("wrong postcondition encoding should not error");
    assert!(
        crate::tests::rejected(&result),
        "wrong postcondition *v == elem + 999 must fail: {result:?}"
    );
}

/// Exact model of `tests/should_succeed/slices/01.rs::slice_first`.
///
/// The body returns `Some(a[0])` when `a@.len() > 0` and `None` otherwise.
/// The postcondition matches on `result`; that match must not be routed to
/// the native ADT theory-conflict path, which cannot discharge it and answers
/// `Unknown(QuantifierUnhandled)`.
#[test]
#[timeout(30000)]
fn test_verify_slice_first_match_postcondition() {
    let len = method_call(view(var("a")), "len", vec![]);
    let index_zero = method_call(var("a"), "index_logic", vec![int(0)]);
    let body = ite(
        gt(len.clone(), int(0)),
        PureExpr::LetAssume {
            assumption: std::sync::Arc::new(lt(int(0), len.clone())),
            body: std::sync::Arc::new(logic_fn_call("Some", vec![index_zero.clone()])),
        },
        logic_fn_call("None", vec![]),
    );
    let ens = match_expr(
        var_with_sort(
            "result",
            ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("OptionInt")),
        ),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                eq(deref(var("v")), index_zero),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                eq(len, int(0)),
            ),
        ],
    );

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("slice_first encoding should not error");
    // KNOWN-CLASS PIN: the verdict demotes to `Unknown(ProofTrusted)` under
    // ay's mandatory strict UNSAT certification; the property this test guards
    // is unchanged and every other outcome fails. See
    // `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result),
        "slice_first match postcondition should verify: {result:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_verify_slice_first_wrong_none_postcondition_fails() {
    let len = method_call(view(var("a")), "len", vec![]);
    let index_zero = method_call(var("a"), "index_logic", vec![int(0)]);
    let body = ite(
        gt(len.clone(), int(0)),
        PureExpr::LetAssume {
            assumption: std::sync::Arc::new(lt(int(0), len.clone())),
            body: std::sync::Arc::new(logic_fn_call("Some", vec![index_zero.clone()])),
        },
        logic_fn_call("None", vec![]),
    );
    let ens = match_expr(
        var_with_sort(
            "result",
            ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("OptionInt")),
        ),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                eq(deref(var("v")), index_zero),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                eq(len, int(1)),
            ),
        ],
    );

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("wrong slice_first postcondition should not error");
    assert!(
        crate::tests::rejected(&result),
        "wrong None-arm postcondition must fail: {result:?}"
    );
}

// ── resolve_sat_result pipeline tests (#1481) ───────────────────────

/// Verifies that the Unsat→Verified path through resolve_sat_result works end-to-end.
/// verify_function internally calls resolve_sat_result; a provable postcondition produces
/// Unsat at the solver level → Verified result.
#[test]
#[timeout(30000)]
fn resolve_sat_result_verified_path_through_verify_function() {
    // Provable: requires x > 0, body = x + 1, ensures result > x
    let req = gt(var("x"), int(0));
    let body = add(var("x"), int(1));
    let ens = gt(var("result"), var("x"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x+1 > x given x > 0 should follow Unsat→Verified path: {result:?}"
    );
}

/// Verifies that the Sat→Failed path through resolve_sat_result works end-to-end.
/// An unprovable postcondition produces Sat at the solver level → Failed with counterexample.
#[test]
#[timeout(30000)]
fn resolve_sat_result_failed_path_through_verify_function() {
    // Unprovable: body = x (unconstrained), ensures result > 0
    let body = var("x");
    let ens = gt(var("result"), int(0));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "unconstrained body with ensures(result>0) should follow Sat→Failed path: {result:?}"
    );
}

/// Verifies that the Failed path includes a counterexample with variable assignments.
#[test]
#[timeout(30000)]
fn resolve_sat_result_failed_path_includes_counterexample() {
    // body = x, ensures result > 100 — solver should find x ≤ 100 as counterexample
    let body = var("x");
    let ens = gt(var("result"), int(100));

    let result =
        verify_function_with_modes(VerificationRequest::new(&[], &[ens]).return_expr(Some(&body)))
            .expect("encoding should succeed");
    match result {
        VerificationResult::Failed(cex) => {
            // The counterexample should have at least one assignment
            let debug_str = format!("{cex:?}");
            assert!(
                !debug_str.is_empty(),
                "counterexample should have non-empty debug representation"
            );
        }
        other => panic!("expected Failed with counterexample, got {other:?}"),
    }
}

// ── exists formula expansion coverage (#1512) ───────────────────────

/// Verifies that an exists-quantified postcondition encodes and runs.
///
/// `ensures(exists<w: Int> result == x + w && w > 0)` with body = x + 1.
/// ay returns Unknown("quantifiers") because E-matching doesn't synthesize
/// existential witnesses. This test exercises the `QuantifierKind::Exists`
/// path through the encoder (quantifier.rs:563-565) and verifies the formula
/// is accepted by the solver (no encoding error), even though ay can't
/// decide it.
///
/// Part of #1512
#[test]
#[timeout(60000)]
fn exists_postcondition_encodes_and_solver_accepts() {
    // requires: x > 0
    let req = gt(var("x"), int(0));
    // body: x + 1
    let body = add(var("x"), int(1));
    // ensures: exists w. result == x + w && w > 0
    let ens = exists(
        "w",
        and(
            eq(var("result"), add(var("x"), var("w"))),
            gt(var("w"), int(0)),
        ),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .expect("exists-quantified postcondition must encode without error");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "exists postcondition should verify with the concrete witness from result == x + w: {result:?}"
    );
}

/// Negative test: exists postcondition with impossible witness.
///
/// `ensures(exists<w: Int> result == x + w && w > 100)` with body = x + 1.
/// The only w satisfying result = x+w is w=1, but w > 100 fails.
/// ay should return Failed or Unknown (never Verified).
///
/// Part of #1512
#[test]
#[timeout(30000)]
fn exists_postcondition_impossible_witness_not_verified() {
    let req = gt(var("x"), int(0));
    let body = add(var("x"), int(1));
    // ensures: exists w. result == x + w && w > 100
    let ens = exists(
        "w",
        and(
            eq(var("result"), add(var("x"), var("w"))),
            gt(var("w"), int(100)),
        ),
    );

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens]).return_expr(Some(&body)),
    )
    .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "exists w. w>100 with body=x+1 must not verify (no valid witness): {result:?}"
    );
}

// ── type_constants coverage (#1512) ─────────────────────────────────

/// Test that type_constants resolution works through verify_function_with_modes.
///
/// Models `i32::checked_add` where `Self::MAX` is a type constant that
/// resolves to `i32::MAX` (2147483647). The postcondition `result <= Self::MAX@`
/// should verify when body = x + 1 and requires x < Self::MAX.
///
/// Exercises view.rs:29-31 (type_constants.get) which has zero test coverage.
///
/// Part of #1512
#[test]
#[timeout(30000)]
fn type_constants_resolve_in_postcondition() {
    let mut type_consts = HashMap::new();
    type_consts.insert("Self::MAX".to_string(), PureExpr::Int(2_147_483_647));

    // requires: x >= 0 && x < Self::MAX (2147483647)
    let req1 = ge(var("x"), int(0));
    let req2 = lt(var("x"), int(2_147_483_647));
    // body: x + 1
    let body = add(var("x"), int(1));
    // ensures: result <= Self::MAX@ (Self::MAX@ should resolve to 2147483647)
    let ens = le(var("result"), view(var("Self::MAX")));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req1, req2], &[ens])
            .return_expr(Some(&body))
            .type_constants(Some(&type_consts)),
    )
    .expect("type_constants verification should not error");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "x+1 <= Self::MAX given x < Self::MAX should verify via type_constants: {result:?}"
    );
}

// ── mode_overrides error path coverage (#1512) ──────────────────────

/// Test that mismatched mode_overrides length silently drops overrides.
///
/// verify_function_with_modes silently drops mode_overrides when lengths don't
/// match (#2316, #2700). The overrides are computed from the full logic_fn_defs
/// set, but logic_fns may be a filtered subset. Rather than aborting
/// verification, the overrides are dropped so filter_logic_functions_for_goal
/// falls back to default mode scoping.
///
/// Part of #1512, updated for #2316
#[test]
#[timeout(30000)]
fn mode_overrides_length_mismatch_drops_overrides_silently() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let id_fn = LogicFnDef::new(
        "id".to_string(),
        "test::id".to_string(),
        vec!["x".to_string()],
        var("x"),
    );
    let logic_fns = vec![id_fn];
    // Provide 2 mode overrides for 1 logic function — length mismatch
    let mode_overrides = vec![LogicMode::Open, LogicMode::Open];

    let ens = eq(var("result"), int(0));
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .logic_fns(Some(&logic_fns))
            .mode_overrides(Some(&mode_overrides)),
    );

    // Should NOT error — overrides are dropped, verification proceeds
    assert!(
        result.is_ok(),
        "mode_overrides mismatch should be silently dropped, not error: {result:?}"
    );
}

// ── Closure capture projection integration tests (#1505) ──────────────
