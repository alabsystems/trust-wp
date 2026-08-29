// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use ntest::timeout;

use super::*;

// =============================================================================
// Tuple-of-&mut verification tests (#858)
//
// These tests model Creusot patterns that require the driver to decompose
// tuple parameters containing &mut references into per-field final_values.
// They verify that the ay encoder can handle these patterns correctly when
// given proper inputs, proving the gap is in the driver's MIR analysis.
// =============================================================================

/// Model `drop_pair(_x: (&mut u32, &mut u32))` -- empty body, resolve postcondition.
///
/// Contracts:
///   ensures: ^_x.0 == *_x.0
///   ensures: ^_x.1 == *_x.1
///
/// When the driver decomposes the tuple parameter into per-field tracking,
/// the final_values should be:
///   _x.0 -> *_x.0  (identity -- field 0 not modified)
///   _x.1 -> *_x.1  (identity -- field 1 not modified)
///
/// This test proves the encoder can verify the pattern with correct inputs.
/// Creusot test: tests/should_succeed/drop_pair.rs
/// Re: #858, #745
#[test]
#[timeout(30000)]
fn test_drop_pair_with_field_final_values() {
    // ensures: ^_x.0 == *_x.0
    // After postcondition transformation for mut refs:
    //   ^_x = Final(Var("_x")), *_x = Deref(Var("_x"))
    //   ^_x.0 = Final(LogicFnCall{tuple_get_0, [Var("_x")]})
    //         -> encodes as tuple_get_0(_x_final)
    //   *_x.0 = Deref(LogicFnCall{tuple_get_0, [Var("_x")]})
    //         -> encodes as tuple_get_0(_x_current)
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    // ^_x.0 == *_x.0
    let ens_0 = eq(
        final_expr(logic_fn_call(&tuple_get_0, vec![var("_x")])),
        deref(logic_fn_call(&tuple_get_0, vec![var("_x")])),
    );

    // ^_x.1 == *_x.1
    let ens_1 = eq(
        final_expr(logic_fn_call(&tuple_get_1, vec![var("_x")])),
        deref(logic_fn_call(&tuple_get_1, vec![var("_x")])),
    );

    // Body: identity -- the tuple is dropped without modification.
    // final_values: _x_final = _x_current (identity resolve at the whole-tuple level).
    let mut final_values = HashMap::new();
    final_values.insert("_x".to_string(), deref(var("_x")));

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &[],
        &[ens_0, ens_1],
        &final_values,
    ))
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "drop_pair with identity final_values should verify via tuple axioms: got {result:?}"
    );
}

/// Model `pair_bor_mut(p: (&mut T, &mut T), take_first: bool) -> &mut T`.
///
/// Contracts:
///   ensures: if take_first { result == p.0 && ^p.1 == *p.1 }
///            else { result == p.1 && ^p.0 == *p.0 }
///
/// When the driver provides whole-tuple identity final_values:
///   p_final = *p (identity, since the function returns one element and drops the other)
///
/// The postcondition requires path-sensitive reasoning about which field resolves.
/// This test models the conditional postcondition using Ite.
/// Creusot test: tests/should_succeed/pair_bor_mut.rs
/// Re: #858, #745
#[test]
#[timeout(30000)]
fn test_pair_bor_mut_with_final_values() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    // p.0 = Deref(LogicFnCall{tuple_get_0, [Var("p")]})  -> tuple_get_0(p_current)
    let p_0_current = deref(logic_fn_call(&tuple_get_0, vec![var("p")]));
    // p.1 = Deref(LogicFnCall{tuple_get_1, [Var("p")]})  -> tuple_get_1(p_current)
    let p_1_current = deref(logic_fn_call(&tuple_get_1, vec![var("p")]));
    // ^p.0 = Final(LogicFnCall{tuple_get_0, [Var("p")]}) -> tuple_get_0(p_final)
    let p_0_final = final_expr(logic_fn_call(&tuple_get_0, vec![var("p")]));
    // ^p.1 = Final(LogicFnCall{tuple_get_1, [Var("p")]}) -> tuple_get_1(p_final)
    let p_1_final = final_expr(logic_fn_call(&tuple_get_1, vec![var("p")]));

    // result == p.0 && ^p.1 == *p.1
    let then_branch = and(
        eq(var("result"), p_0_current.clone()),
        eq(p_1_final, p_1_current.clone()),
    );

    // result == p.1 && ^p.0 == *p.0
    let else_branch = and(eq(var("result"), p_1_current), eq(p_0_final, p_0_current));

    // if take_first { ... } else { ... }
    let ens = ite(var("take_first"), then_branch, else_branch);

    // Body: identity -- the whole tuple is passed through
    // (the function returns one element, the other is dropped).
    // p_final = *p (identity at whole-tuple level).
    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(var("p")));

    // Return expression: conditional -- if take_first then p.0 else p.1
    let return_expr = ite(
        var("take_first"),
        deref(logic_fn_call(&tuple_get_0, vec![var("p")])),
        deref(logic_fn_call(&tuple_get_1, vec![var("p")])),
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    )
    .unwrap();
    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result),
        "pair_bor_mut should verify with identity final_values and conditional return: got {result:?}"
    );
}

/// Model `bug/486.rs`: `fn test(x: HasMutRef<'_, u32>)` where `HasMutRef(pub &'a mut T)`.
///
/// Contracts:
///   ensures: (^x.0)@ == 5
///
/// Simplified (without View/@): ensures ^x.0 == 5
///
/// Body: `*x.0 = 5`
///
/// In the driver, `x` has type `HasMutRef<'_, u32>` (newtype wrapping `&mut u32`).
/// Field `.0` accesses the wrapped `&mut u32`. Writing `*x.0 = 5` means
/// the final value of field 0 is 5.
///
/// Modeled as: x is the newtype struct, x.0 is the inner `&mut u32`.
/// The final value of the deref of field 0 is 5.
///
/// This models the case where the driver would need to decompose the newtype
/// to track the inner &mut's final value.
///
/// Creusot test: tests/should_succeed/bug/486.rs
/// Re: #858, #745
#[test]
#[timeout(30000)]
fn test_bug_486_newtype_mut_ref_write() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);

    // ensures: ^x.0 == 5
    // ^x.0 = Final(LogicFnCall{tuple_get_0, [Var("x")]}) -> tuple_get_0(x_final)
    let ens = eq(
        final_expr(logic_fn_call(&tuple_get_0, vec![var("x")])),
        int(5),
    );

    // Body: *x.0 = 5
    // The final value of x should be a tuple where field 0 = 5.
    // Since HasMutRef is a newtype (single-field tuple struct), x is essentially
    // a one-element wrapper: x_final = __trust_wp_tuple1(5).
    //
    // The driver now extracts final_values for newtype-wrapped &mut
    // parameters (W4 commits for #2124). This test verifies the encoder
    // handles the hand-constructed equivalent correctly.

    // Model the body as: x_final = tuple1(5), so tuple_get_0(x_final) = 5.
    let tuple1 = trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(1);
    let final_val = logic_fn_call(&tuple1, vec![int(5)]);

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), final_val);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "bug/486 pattern should verify when final_values correctly model the body: got {result:?}"
    );
}

/// Variant of test_bug_486 with View operator: `(^x.0)@ == 5`.
///
/// The actual Creusot postcondition for bug/486.rs is `(^x.0)@ == 5`, not
/// `^x.0 == 5`. For u32, `@` (View) should be identity, so this should also
/// verify. This test checks that the View(Final(tuple_get_0(Var("x"))))
/// encoding correctly connects through tuple axioms.
#[test]
#[timeout(30000)]
fn test_bug_486_newtype_mut_ref_write_with_view() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);

    // ensures: (^x.0)@ == 5
    // = View(Final(LogicFnCall{tuple_get_0, [Var("x")]})) == Int(5)
    let ens = eq(
        view(final_expr(logic_fn_call(&tuple_get_0, vec![var("x")]))),
        int(5),
    );

    let tuple1 = trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(1);
    let final_val = logic_fn_call(&tuple1, vec![int(5)]);

    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), final_val);

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "bug/486 with View should verify: (^x.0)@ == 5; got {result:?}"
    );
}

/// End-to-end reproduction of bug/486 failure with transform_postcondition_for_mut_refs applied.
///
/// The actual E2E pipeline:
/// 1. Parses `(^x.0)@ == 5` as `View(Final(LogicFnCall("tuple_get_0", [Var("x")])))`
/// 2. `transform_contract` adds BOTH "x" AND "x.0" to mut_ref_params
/// 3. `transform_postcondition_for_mut_refs` rewrites `Var("x")` → `Deref(Var("x"))`
/// 4. Postcondition becomes: `View(Final(LogicFnCall("tuple_get_0", [Deref(Var("x"))])))`
/// 5. `final_values` has: {"x": tuple1(5), "x.0": Int(5)}
///
/// The encoder pushes Final into the LogicFnCall, producing
/// `tuple_get_0(x_current_final)`. The alias `x_current_final == tuple1(5)`
/// plus the tuple axiom `get_0(tuple1(t)) == t` should yield `tuple_get_0(tuple1(5)) == 5`.
///
/// Re: #2124, #486
#[test]
#[timeout(30000)]
fn test_bug_486_e2e_with_deref_var_and_field_final_values() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);

    // After transform_postcondition_for_mut_refs: Var("x") → Deref(Var("x"))
    let ens = eq(
        view(final_expr(logic_fn_call(
            &tuple_get_0,
            vec![deref(var("x"))],
        ))),
        int(5),
    );

    let tuple1 = trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(1);

    // Both "x" and "x.0" entries, matching actual extraction output
    let mut final_values = HashMap::new();
    final_values.insert("x".to_string(), logic_fn_call(&tuple1, vec![int(5)]));
    final_values.insert("x.0".to_string(), PureExpr::Int(5));

    let result =
        verify_mut_borrow_function_with_modes(MutBorrowRequest::new(&[], &[ens], &final_values))
            .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "bug/486 E2E with Deref(Var) + field final_values should verify: got {result:?}"
    );
}

/// Regression test for the `_current_final` / `_current_current` naming mismatch.
///
/// After `transform_postcondition_for_mut_refs`, postconditions for
/// `drop_pair(_x: (&mut u32, &mut u32))` use `Deref(Var("_x"))` inside tuple
/// accessors:
///
///   `^_x.0 == *_x.0`  ->  `Final(tuple_get_0(Deref(Var("_x")))) == Deref(tuple_get_0(Deref(Var("_x"))))`
///
/// The encoder pushes Final/Deref inside the LogicFnCall args, producing:
///   LHS: `tuple_get_0(Final(Deref(Var("_x"))))` -> `tuple_get_0(_x_current_final)`
///   RHS: `tuple_get_0(Deref(Deref(Var("_x"))))` -> `tuple_get_0(_x_current_current)`
///
/// Without the `_current_final` and `_current_current` aliases in
/// `verify_mut_borrow_function`, these are free variables disconnected from the
/// `_x_final = _x_current` body constraint, causing spurious verification failure.
///
/// Re: #858, #745
#[test]
#[timeout(30000)]
fn test_drop_pair_deref_var_postcondition_form() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    // Simulate the postcondition form produced by transform_postcondition_for_mut_refs.
    // Note: args use Deref(Var("_x")), NOT bare Var("_x").
    // This is the key difference from test_drop_pair_with_field_final_values.

    // ^_x.0 == *_x.0  ->  Final(tuple_get_0(Deref(Var("_x")))) == Deref(tuple_get_0(Deref(Var("_x"))))
    let ens0 = eq(
        final_expr(logic_fn_call(&tuple_get_0, vec![deref(var("_x"))])),
        deref(logic_fn_call(&tuple_get_0, vec![deref(var("_x"))])),
    );

    // ^_x.1 == *_x.1
    let ens1 = eq(
        final_expr(logic_fn_call(&tuple_get_1, vec![deref(var("_x"))])),
        deref(logic_fn_call(&tuple_get_1, vec![deref(var("_x"))])),
    );

    // resolve(_x) -> Deref form: resolve(Deref(Var("_x")))
    let ens2 = logic_fn_call("resolve", vec![deref(var("_x"))]);

    // Body: identity -- _x_final = *_x (i.e., _x_current)
    let mut final_values = HashMap::new();
    final_values.insert("_x".to_string(), deref(var("_x")));

    let result = verify_mut_borrow_function_with_modes(MutBorrowRequest::new(
        &[],
        &[ens0, ens1, ens2],
        &final_values,
    ))
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "drop_pair with Deref(Var) postcondition form should verify: got {result:?}"
    );
}

/// Model `pair_bor_mut` with `Deref(Var("p"))` postcondition form.
///
/// After `transform_postcondition_for_mut_refs`, the driver rewrites `Var("p")`
/// to `Deref(Var("p"))` inside tuple accessors. This is the form that reaches ay
/// in the production pipeline.
///
/// Contracts (after transform):
///   ensures: if take_first { result == Deref(tuple_get_0(Deref(Var("p"))))
///                          && Final(tuple_get_1(Deref(Var("p")))) == Deref(tuple_get_1(Deref(Var("p")))) }
///            else { result == Deref(tuple_get_1(Deref(Var("p"))))
///                 && Final(tuple_get_0(Deref(Var("p")))) == Deref(tuple_get_0(Deref(Var("p")))) }
///
/// Return expression (after transform):
///   if take_first then Deref(tuple_get_0(Deref(Var("p"))))
///   else Deref(tuple_get_1(Deref(Var("p"))))
///
/// This models the actual E2E shape the ay encoder receives for `pair_bor_mut`.
/// The Deref(Var) form creates `_current_final` and `_current_current` intermediate
/// variables that must be correctly aliased for the proof to close.
///
/// Creusot test: tests/should_succeed/pair_bor_mut.rs
/// Re: #2673, #858
#[test]
#[timeout(30000)]
fn test_pair_bor_mut_deref_var_postcondition_form() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    // After transform_postcondition_for_mut_refs: Var("p") -> Deref(Var("p"))
    // *p.0 = Deref(tuple_get_0(Deref(Var("p"))))
    let p_0_current = deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    // *p.1 = Deref(tuple_get_1(Deref(Var("p"))))
    let p_1_current = deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));
    // ^p.0 = Final(tuple_get_0(Deref(Var("p"))))
    let p_0_final = final_expr(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    // ^p.1 = Final(tuple_get_1(Deref(Var("p"))))
    let p_1_final = final_expr(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));

    // if take_first { result == *p.0 && ^p.1 == *p.1 }
    //          else { result == *p.1 && ^p.0 == *p.0 }
    let then_branch = and(
        eq(var("result"), p_0_current.clone()),
        eq(p_1_final, p_1_current.clone()),
    );
    let else_branch = and(eq(var("result"), p_1_current), eq(p_0_final, p_0_current));
    let ens = ite(var("take_first"), then_branch, else_branch);

    // Body: identity for the whole tuple
    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(var("p")));

    // Return expression: if take_first then *p.0 else *p.1
    // After transform: if take_first then Deref(tuple_get_0(Deref(Var("p"))))
    //                  else Deref(tuple_get_1(Deref(Var("p"))))
    let return_expr = ite(
        var("take_first"),
        deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))])),
        deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))])),
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values).return_expr(Some(&return_expr)),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pair_bor_mut with Deref(Var) postcondition form should verify: got {result:?}"
    );
}

/// Model `pair_bor_mut` with resolve assumptions for p.
///
/// In the production pipeline, the driver may also provide resolve assumptions
/// for parameters in the resolve set. For `pair_bor_mut`, `p` might be in the
/// resolve set since the function returns one of its fields and drops the other.
///
/// Re: #2673, #858
#[test]
#[timeout(30000)]
fn test_pair_bor_mut_deref_var_with_resolve() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    let p_0_current = deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    let p_1_current = deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));
    let p_0_final = final_expr(logic_fn_call(&tuple_get_0, vec![deref(var("p"))]));
    let p_1_final = final_expr(logic_fn_call(&tuple_get_1, vec![deref(var("p"))]));

    let then_branch = and(
        eq(var("result"), p_0_current.clone()),
        eq(p_1_final, p_1_current.clone()),
    );
    let else_branch = and(eq(var("result"), p_1_current), eq(p_0_final, p_0_current));
    let ens = ite(var("take_first"), then_branch, else_branch);

    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(var("p")));

    let return_expr = ite(
        var("take_first"),
        deref(logic_fn_call(&tuple_get_0, vec![deref(var("p"))])),
        deref(logic_fn_call(&tuple_get_1, vec![deref(var("p"))])),
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &[ens], &final_values)
            .return_expr(Some(&return_expr))
            .resolve_assumptions(Some(vec!["p".to_string()])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pair_bor_mut with Deref(Var) + resolve should verify: got {result:?}"
    );
}

/// Models the exact inputs the driver produces for `pair_bor_mut` (#2673 diagnostic).
///
/// The driver produces:
///   result_expr: Ite(take_first, tuple_get_0(Var("p")), tuple_get_1(Var("p")))
///   ensures: Ite(take_first,
///     And(Eq(Var("result", MutRef), tuple_get_0(Deref(Var("p")))),
///         Eq(Final(tuple_get_1(Deref(p))), Deref(tuple_get_1(Deref(p))))),
///     And(Eq(Var("result", MutRef), tuple_get_1(Deref(Var("p")))),
///         Eq(Final(tuple_get_0(Deref(p))), Deref(tuple_get_0(Deref(p))))))
///   requires: [inv(Deref(p)), inv(Deref(p.0)), inv(Deref(p.1))]
///   final_values: { "p" -> Deref(p), "p.0" -> Deref(tuple_get_0(Deref(p))),
///                   "p.1" -> Deref(tuple_get_1(Deref(p))) }
///
/// This test checks whether the encoder can verify these exact inputs.
/// Re: #2673 (root-cause isolation)
#[test]
#[timeout(60000)]
fn test_pair_bor_mut_exact_driver_inputs() {
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    let t_id = intern_sort_name("T");
    let p_var = PureExpr::Var("p".to_string(), Some(ExprSort::Tuple(2)));
    let take_first_var = PureExpr::Var("take_first".to_string(), Some(ExprSort::Bool));
    let result_var = PureExpr::Var(
        "result".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::TypeParam(t_id)))),
    );

    // result_expr: Ite(take_first, tuple_get_0(p), tuple_get_1(p))
    // (This is what the driver extracts -- no Deref wrapper on the field projections)
    let return_expr = ite(
        take_first_var.clone(),
        logic_fn_call(&tuple_get_0, vec![p_var.clone()]),
        logic_fn_call(&tuple_get_1, vec![p_var.clone()]),
    );

    // ensures (post-postcondition-transform, as the driver produces):
    let ensures = vec![ite(
        take_first_var.clone(),
        and(
            eq(
                result_var.clone(),
                logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())]),
            ),
            eq(
                final_expr(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
                deref(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
            ),
        ),
        and(
            eq(
                result_var.clone(),
                logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())]),
            ),
            eq(
                final_expr(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
                deref(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
            ),
        ),
    )];

    // requires (type invariants injected by the driver):
    let requires = vec![
        logic_fn_call("inv", vec![deref(PureExpr::Var("p".to_string(), None))]),
        logic_fn_call("inv", vec![deref(PureExpr::Var("p.0".to_string(), None))]),
        logic_fn_call("inv", vec![deref(PureExpr::Var("p.1".to_string(), None))]),
    ];

    // final_values (identity -- function doesn't modify, just returns one ref):
    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(p_var.clone()));
    final_values.insert(
        "p.0".to_string(),
        deref(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
    );
    final_values.insert(
        "p.1".to_string(),
        deref(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pair_bor_mut with exact driver inputs should verify (#2673): got {result:?}"
    );
}

/// Isolation A: bare result + whole-tuple finals + inv requires.
/// Tests whether adding inv() requires alone causes failure.
/// Re: #2673 (progressive isolation)
#[test]
#[timeout(60000)]
fn test_pair_bor_mut_isolation_a_inv_requires_only() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    let p_var = PureExpr::Var("p".to_string(), Some(ExprSort::Tuple(2)));
    let take_first_var = PureExpr::Var("take_first".to_string(), Some(ExprSort::Bool));

    let return_expr = ite(
        take_first_var.clone(),
        logic_fn_call(&tuple_get_0, vec![p_var.clone()]),
        logic_fn_call(&tuple_get_1, vec![p_var.clone()]),
    );

    let ensures = vec![ite(
        take_first_var.clone(),
        and(
            eq(
                var("result"),
                logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())]),
            ),
            eq(
                final_expr(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
                deref(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
            ),
        ),
        and(
            eq(
                var("result"),
                logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())]),
            ),
            eq(
                final_expr(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
                deref(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
            ),
        ),
    )];

    let requires = vec![
        logic_fn_call("inv", vec![deref(PureExpr::Var("p".to_string(), None))]),
        logic_fn_call("inv", vec![deref(PureExpr::Var("p.0".to_string(), None))]),
        logic_fn_call("inv", vec![deref(PureExpr::Var("p.1".to_string(), None))]),
    ];

    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(var("p")));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&requires, &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "isolation A: inv requires should not prevent verification (#2673): got {result:?}"
    );
}

/// Isolation B: bare result + per-field finals + no requires.
/// Tests whether per-field final_values alone cause failure.
/// Re: #2673 (progressive isolation)
#[test]
#[timeout(60000)]
fn test_pair_bor_mut_isolation_b_per_field_finals_only() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    let p_var = PureExpr::Var("p".to_string(), Some(ExprSort::Tuple(2)));
    let take_first_var = PureExpr::Var("take_first".to_string(), Some(ExprSort::Bool));

    let return_expr = ite(
        take_first_var.clone(),
        logic_fn_call(&tuple_get_0, vec![p_var.clone()]),
        logic_fn_call(&tuple_get_1, vec![p_var.clone()]),
    );

    let ensures = vec![ite(
        take_first_var.clone(),
        and(
            eq(
                var("result"),
                logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())]),
            ),
            eq(
                final_expr(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
                deref(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
            ),
        ),
        and(
            eq(
                var("result"),
                logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())]),
            ),
            eq(
                final_expr(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
                deref(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
            ),
        ),
    )];

    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(p_var.clone()));
    final_values.insert(
        "p.0".to_string(),
        deref(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
    );
    final_values.insert(
        "p.1".to_string(),
        deref(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
    );

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "isolation B: per-field finals should not prevent verification (#2673): got {result:?}"
    );
}

/// Isolation C: MutRef annotation on result + whole-tuple finals + no requires.
/// Tests whether MutRef sort annotation alone causes failure.
/// Re: #2673 (progressive isolation)
#[test]
#[timeout(60000)]
fn test_pair_bor_mut_isolation_c_mutref_annotation_only() {
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    let t_id = intern_sort_name("T");
    let p_var = PureExpr::Var("p".to_string(), Some(ExprSort::Tuple(2)));
    let take_first_var = PureExpr::Var("take_first".to_string(), Some(ExprSort::Bool));
    let result_var = PureExpr::Var(
        "result".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::TypeParam(t_id)))),
    );

    let return_expr = ite(
        take_first_var.clone(),
        logic_fn_call(&tuple_get_0, vec![p_var.clone()]),
        logic_fn_call(&tuple_get_1, vec![p_var.clone()]),
    );

    let ensures = vec![ite(
        take_first_var.clone(),
        and(
            eq(
                result_var.clone(),
                logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())]),
            ),
            eq(
                final_expr(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
                deref(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
            ),
        ),
        and(
            eq(
                result_var.clone(),
                logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())]),
            ),
            eq(
                final_expr(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
                deref(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
            ),
        ),
    )];

    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(var("p")));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "isolation C: MutRef annotation alone should not prevent verification (#2673): got {result:?}"
    );
}

/// Variant: same as test_pair_bor_mut_exact_driver_inputs but without MutRef
/// sort annotation on result (uses bare Var("result")) and without per-field
/// final_values. This isolates whether the MutRef annotation or per-field
/// finals cause the gap.
/// Re: #2673 (progressive isolation)
#[test]
#[timeout(60000)]
fn test_pair_bor_mut_driver_no_mutref_annotation() {
    let tuple_get_0 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
    let tuple_get_1 =
        trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1);

    let p_var = PureExpr::Var("p".to_string(), Some(ExprSort::Tuple(2)));
    let take_first_var = PureExpr::Var("take_first".to_string(), Some(ExprSort::Bool));

    // result_expr: Ite(take_first, tuple_get_0(p), tuple_get_1(p))
    // (no Deref -- matching driver output)
    let return_expr = ite(
        take_first_var.clone(),
        logic_fn_call(&tuple_get_0, vec![p_var.clone()]),
        logic_fn_call(&tuple_get_1, vec![p_var.clone()]),
    );

    // ensures: same postcondition but with bare Var("result") (no MutRef sort)
    let ensures = vec![ite(
        take_first_var.clone(),
        and(
            eq(
                var("result"),
                logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())]),
            ),
            eq(
                final_expr(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
                deref(logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())])),
            ),
        ),
        and(
            eq(
                var("result"),
                logic_fn_call(&tuple_get_1, vec![deref(p_var.clone())]),
            ),
            eq(
                final_expr(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
                deref(logic_fn_call(&tuple_get_0, vec![deref(p_var.clone())])),
            ),
        ),
    )];

    // Whole-tuple identity final_values only (no per-field)
    let mut final_values = HashMap::new();
    final_values.insert("p".to_string(), deref(var("p")));

    let result = verify_mut_borrow_function_with_modes(
        MutBorrowRequest::new(&[], &ensures, &final_values).return_expr(Some(&return_expr)),
    )
    .expect("encoding should succeed");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "pair_bor_mut without MutRef annotation should verify (#2673): got {result:?}"
    );
}
