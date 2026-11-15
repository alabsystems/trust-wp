// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[path = "nonzero_quantified_invariants/tuple_congruence_diagnostics.rs"]
mod tuple_congruence_diagnostics;

// --- Creusot non_zero.rs pattern: by-value invariant add/sub (#359) ---

/// Test NonZero add by value: adding two positive integers yields a positive result.
///
/// Models Creusot's `reference/creusot/tests/should_succeed/type_invariants/non_zero.rs`:
/// ```rust
/// #[invariant(self.0@ > 0)]
/// struct NonZeroU32(pub u32);
///
/// #[requires(self.0@ + rhs.0@ <= u32::MAX@)]
/// pub fn add(self, rhs: Self) -> Self {
///     Self(self.0 + rhs.0)
/// }
/// ```
///
/// With newtype simplification, `self.0@` becomes `self`, so the invariant body
/// is `self > 0`. The auto-injected clauses become:
/// - requires: self.invariant() && rhs.invariant()  (i.e., self > 0 && rhs > 0)
/// - ensures: result.invariant()  (i.e., result > 0)
/// Body: result = self + rhs
/// Since self > 0 and rhs > 0, result = self + rhs > 0. QED.
#[test]
#[timeout(30000)]
fn test_verify_nonzero_add_by_value_preserves_invariant() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: self.invariant() && rhs.invariant()
    let req_self = method_call(var("self_"), &inv_method, vec![]);
    let req_rhs = method_call(var("rhs"), &inv_method, vec![]);

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = self + rhs
    let body = add(var("self_"), var("rhs"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_rhs], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZero add(self, rhs) should preserve invariant: self>0 + rhs>0 => result>0: got {result:?}"
    );
}

/// Negative test: NonZero sub by value without sufficient precondition fails.
///
/// Models the case where `fn sub(self, rhs: Self) -> Self` with body `self - rhs`
/// only has the auto-injected invariant preconditions (self > 0, rhs > 0).
/// Since self=1, rhs=1 gives result=0 which violates self > 0, this should fail.
///
/// In Creusot, the `sub` function requires `self.sub_pre(rhs)` (i.e., self > rhs)
/// as an additional precondition. Without it, verification fails.
#[test]
#[timeout(30000)]
fn test_verify_nonzero_sub_by_value_without_extra_precondition_fails() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: only auto-injected invariants (self > 0 && rhs > 0)
    let req_self = method_call(var("self_"), &inv_method, vec![]);
    let req_rhs = method_call(var("rhs"), &inv_method, vec![]);

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = self - rhs
    let body = sub(var("self_"), var("rhs"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_rhs], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "NonZero sub(self, rhs) without sub_pre should produce counterexample: got {result:?}"
    );
}

/// Identity function preserves trivial invariant (Creusot parity: type_invariants.rs `id`).
///
/// Models:
/// ```rust
/// #[invariant(true)]
/// struct WithInvariant;
///
/// fn id(x: WithInvariant) -> WithInvariant {
///     x
/// }
/// ```
///
/// Models Creusot's `type_invariants.rs` identity function. Uses non-trivial
/// invariant `self > 0` (not `true`) to ensure the test exercises the invariant
/// axiom and transfer logic. Body `result = x` preserves any invariant.
#[test]
#[timeout(30000)]
fn test_verify_invariant_identity_function() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Positive");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant()  (i.e., x > 0)
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: result.invariant()  (i.e., result > 0)
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = x
    let body = var("x");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "identity function with invariant should verify via body transfer: got {result:?}"
    );
}

/// Negative test for identity function: ensure invariant is actually checked.
///
/// Uses the same Positive (self > 0) invariant but body `result = 0`,
/// which violates the postcondition invariant. If the encoder weren't
/// checking invariants, this would trivially pass.
#[test]
#[timeout(30000)]
fn test_verify_invariant_identity_function_violation() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Positive");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: x.invariant()
    let req = method_call(var("x"), &inv_method, vec![]);

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = 0 (violates result > 0)
    let body = int(0);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "identity function returning 0 should FAIL invariant check: got {result:?}"
    );
}

/// Positive test: NonZero sub with additional precondition `self > rhs` succeeds.
///
/// Models Creusot's:
/// ```rust
/// #[requires(self.sub_pre(rhs))] // self.0@ > rhs.0@
/// pub fn sub(self, rhs: Self) -> Self {
///     Self(self.0 - rhs.0)
/// }
/// ```
///
/// With sub_pre meaning self > rhs, we have:
/// - self > 0, rhs > 0 (invariants)
/// - self > rhs (extra precondition)
/// - result = self - rhs > 0 (since self > rhs > 0)
#[test]
#[timeout(30000)]
fn test_verify_nonzero_sub_by_value_with_sub_pre_succeeds() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: self.invariant() && rhs.invariant() && self > rhs
    let req_self = method_call(var("self_"), &inv_method, vec![]);
    let req_rhs = method_call(var("rhs"), &inv_method, vec![]);
    let sub_pre = gt(var("self_"), var("rhs"));

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = self - rhs
    let body = sub(var("self_"), var("rhs"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_rhs, sub_pre], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZero sub(self, rhs) with sub_pre should verify: self>rhs>0 => self-rhs>0: got {result:?}"
    );
}

/// Positive test: NonZero sub with method-style `self.sub_pre(rhs)` precondition.
///
/// This is the exact ay-level analogue of the Creusot `NonZeroU32::sub` test case.
/// Unlike `test_verify_nonzero_sub_by_value_with_sub_pre_succeeds` which uses the
/// arithmetic expansion `self > rhs`, this test uses `PureExpr::MethodCall` to
/// encode `self.sub_pre(rhs)` — the same form that arrives from MIR extraction.
///
/// The registered open logic function `sub_pre(x, y) = x > y` must be resolved
/// by the method call dispatch path (`try_logic_fn_dispatch`) for the precondition
/// to constrain the VC. (#2341)
#[test]
#[timeout(30000)]
fn test_verify_nonzero_sub_by_value_with_method_sub_pre() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // Logic function: sub_pre(x, y) = x > y (open mode)
    let mut sub_pre_fn = LogicFnDef::new(
        "sub_pre".to_string(),
        "NonZero::sub_pre".to_string(),
        vec!["x".to_string(), "y".to_string()],
        gt(var("x"), var("y")),
    );
    sub_pre_fn.set_mode(LogicMode::Open);

    // requires: self.invariant() && rhs.invariant() && self.sub_pre(rhs)
    let req_self = method_call(var("self_"), &inv_method, vec![]);
    let req_rhs = method_call(var("rhs"), &inv_method, vec![]);
    // Method-style precondition: self_.sub_pre(rhs)
    let req_sub_pre = method_call(var("self_"), "sub_pre", vec![var("rhs")]);

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = self - rhs
    let body = sub(var("self_"), var("rhs"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_rhs, req_sub_pre], &[ens])
            .return_expr(Some(&body))
            .logic_fns(Some(&[sub_pre_fn]))
            .type_invariants(Some(&[inv_def])),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "NonZero sub(self, rhs) with method-style sub_pre should verify: got {result:?}"
    );
}

/// NonZero constructor verification (Creusot parity: non_zero.rs `new`).
///
/// Models:
/// ```rust
/// #[invariant(self.0@ > 0)]
/// struct NonZeroU32(pub u32);
///
/// #[requires(n@ > 0)]
/// pub fn new(n: u32) -> Self {
///     Self(n)
/// }
/// ```
///
/// With newtype simplification: requires n > 0, body result = n.
/// Postcondition: result.invariant() expands to result > 0.
/// Since result = n and n > 0, this is trivially true.
#[test]
#[timeout(30000)]
fn test_verify_nonzero_new_constructor() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: n > 0
    let req = gt(var("n"), int(0));

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = n
    let body = var("n");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZero::new(n) with n>0 should establish invariant: got {result:?}"
    );
}

/// NonZero constructor without precondition fails (negative test).
///
/// If we don't require n > 0, the invariant result > 0 cannot be proved
/// because n could be 0.
#[test]
#[timeout(30000)]
fn test_verify_nonzero_new_without_precondition_fails() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // No precondition on n

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = n
    let body = var("n");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        crate::tests::rejected(&result),
        "NonZero::new(n) without precondition should produce counterexample (n=0): got {result:?}"
    );
}

/// Two distinct types with different invariants in the same verification context.
///
/// Models a function that takes a NonZero (inv: self > 0) and a Bounded
/// (inv: self >= 1 && self <= 100), verifying both invariants are independently
/// tracked and applied without interference.
///
/// ```rust
/// #[invariant(self.0 > 0)]
/// struct NonZero(i32);
///
/// #[invariant(self.0 >= 1 && self.0 <= 100)]
/// struct Bounded(i32);
///
/// fn combine(a: NonZero, b: Bounded) -> NonZero {
///     NonZero(a.0 + b.0) // a>0, 1<=b<=100, so a+b>0
/// }
/// ```
#[test]
#[timeout(30000)]
fn test_verify_two_type_invariants_in_same_context() {
    let inv_nonzero = trust_wp_core::logic::type_invariant_method_name("NonZero");
    let inv_bounded = trust_wp_core::logic::type_invariant_method_name("Bounded");

    let nonzero_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    let bounded_def = trust_wp_core::type_invariant_def! {
        type_name: "Bounded".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: and(ge(var("self"), int(1)), le(var("self"), int(100))),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: a.invariant() && b.invariant()
    let req_a = method_call(var("a"), &inv_nonzero, vec![]);
    let req_b = method_call(var("b"), &inv_bounded, vec![]);

    // ensures: result.invariant() (NonZero)
    let ens = method_call(var("result"), &inv_nonzero, vec![]);

    // body: result = a + b (a > 0, b >= 1, so a + b > 0)
    let body = add(var("a"), var("b"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_a, req_b], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[nonzero_def, bounded_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "combine(NonZero, Bounded) -> NonZero should verify: a>0 + b>=1 => a+b>0: got {result:?}"
    );
}

/// sub_pre transitivity lemma with type invariants and logic function.
///
/// Models Creusot's `non_zero.rs`:
/// ```rust
/// #[logic(open)]
/// pub fn sub_pre(self, rhs: Self) -> bool {
///     pearlite! { self.0@ > rhs.0@ }
/// }
///
/// #[logic(open)]
/// #[requires(a.sub_pre(b))]
/// #[requires(b.sub_pre(c))]
/// #[ensures(a.sub_pre(c))]
/// pub fn sub_pre_trans(a: Self, b: Self, c: Self) {}
/// ```
///
/// The lemma: a > b && b > c => a > c (transitivity of >).
/// This tests logic function + type invariant interaction.
#[test]
#[timeout(30000)]
fn test_verify_sub_pre_trans_logic_lemma_with_invariants() {
    use trust_wp_core::logic::LogicFnDef;

    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // Logic function: sub_pre(x, y) = x > y
    // Mode is Open (#[logic(open)]) so the defining axiom is emitted.
    let mut sub_pre_fn = LogicFnDef::new(
        "sub_pre".to_string(),
        "NonZero::sub_pre".to_string(),
        vec!["x".to_string(), "y".to_string()],
        gt(var("x"), var("y")),
    );
    sub_pre_fn.set_mode(trust_wp_core::logic::LogicMode::Open);

    // requires: a.invariant() && b.invariant() && c.invariant()
    let req_a_inv = method_call(var("a"), &inv_method, vec![]);
    let req_b_inv = method_call(var("b"), &inv_method, vec![]);
    let req_c_inv = method_call(var("c"), &inv_method, vec![]);

    // requires: sub_pre(a, b)  (a > b)
    let req_ab = logic_fn_call("sub_pre", vec![var("a"), var("b")]);
    // requires: sub_pre(b, c)  (b > c)
    let req_bc = logic_fn_call("sub_pre", vec![var("b"), var("c")]);

    // ensures: sub_pre(a, c)  (a > c)
    let ens = logic_fn_call("sub_pre", vec![var("a"), var("c")]);

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_a_inv, req_b_inv, req_c_inv, req_ab, req_bc], &[ens])
            .logic_fns(Some(&[sub_pre_fn]))
            .type_invariants(Some(&[inv_def])),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "sub_pre_trans: a>b && b>c => a>c should verify: got {result:?}"
    );
}

// --- Compat-level regression: View operator in contracts (#2669) ---

/// NonZero::new with View operator in precondition (compat regression #2669).
///
/// Models the EXACT encoding that the compat harness produces for:
/// ```rust
/// #[requires(n@ > 0)]
/// pub fn new(n: u32) -> Self {
///     Self(n)
/// }
/// ```
///
/// The `n@` in the contract becomes `View(Var("n"))`, which the ay encoder
/// declares as a separate `n_view` variable with `n == n_view`. The body
/// `result = n` uses the raw `n` variable. The postcondition `result.invariant()`
/// inlines to `result > 0`. The chain: `n_view > 0 ∧ n == n_view → n > 0`,
/// `result = n → result > 0`.
///
/// This test uses `View(Var("n"))` in the precondition to reproduce the compat
/// failure where the simplified ay-level test passes (no View) but the compat
/// test fails (with View).
#[test]
#[timeout(30000)]
fn test_verify_nonzero_new_with_view_precondition() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: n@ > 0  (View(Var("n")) > 0, NOT Var("n") > 0)
    let req = gt(view(var("n")), int(0));

    // ensures: result.invariant()  (inlines to result > 0)
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = n (newtype simplification collapses Self(n) to n)
    let body = var("n");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZero::new(n) with View precondition n@ > 0 should verify: got {result:?}"
    );
}

/// NonZero::add with View operator in precondition and field access in body (#2669).
///
/// Models the compat encoding for:
/// ```rust
/// #[requires(self.0@ + rhs.0@ <= u32::MAX@)]
/// pub fn add(self, rhs: Self) -> Self {
///     Self(self.0 + rhs.0)
/// }
/// ```
///
/// After newtype simplification at the driver level:
/// - `self.0@` → `View(Var("self_"))` (field-0 simplified to self, then viewed)
/// - Body: `self.0 + rhs.0` → `self_ + rhs` (field-0 simplified)
///
/// The auto-injected invariant clauses are:
/// - requires: self_.invariant() ∧ rhs.invariant() (both > 0)
/// - ensures: result.invariant() (result > 0)
/// Plus the user precondition: View(self_) + View(rhs) <= MAX (unused for positivity proof).
///
/// This test uses the simplified form (no View in body), matching what the
/// driver produces after newtype simplification.
#[test]
#[timeout(30000)]
fn test_verify_nonzero_add_with_view_precondition() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("NonZero");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "NonZero".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // requires: self.invariant() && rhs.invariant()
    let req_self = method_call(var("self_"), &inv_method, vec![]);
    let req_rhs = method_call(var("rhs"), &inv_method, vec![]);
    // User precondition: self_@ + rhs@ <= MAX (view form)
    // For simplicity, encode the view form but the key constraint is the invariants.
    let req_overflow = le(
        add(view(var("self_")), view(var("rhs"))),
        int(u32::MAX as i64),
    );

    // ensures: result.invariant()
    let ens = method_call(var("result"), &inv_method, vec![]);

    // body: result = self_ + rhs (newtype-simplified from Self(self.0 + rhs.0))
    let body = add(var("self_"), var("rhs"));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[req_self, req_rhs, req_overflow], &[ens])
            .return_expr(Some(&body))
            .type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "NonZero::add with view precondition should verify: got {result:?}"
    );
}

// --- Creusot quant.rs parity: quantifier + type invariant interaction (#359) ---

/// Creusot `quant.rs` parity: forall<x: T> x.invariant() ==> x > 0.
///
/// With body axiom `forall self. invariant(self) ⟺ (self > 0)`, the
/// implication `invariant(x) ==> x > 0` follows directly. ay now
/// correctly instantiates the body axiom to verify this (previously
/// returned Unknown("quantifiers") before the ay pin bump).
#[test]
#[timeout(30000)]
fn test_verify_forall_invariant_implication_ay_limitation() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Positive");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // ensures: forall x. x.invariant() ==> x > 0
    // Encode ==> as (!lhs || rhs) since PureExpr doesn't have Implies
    let ens = forall(
        "x",
        or(
            not(method_call(var("x"), &inv_method, vec![])),
            gt(var("x"), int(0)),
        ),
    );

    // No requires, no body — this is a logic lemma about the invariant
    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    // Eager body inlining (#726) replaces inv(x) with (x > 0) inside the
    // quantifier, making this `forall x. (x > 0) ==> x > 0` — trivially true.
    // Previously fixed by ay pin bump; now also covered by trust-wp-side inlining.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "forall x. invariant(x) ==> x > 0 should be Verified. Got: {result:?}"
    );
}

/// Creusot `quant.rs` parity: exists<x: T> x.invariant().
///
/// The existential `exists x. invariant(x)` should be provable because
/// the body axiom gives `invariant(x) ⟺ (x > 0)`, and there exists
/// at least one integer > 0 (e.g., 1).
///
/// Previously returned Unknown("quantifiers") because ay could not compose
/// the body axiom with the postcondition quantifier via E-matching. Fixed
/// by eager invariant body inlining (#726): `inv(x)` is replaced with
/// `x > 0` inside quantifier scopes, so `exists x. x > 0` is trivially
/// satisfiable.
#[test]
#[timeout(30000)]
fn test_verify_exists_inhabited_invariant_type() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Positive");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // ensures: exists x. x.invariant()
    let ens = exists("x", method_call(var("x"), &inv_method, vec![]));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "exists x. invariant(x) should be Verified with body inlining: got {result:?}"
    );
}

/// Negative test: forall<x: T> x.invariant() SHOULD NOT be provable when
/// invariant body is non-trivial.
///
/// With body axiom `invariant(x) ⟺ (x > 0)`, the statement `forall x.
/// invariant(x)` is false because x = -1 is a counterexample. ay now
/// correctly returns Failed with a counterexample. Previously returned
/// Verified (ay#2829) and before that Unknown("quantifiers").
#[test]
#[timeout(30000)]
fn test_verify_forall_invariant_not_universally_true() {
    let inv_method = trust_wp_core::logic::type_invariant_method_name("Positive");

    let inv_def = trust_wp_core::type_invariant_def! {
        type_name: "Positive".to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: gt(var("self"), int(0)),
        is_newtype: true,
        element_invariant_method: None,
    };

    // ensures: forall x. x.invariant()  — should FAIL
    let ens = forall("x", method_call(var("x"), &inv_method, vec![]));

    let result = verify_function_with_modes(
        VerificationRequest::new(&[], &[ens]).type_invariants(Some(&[inv_def])),
    )
    .unwrap();
    // ay correctly returns Failed — `forall x. x > 0` is false because x = -1
    // is a counterexample. This improved from Verified (ay#2829 limitation) and
    // before that from Unknown("quantifiers"). The Failed result is the CORRECT
    // answer: the universal invariant is not provable.
    assert!(
        matches!(result, VerificationResult::Failed(..)),
        "forall x. invariant(x) should return Failed (x=-1 is a counterexample \
         to forall x. x > 0). Got: {result:?}"
    );
}
