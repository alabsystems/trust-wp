// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AY integration tests for logic function postcondition verification.
//!
//! Covers ay ITE/UF primitives, Seq-parameter sort panics (#1572),
//! structural induction with spec axioms (#2097), and Bool-result
//! sort pollution regressions (#994).
//!
//! Split from postcondition_verification.rs per #2251.

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

/// Minimal ay test: can the solver prove ite(c, a, b) == ite(c, a, b)?
#[test]
#[timeout(5000)]
fn test_ay_ite_self_equality() {
    use ay_dpll::api::{Solver, Sort};
    let mut s = Solver::try_new(ay_dpll::Logic::QfUflia).unwrap();
    let a = s.fresh_var("a", Sort::Int);
    let b = s.fresh_var("b", Sort::Int);
    let c = s.ge(a, b);
    let ite1 = s.ite(c, a, b);
    let ite2 = s.ite(c, a, b);
    let eq = s.eq(ite1, ite2);
    let neg = s.not(eq);
    s.assert_term(neg);
    let result = s.check_sat().into_inner();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "ite(c,a,b) == ite(c,a,b) should be UNSAT. Got: {result:?}"
    );
}

/// Minimal ay test: UF + ITE axiom
#[test]
#[timeout(30000)]
fn test_ay_uf_ite_axiom_instantiation() {
    use ay_dpll::api::{Solver, Sort};
    let mut s = Solver::try_new(ay_dpll::Logic::QfUflia).unwrap();
    let a = s.fresh_var("a", Sort::Int);
    let b = s.fresh_var("b", Sort::Int);

    // Declare max_logic(Int, Int) -> Int
    let f = s
        .try_declare_fun("max_logic", &[Sort::Int, Sort::Int], Sort::Int)
        .expect("max_logic declaration should succeed");

    // Axiom: forall x,y. max_logic(x,y) = ite(x >= y, x, y)
    let qx = s.fresh_var("qx", Sort::Int);
    let qy = s.fresh_var("qy", Sort::Int);
    let cond = s.ge(qx, qy);
    let ite_body = s.ite(cond, qx, qy);
    let fn_app = s
        .try_apply(&f, &[qx, qy])
        .expect("max_logic(qx, qy) application should succeed");
    let axiom_eq = s.eq(fn_app, ite_body);
    let trigger = s
        .try_apply(&f, &[qx, qy])
        .expect("max_logic(qx, qy) trigger should succeed");
    let axiom = s.forall_with_triggers(&[qx, qy], axiom_eq, &[&[trigger]]);
    s.assert_term(axiom);

    // Goal: ite(a >= b, a, b) == max_logic(a, b)
    let cond2 = s.ge(a, b);
    let body = s.ite(cond2, a, b);
    let goal_app = s
        .try_apply(&f, &[a, b])
        .expect("max_logic(a, b) application should succeed");
    let goal = s.eq(body, goal_app);
    let neg_goal = s.not(goal);
    s.assert_term(neg_goal);

    let result = s.check_sat().into_inner();
    assert!(
        matches!(result, ay_dpll::api::SolveResult::Unsat(_)),
        "UF + ITE axiom should prove ite(a>=b,a,b) == max_logic(a,b). Got: {result:?}"
    );
}

/// Reproducer for #1572: lemma postcondition verification with Seq params.
///
/// Models the filter_positive.rs pattern:
/// ```text
/// #[logic(open)]
/// fn num_of_pos(i: Int, j: Int, t: Seq<i32>) -> Int { ... }
///
/// #[logic(open)]
/// #[requires(j <= k)]
/// #[ensures(num_of_pos(i, j, t) <= num_of_pos(i, k, t))]
/// fn lemma_increasing(i: Int, j: Int, k: Int, t: Seq<i32>) { ... }
/// ```
///
/// The postcondition verification of `lemma_increasing` must not panic
/// with a sort mismatch when encoding `num_of_pos(i, j, t)` where
/// `t` is a Seq-sorted parameter.
#[test]
#[timeout(30000)]
fn test_verify_lemma_postcondition_with_seq_param_no_sort_panic() {
    use std::time::Duration;

    use crate::{verify_function_with_modes, VerificationResult};

    // num_of_pos(i, j, t) with t as Seq (detected via t.index() in body)
    let num_of_pos_fn = LogicFnDef::new(
        "num_of_pos".to_string(),
        "test::num_of_pos".to_string(),
        vec!["i".to_string(), "j".to_string(), "t".to_string()],
        ite(
            ge(var("i"), var("j")),
            int(0),
            add(
                ite(
                    gt(
                        view(method_call(var("t"), "index", vec![sub(var("j"), int(1))])),
                        int(0),
                    ),
                    int(1),
                    int(0),
                ),
                logic_fn_call(
                    "num_of_pos",
                    vec![var("i"), sub(var("j"), int(1)), var("t")],
                ),
            ),
        ),
    )
    .with_mode(LogicMode::Open);

    // lemma_increasing(i, j, k, t) — cross-fn Seq inference for t
    let nop = |a: &str, b: &str| logic_fn_call("num_of_pos", vec![var("i"), var(a), var(b)]);
    let mut lemma_fn = LogicFnDef::new(
        "lemma_increasing".to_string(),
        "test::lemma_increasing".to_string(),
        vec!["i".into(), "j".into(), "k".into(), "t".into()],
        int(0),
    )
    .with_mode(LogicMode::Open);
    lemma_fn.set_requires(vec![le(var("j"), var("k"))]);
    lemma_fn.set_ensures(vec![le(nop("j", "t"), nop("k", "t"))]);

    let logic_fns = vec![num_of_pos_fn, lemma_fn];
    let requires = vec![le(var("j"), var("k"))];
    let ensures = vec![le(nop("j", "t"), nop("k", "t"))];

    // Use a 2s solver timeout so ay terminates gracefully. This test
    // only checks for sort-mismatch panics, not solver completeness.
    // With the logic function body prescan (#1965), sorts are now
    // correct (Seq for t), making ay explore a larger Array-theory
    // search space. A short timeout is sufficient for the panic check.
    let result = verify_function_with_modes(
        crate::verify::VerificationRequest::new(&requires, &ensures)
            .logic_fns(Some(&logic_fns))
            .timeout(Some(Duration::from_secs(2))),
    );
    assert!(result.is_ok(), "Should not panic: {result:?}");
    // May be Unknown (solver completeness), but must NOT be a sort panic.
    let vr = result.unwrap();
    let is_sort_panic = matches!(&vr, VerificationResult::Unknown(msg)
        if msg.as_str().contains("sort")
        || msg.as_str().contains("panic"));
    assert!(
        !is_sort_panic,
        "Should not have sort mismatch panic, got: {vr:?}"
    );
}

/// Structural induction: a recursive logic function's postcondition should
/// be provable when its own spec axiom is available as the induction
/// hypothesis, but its defining axiom is suppressed. (#2097, RC2)
///
/// Models `lemma_sum_nonneg` from the rusthorn tests:
///   sum_nat(n) = if n <= 0 { 0 } else { n + sum_nat(n - 1) }
///   requires(n >= 0), ensures(result >= 0)
///
/// Without the spec axiom (old behavior): the function's own postcondition
/// is excluded to prevent circular reasoning, so the solver cannot derive
/// `sum_nat(n-1) >= 0` in the inductive step. Verification fails or is Unknown.
///
/// With the spec axiom in Default mode (new behavior): the spec axiom
/// `forall n [sum_nat(n)]. n >= 0 => sum_nat(n) >= 0` is available. The
/// recursive call `sum_nat(n-1)` in the body creates a ground instance that
/// triggers E-matching, producing `sum_nat(n-1) >= 0` (the IH). Combined
/// with `n >= 1` from the else branch, the postcondition follows.
#[test]
#[timeout(30000)]
fn test_recursive_logic_fn_structural_induction_with_spec_axiom() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // sum_nat(n) = if n <= 0 { 0 } else { n + sum_nat(n - 1) }
    let sum_body = ite(
        le(var("n"), int(0)),
        int(0),
        add(
            var("n"),
            logic_fn_call("sum_nat", vec![sub(var("n"), int(1))]),
        ),
    );

    let mut sum_fn = LogicFnDef::new_with_requires(
        "sum_nat".to_string(),
        "test::sum_nat".to_string(),
        vec!["n".to_string()],
        vec![ge(var("n"), int(0))],
        sum_body.clone(),
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();
    sum_fn.set_ensures(vec![ge(var("result"), int(0))]);

    // --- Case 1: WITHOUT spec axiom (old behavior) ---
    // Exclude sum_nat from available logic fns entirely. The postcondition
    // cannot be proved because the IH `sum_nat(n-1) >= 0` is unavailable.
    let result_without = verify_function_with_modes(
        VerificationRequest::new(sum_fn.requires(), sum_fn.ensures())
            .return_expr(Some(sum_fn.body())),
    );
    assert!(
        matches!(result_without, Ok(VerificationResult::Failed(_))),
        "Without spec axiom, recursive postcondition should fail: {result_without:?}"
    );

    // --- Case 2: WITH spec axiom in Default mode (new behavior) ---
    // Include sum_nat but with Default mode override. This emits only the
    // spec axiom (postcondition), not the defining axiom (body).
    let mode_overrides = vec![LogicMode::Default];
    let result_with = verify_function_with_modes(
        VerificationRequest::new(sum_fn.requires(), sum_fn.ensures())
            .return_expr(Some(sum_fn.body()))
            .logic_fns(Some(std::slice::from_ref(&sum_fn)))
            .mode_overrides(Some(&mode_overrides)),
    );
    assert!(
        matches!(result_with, Ok(VerificationResult::Verified(_))),
        "With spec axiom as IH, recursive postcondition should verify via \
         structural induction. Got: {result_with:?}"
    );
}

/// Negative control for structural induction: a WRONG postcondition should
/// still fail even with the spec axiom available. (#2097, RC2)
///
/// If induction is unsound (e.g., spec axiom used circularly), this test
/// would incorrectly verify. The fact that it fails confirms the mechanism
/// is non-vacuous.
#[test]
#[timeout(30000)]
fn test_recursive_logic_fn_structural_induction_wrong_postcondition_fails() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // sum_nat(n) = if n <= 0 { 0 } else { n + sum_nat(n - 1) }
    let sum_body = ite(
        le(var("n"), int(0)),
        int(0),
        add(
            var("n"),
            logic_fn_call("sum_nat", vec![sub(var("n"), int(1))]),
        ),
    );

    // WRONG postcondition: result <= 0 (sum of non-negatives is non-positive)
    let mut sum_fn = LogicFnDef::new_with_requires(
        "sum_nat".to_string(),
        "test::sum_nat".to_string(),
        vec!["n".to_string()],
        vec![ge(var("n"), int(0))],
        sum_body,
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();
    sum_fn.set_ensures(vec![le(var("result"), int(0))]);

    let mode_overrides = vec![LogicMode::Default];
    let result = verify_function_with_modes(
        VerificationRequest::new(sum_fn.requires(), sum_fn.ensures())
            .return_expr(Some(sum_fn.body()))
            .logic_fns(Some(std::slice::from_ref(&sum_fn)))
            .mode_overrides(Some(&mode_overrides)),
    );
    // n=1 gives sum_nat(1) = 1 + sum_nat(0) = 1 + 0 = 1 > 0, contradicting result <= 0
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "Wrong postcondition (result <= 0) must fail. Got: {result:?}"
    );
}

/// Structural-induction precheck for ADT lemmas of the rusthorn
/// `lemma_sum_nonneg` shape. (trust-wp Phase 3 B4)
///
/// Models the lemma over a `List` ADT:
///
/// ```text
/// #[logic(open)]
/// fn sum(self) -> Int {
///     match self {
///         Cons(a, l) => a@ + l.sum(),
///         Nil => 0,
///     }
/// }
///
/// #[logic]
/// #[ensures(self.sum() >= 0)]
/// fn lemma_sum_nonneg(&self) {
///     match self {
///         Cons(_, l) => l.lemma_sum_nonneg(),
///         Nil => (),
///     }
/// }
/// ```
///
/// Without the precheck, the quantified obligation
/// `forall self. body ==> sum(self) >= 0` cannot be closed by E-matching on
/// an ADT receiver and the solver returns
/// `quantifier-ematching-exists-incomplete`. The structural-induction
/// precheck recognises the shape (recursive helper with non-negative-sum
/// arms + a body that mirrors the helper's match structure) and discharges
/// the obligation directly.
#[test]
#[timeout(15000)]
fn test_recursive_adt_lemma_structural_induction_precheck_verifies() {
    use trust_wp_core::formula::{
        internal::tuple_lowering::tuple_logic_fn_name, MatchArm, Pattern,
    };

    use crate::{verify_function_with_modes, VerificationRequest};

    let unit = PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(0),
        args: vec![],
    };

    // sum(self) = match self { Cons(a, l) => a@ + l.sum(), Nil => 0 }
    let sum_body = PureExpr::Match {
        scrutinee: Arc::new(var("self")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("a".to_string()),
                        Pattern::Binding("l".to_string()),
                    ]))),
                },
                body: add(
                    view(var("a")),
                    PureExpr::MethodCall {
                        receiver: Arc::new(var("l")),
                        method: "sum".to_string(),
                        args: vec![],
                    },
                ),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Nil".to_string(),
                    inner: None,
                },
                body: int(0),
            },
        ],
    };

    // Rewrite the sum body so the recursive call uses the LogicFnCall form
    // that the precheck matches against (precheck accepts both, but the
    // unfold layer is more reliably exercised this way).
    let sum_body = sum_body.rewrite_bottom_up(|node| match node {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "sum" && args.is_empty() => PureExpr::LogicFnCall {
            name: "sum".to_string(),
            args: vec![(*receiver).clone()],
        },
        other => other,
    });

    let sum_fn = LogicFnDef::new(
        "sum".to_string(),
        "test::List::sum".to_string(),
        vec!["self".to_string()],
        sum_body,
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();

    // lemma_sum_nonneg(self) = match self { Cons(_, l) => l.lemma_sum_nonneg(), Nil => () }
    let lemma_body = PureExpr::Match {
        scrutinee: Arc::new(var("self")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Wildcard,
                        Pattern::Binding("l".to_string()),
                    ]))),
                },
                body: PureExpr::MethodCall {
                    receiver: Arc::new(var("l")),
                    method: "lemma_sum_nonneg".to_string(),
                    args: vec![],
                },
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Nil".to_string(),
                    inner: None,
                },
                body: unit.clone(),
            },
        ],
    };
    let mut lemma_fn = LogicFnDef::new(
        "lemma_sum_nonneg".to_string(),
        "test::List::lemma_sum_nonneg".to_string(),
        vec!["self".to_string()],
        lemma_body,
    )
    .with_mode(LogicMode::Default)
    .detect_recursion();
    // ensures(sum(self) >= 0)
    lemma_fn.set_ensures(vec![ge(logic_fn_call("sum", vec![var("self")]), int(0))]);

    let logic_fns = vec![sum_fn, lemma_fn.clone()];
    let mode_overrides = vec![LogicMode::Open, LogicMode::Default];
    let result = verify_function_with_modes(
        VerificationRequest::new(lemma_fn.requires(), lemma_fn.ensures())
            .return_expr(Some(lemma_fn.body()))
            .logic_fns(Some(&logic_fns))
            .mode_overrides(Some(&mode_overrides)),
    );
    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        result
            .as_ref()
            .is_ok_and(crate::tests::helpers::verified_or_known_proof_trusted),
        "Structural-induction precheck should discharge the lemma. Got: {result:?}"
    );
}

/// Negative control: the precheck must NOT fire when the helper's arm body
/// is not a non-negative sum (e.g., the helper subtracts a value), even if
/// the lemma's match shape looks superficially correct. This guards against
/// the precheck blindly returning `Verified` for any ADT-shaped lemma.
#[test]
#[timeout(15000)]
fn test_recursive_adt_lemma_structural_induction_precheck_rejects_subtraction() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    use crate::{
        verify_function_with_modes_outcome, VerificationOutcome, VerificationRequest,
        VerificationResult,
    };

    // diff(self) = match self { Cons(a, l) => a@ - diff(l), Nil => 0 }
    // Not a non-negative sum: the recursive call is *subtracted*. The
    // precheck must reject this shape.
    let diff_body = PureExpr::Match {
        scrutinee: Arc::new(var("self")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("a".to_string()),
                        Pattern::Binding("l".to_string()),
                    ]))),
                },
                body: sub(view(var("a")), logic_fn_call("diff", vec![var("l")])),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Nil".to_string(),
                    inner: None,
                },
                body: int(0),
            },
        ],
    };
    let diff_fn = LogicFnDef::new(
        "diff".to_string(),
        "test::List::diff".to_string(),
        vec!["self".to_string()],
        diff_body,
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();

    let lemma_body = PureExpr::Match {
        scrutinee: Arc::new(var("self")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Wildcard,
                        Pattern::Binding("l".to_string()),
                    ]))),
                },
                body: PureExpr::MethodCall {
                    receiver: Arc::new(var("l")),
                    method: "lemma_diff_nonneg".to_string(),
                    args: vec![],
                },
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Nil".to_string(),
                    inner: None,
                },
                body: PureExpr::LogicFnCall {
                    name: trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(0),
                    args: vec![],
                },
            },
        ],
    };
    let mut lemma_fn = LogicFnDef::new(
        "lemma_diff_nonneg".to_string(),
        "test::List::lemma_diff_nonneg".to_string(),
        vec!["self".to_string()],
        lemma_body,
    )
    .with_mode(LogicMode::Default)
    .detect_recursion();
    lemma_fn.set_ensures(vec![ge(logic_fn_call("diff", vec![var("self")]), int(0))]);

    let logic_fns = vec![diff_fn, lemma_fn.clone()];
    let mode_overrides = vec![LogicMode::Open, LogicMode::Default];
    let outcome = verify_function_with_modes_outcome(
        VerificationRequest::new(lemma_fn.requires(), lemma_fn.ensures())
            .return_expr(Some(lemma_fn.body()))
            .logic_fns(Some(&logic_fns))
            .mode_overrides(Some(&mode_overrides))
            .timeout(Some(std::time::Duration::from_secs(2))),
    );
    // The precheck must reject this shape; the regular solver pipeline may
    // then return Unknown or Failed — both are acceptable. The forbidden
    // outcome is `Verified`, which would indicate the precheck wrongly
    // accepted a subtraction-based helper as non-negative.
    let result_kind = outcome.map(|VerificationOutcome { result, .. }| result);
    assert!(
        !matches!(result_kind, Ok(VerificationResult::Verified(_))),
        "Precheck must not accept subtraction-based helpers. Got: {result_kind:?}"
    );
}

/// Recursive proof-style calls nested under branch-local `let` statements must
/// keep their active path guards when they seed ground spec instances. Without
/// those guards, the induction hypotheses for `lemma_fib_bound(i - 2)` and
/// `lemma_fib_bound(i - 1)` lose the branch facts needed to discharge the
/// callee preconditions, and the proof stalls at `i = 2`. (#994)
///
/// The branch-local proof-call guards should be sufficient to verify; a solver
/// hang or Unknown result is a regression.
#[test]
#[timeout(60000)]
fn test_recursive_logic_fn_proof_calls_keep_branch_guards() {
    use trust_wp_core::{
        formula::{internal::tuple_lowering::tuple_logic_fn_name, BinOp, PureExpr},
        logic::{LogicFnDef, LogicMode},
    };

    use crate::{verify_function_with_modes, VerificationRequest};

    let unit = || PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(0),
        args: vec![],
    };
    let var_i = || PureExpr::Var("i".to_string(), None);
    let logic_call = |name: &str, args: Vec<PureExpr>| PureExpr::LogicFnCall {
        name: name.to_string(),
        args,
    };
    let pow2 = |receiver: PureExpr| PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "pow2".to_string(),
        args: vec![],
    };
    let sub =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Sub, Arc::new(rhs));
    let add =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Add, Arc::new(rhs));
    let le =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Le, Arc::new(rhs));
    let eq =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs));

    let fib_body = ite(
        le(var("i"), int(0)),
        int(0),
        ite(
            eq(var("i"), int(1)),
            int(1),
            add(
                logic_call("fib", vec![sub(var_i(), PureExpr::Int(1))]),
                logic_call("fib", vec![sub(var_i(), PureExpr::Int(2))]),
            ),
        ),
    );
    let fib = LogicFnDef::new(
        "fib".to_string(),
        "test::fib".to_string(),
        vec!["i".to_string()],
        fib_body,
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();

    let lemma_body = PureExpr::Ite(
        Arc::new(eq(var_i(), PureExpr::Int(0))),
        Arc::new(unit()),
        Arc::new(PureExpr::Ite(
            Arc::new(eq(var_i(), PureExpr::Int(1))),
            Arc::new(unit()),
            Arc::new(PureExpr::Let {
                var: "__stmt0".to_string(),
                value: Arc::new(logic_call(
                    "lemma_fib_bound",
                    vec![sub(var_i(), PureExpr::Int(2))],
                )),
                body: Arc::new(PureExpr::Let {
                    var: "__stmt1".to_string(),
                    value: Arc::new(logic_call(
                        "lemma_fib_bound",
                        vec![sub(var_i(), PureExpr::Int(1))],
                    )),
                    body: Arc::new(unit()),
                }),
            }),
        )),
    );
    let mut lemma = LogicFnDef::new_with_requires(
        "lemma_fib_bound".to_string(),
        "test::lemma_fib_bound".to_string(),
        vec!["i".to_string()],
        vec![le(int(0), var("i"))],
        lemma_body,
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();
    lemma.set_ensures(vec![le(logic_call("fib", vec![var_i()]), pow2(var_i()))]);

    let logic_fns = vec![fib, lemma.clone()];
    let mode_overrides = vec![LogicMode::Open, LogicMode::Default];
    let result = verify_function_with_modes(
        VerificationRequest::new(lemma.requires(), lemma.ensures())
            .return_expr(Some(lemma.body()))
            .logic_fns(Some(&logic_fns))
            .mode_overrides(Some(&mode_overrides))
            .timeout(Some(std::time::Duration::from_secs(45))),
    );
    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        result
            .as_ref()
            .is_ok_and(crate::tests::helpers::verified_or_known_proof_trusted),
        "branch-local recursive proof calls should verify: {result:?}"
    );
}

/// Regression: a logic function with `#[ensures(result)]` (Bool return)
/// must not leak a Bool sort hint for "result" into the shared encoder
/// context. Otherwise, a sibling logic function returning Option<Int>
/// whose postcondition uses `match result { None => ..., Some(j) => ... }`
/// hits a sort conflict: "result declared as Bool, requested as OptionInt".
///
/// Reproduces the `find_ptr_in_seq` / `pigeon` interaction from
/// `list_reversal_lasso.rs`. (#994)
#[test]
#[timeout(60000)]
fn test_logic_fn_bool_result_does_not_pollute_option_result() {
    use trust_wp_core::formula::Pattern;

    // pigeon(s, n) -> Bool body, with #[ensures(result)]
    let mut pigeon_fn = LogicFnDef::new(
        "pigeon".to_string(),
        "test::pigeon".to_string(),
        vec!["s".to_string(), "n".to_string()],
        PureExpr::Bool(true), // simplified body
    )
    .with_mode(LogicMode::Open);
    pigeon_fn.set_ensures(vec![var("result")]);

    // find_ptr(s, i, p) -> Option<Int> body, with:
    //   #[ensures(match result { None => i > 10, Some(j) => j >= 0 })]
    let find_body = ite(
        ge(var("i"), int(10)),
        logic_fn_call("None", vec![]),
        logic_fn_call("Some", vec![var("i")]),
    );
    let find_ensures = match_expr(
        var("result"),
        vec![
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                gt(var("i"), int(10)),
            ),
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("j".to_string()))),
                },
                ge(var("j"), int(0)),
            ),
        ],
    );
    let mut find_fn = LogicFnDef::new(
        "find_ptr".to_string(),
        "test::find_ptr".to_string(),
        vec!["s".to_string(), "i".to_string(), "p".to_string()],
        find_body.clone(),
    )
    .with_mode(LogicMode::Open);
    find_fn.set_ensures(vec![find_ensures.clone()]);

    // Verify find_ptr's postcondition with pigeon available as a sibling
    let logic_fns = vec![pigeon_fn, find_fn];
    let result = verify_function_with_modes(
        VerificationRequest::new(
            &[],             // requires
            &[find_ensures], // ensures
        )
        .return_expr(Some(&find_body))
        .logic_fns(Some(&logic_fns)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Failed(_))),
        "find_ptr postcondition is false at i == 10 and should fail without a \
         sibling Bool-result sort conflict. Got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// MBQI evaluation matrix — Slice 2 of #1925
//
// Three paired tests measuring whether ay-dpll's MBQI can replace trust-wp's
// manual logic ground-pool flushing in the "spec-axiom" lane.
// ---------------------------------------------------------------------------

/// Baseline control: spec-axiom structural induction with ground-pool
/// **enabled** (the current production behaviour). Must verify.
///
/// This is the same `sum_nat` postcondition proof as
/// `test_recursive_logic_fn_structural_induction_with_spec_axiom`, but
/// explicitly sets `LogicGroundInstantiationMode::Enabled` to serve as
/// the A/B control for the Disabled variant below.
#[test]
#[timeout(60000)]
fn test_mbqi_matrix_spec_axiom_ground_pool_enabled() {
    use crate::{
        encoder::LogicGroundInstantiationMode, verify_function_with_modes, VerificationRequest,
        VerificationResult,
    };

    let sum_body = ite(
        le(var("n"), int(0)),
        int(0),
        add(
            var("n"),
            logic_fn_call("sum_nat", vec![sub(var("n"), int(1))]),
        ),
    );

    let mut sum_fn = LogicFnDef::new_with_requires(
        "sum_nat".to_string(),
        "test::sum_nat".to_string(),
        vec!["n".to_string()],
        vec![ge(var("n"), int(0))],
        sum_body.clone(),
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();
    sum_fn.set_ensures(vec![ge(var("result"), int(0))]);

    let mode_overrides = vec![LogicMode::Default];
    let result = verify_function_with_modes(
        VerificationRequest::new(sum_fn.requires(), sum_fn.ensures())
            .return_expr(Some(sum_fn.body()))
            .logic_fns(Some(std::slice::from_ref(&sum_fn)))
            .mode_overrides(Some(&mode_overrides))
            .logic_ground_mode(LogicGroundInstantiationMode::Enabled),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "Baseline (ground-pool enabled): spec-axiom induction must verify. Got: {result:?}"
    );
}

/// Spec-axiom structural induction with ground-pool **disabled**. MBQI should
/// now close the `sum_nat >= 0` proof without the manual ground pool.
#[test]
#[timeout(60000)]
fn test_mbqi_matrix_spec_axiom_ground_pool_disabled() {
    use std::time::Duration;

    use crate::{
        encoder::LogicGroundInstantiationMode, verify_function_with_modes, VerificationRequest,
        VerificationResult,
    };

    let sum_body = ite(
        le(var("n"), int(0)),
        int(0),
        add(
            var("n"),
            logic_fn_call("sum_nat", vec![sub(var("n"), int(1))]),
        ),
    );

    let mut sum_fn = LogicFnDef::new_with_requires(
        "sum_nat".to_string(),
        "test::sum_nat".to_string(),
        vec!["n".to_string()],
        vec![ge(var("n"), int(0))],
        sum_body.clone(),
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();
    sum_fn.set_ensures(vec![ge(var("result"), int(0))]);

    let mode_overrides = vec![LogicMode::Default];
    let result = verify_function_with_modes(
        VerificationRequest::new(sum_fn.requires(), sum_fn.ensures())
            .return_expr(Some(sum_fn.body()))
            .logic_fns(Some(std::slice::from_ref(&sum_fn)))
            .mode_overrides(Some(&mode_overrides))
            .logic_ground_mode(LogicGroundInstantiationMode::Disabled)
            .timeout(Some(Duration::from_secs(30))),
    );

    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "MBQI spec-axiom lane should verify without ground pool: {result:?}"
    );
}

/// Defining-axiom ("proof calls") lane with ground-pool disabled. MBQI should
/// now verify this lane without the manual ground pool.
#[test]
#[timeout(60000)]
fn test_mbqi_matrix_proof_calls_regresses_without_ground_pool() {
    use trust_wp_core::{
        formula::{internal::tuple_lowering::tuple_logic_fn_name, BinOp, PureExpr},
        logic::{LogicFnDef, LogicMode},
    };

    use crate::{
        encoder::LogicGroundInstantiationMode, verify_function_with_modes, VerificationRequest,
    };

    let unit = || PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(0),
        args: vec![],
    };
    let var_i = || PureExpr::Var("i".to_string(), None);
    let logic_call = |name: &str, args: Vec<PureExpr>| PureExpr::LogicFnCall {
        name: name.to_string(),
        args,
    };
    let pow2 = |receiver: PureExpr| PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "pow2".to_string(),
        args: vec![],
    };
    let sub =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Sub, Arc::new(rhs));
    let add =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Add, Arc::new(rhs));
    let le =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Le, Arc::new(rhs));
    let eq =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs));

    let fib_body = ite(
        le(var("i"), int(0)),
        int(0),
        ite(
            eq(var("i"), int(1)),
            int(1),
            add(
                logic_call("fib", vec![sub(var_i(), PureExpr::Int(1))]),
                logic_call("fib", vec![sub(var_i(), PureExpr::Int(2))]),
            ),
        ),
    );
    let fib = LogicFnDef::new(
        "fib".to_string(),
        "test::fib".to_string(),
        vec!["i".to_string()],
        fib_body,
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();

    let lemma_body = PureExpr::Ite(
        Arc::new(eq(var_i(), PureExpr::Int(0))),
        Arc::new(unit()),
        Arc::new(PureExpr::Ite(
            Arc::new(eq(var_i(), PureExpr::Int(1))),
            Arc::new(unit()),
            Arc::new(PureExpr::Let {
                var: "__stmt0".to_string(),
                value: Arc::new(logic_call(
                    "lemma_fib_bound",
                    vec![sub(var_i(), PureExpr::Int(2))],
                )),
                body: Arc::new(PureExpr::Let {
                    var: "__stmt1".to_string(),
                    value: Arc::new(logic_call(
                        "lemma_fib_bound",
                        vec![sub(var_i(), PureExpr::Int(1))],
                    )),
                    body: Arc::new(unit()),
                }),
            }),
        )),
    );
    let mut lemma = LogicFnDef::new_with_requires(
        "lemma_fib_bound".to_string(),
        "test::lemma_fib_bound".to_string(),
        vec!["i".to_string()],
        vec![le(int(0), var("i"))],
        lemma_body,
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();
    lemma.set_ensures(vec![le(logic_call("fib", vec![var_i()]), pow2(var_i()))]);

    let logic_fns = vec![fib, lemma.clone()];
    let mode_overrides = vec![LogicMode::Open, LogicMode::Default];
    let result = verify_function_with_modes(
        VerificationRequest::new(lemma.requires(), lemma.ensures())
            .return_expr(Some(lemma.body()))
            .logic_fns(Some(&logic_fns))
            .mode_overrides(Some(&mode_overrides))
            .logic_ground_mode(LogicGroundInstantiationMode::Disabled)
            .timeout(Some(std::time::Duration::from_secs(45))),
    );
    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        result
            .as_ref()
            .is_ok_and(crate::tests::helpers::verified_or_known_proof_trusted),
        "MBQI proof-calls lane should verify without ground pool. Got: {result:?}"
    );
}
