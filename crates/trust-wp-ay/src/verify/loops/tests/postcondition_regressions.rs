// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{sync::Arc, time::Duration};

use ntest::timeout;
use trust_wp_core::logic::LogicFnDef;

use super::{
    super::postcondition::{
        equality_congruence_consequence, list_index_cursor_postcondition_follows_directly,
        list_reversal_list_postcondition_follows_directly,
        seq_reverse_equality_congruence_has_empty_witness,
    },
    *,
};

#[test]
fn equality_congruence_materializes_nested_sequence_alias() {
    let result = view(var_with_sort("result", ExprSort::Seq));
    let produced = view(var_with_sort("produced", ExprSort::Seq));
    let input = view(var_with_sort("input", ExprSort::Seq));
    let reverse = |value: PureExpr| method_call(value, "reverse", vec![]);
    let invariants = vec![eq(result.clone(), reverse(produced.clone()))];
    let completion = vec![eq(produced, input.clone())];
    let target = eq(result, reverse(input));

    assert_eq!(
        equality_congruence_consequence(&target, &invariants, &completion),
        Some(target),
        "a nested pure-function application must preserve an asserted equality"
    );
}

#[test]
fn sequence_reverse_empty_witness_accepts_normalized_sequence_variables() {
    let result = PureExpr::Var("result".to_string(), Some(ExprSort::Seq));
    let produced = PureExpr::Var("produced".to_string(), Some(ExprSort::Seq));
    let input = PureExpr::Var("input".to_string(), Some(ExprSort::Seq));
    let reverse = |value: PureExpr| method_call(value, "reverse", vec![]);
    let invariants = vec![eq(result.clone(), reverse(produced.clone()))];
    let completion = vec![eq(produced, input.clone())];
    let target = eq(result, reverse(input));

    assert!(
        seq_reverse_equality_congruence_has_empty_witness(&target, &invariants, &completion,),
        "loop normalization removes Seq views; the explicit empty-sequence witness \
         must recognize the resulting typed Seq variables"
    );
}

#[test]
fn equality_congruence_rejects_noncongruent_target() {
    let result = view(var_with_sort("result", ExprSort::Seq));
    let produced = view(var_with_sort("produced", ExprSort::Seq));
    let input = view(var_with_sort("input", ExprSort::Seq));
    let invariants = vec![eq(
        result.clone(),
        method_call(produced.clone(), "reverse", vec![]),
    )];
    let completion = vec![eq(produced, input.clone())];
    let target = eq(result, method_call(input, "push_back", vec![int(1)]));

    assert!(
        equality_congruence_consequence(&target, &invariants, &completion).is_none(),
        "an alias cannot change the surrounding function symbol"
    );
}

#[test]
fn equality_congruence_does_not_rewrite_current_alias_below_old() {
    let invariants = vec![eq(PureExpr::Old(Arc::new(var("x"))), var("entry_value"))];
    let current_alias = vec![eq(var("x"), var("z"))];
    let target = eq(PureExpr::Old(Arc::new(var("z"))), var("entry_value"));

    assert!(
        equality_congruence_consequence(&target, &invariants, &current_alias).is_none(),
        "current-state equality must not rewrite an entry-state old operand"
    );
}

/// Requires referencing loop-modified variables must NOT be asserted in the
/// postcondition VC. Without this filter, `requires(x == 5)` would force
/// the post-loop value of `x` to 5, creating unsound proofs. (#904)
///
/// This test uses a simple VC: ensures(x == 5), modified_vars = `["x"]`,
/// requires = `[x == 5, n >= 0]`. Without filtering, x == 5 leaks in and
/// the postcondition trivially passes. With filtering, x is unconstrained
/// and the postcondition fails.
#[test]
#[timeout(30000)]
fn verify_postcondition_filters_requires_on_modified_vars() {
    let invariants = vec![PureExpr::Bool(true)];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    )];
    let requires = vec![
        // n >= 0 — unmodified, should be asserted
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("n".to_string(), None)),
            BinOp::Ge,
            Arc::new(PureExpr::Int(0)),
        ),
        // x == 5 — modified var, must NOT be asserted in postcondition
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(5)),
        ),
    ];
    let modified_vars: Vec<&str> = vec!["x"];

    let result = verify_postcondition(
        &invariants,
        None, // no loop condition — simplest possible VC
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &requires, &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("postcondition VC should encode without error");

    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "Postcondition should fail: invariant is trivially true, x is unconstrained. \
         If this passes, requires on modified var 'x' leaked into postcondition VC. \
         Got {result:?}"
    );
}

/// Requires on unmodified parameters ARE asserted in the postcondition VC.
/// This is the dual of the filter test above: `requires(n == 5)` where `n`
/// is NOT modified should allow proving `ensures(n == 5)`.
#[test]
#[timeout(30000)]
fn verify_postcondition_keeps_requires_on_unmodified_vars() {
    let invariants = vec![PureExpr::Bool(true)];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    )];
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    )];
    // Only "x" is modified; "n" is unmodified
    let modified_vars: Vec<&str> = vec!["x"];

    let result = verify_postcondition(
        &invariants,
        None,
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &requires, &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("postcondition VC should encode without error");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Postcondition should pass: requires(n == 5) on unmodified 'n' \
         should be asserted, making ensures(n == 5) trivially true. Got {result:?}"
    );
}

/// The loop postcondition path must recheck the full asserted live base, not
/// just the invariants-only disposable probe. Here the invariant is satisfiable,
/// but unmodified `requires` plus the frame equality contradict each other. (#2622)
#[test]
#[timeout(30000)]
fn postcondition_full_base_contradiction_returns_vacuous_unknown() {
    let invariants = vec![PureExpr::Bool(true)];
    let ensures = vec![PureExpr::Bool(true)];
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(0)),
    )];
    let pre_loop_assignments: HashMap<String, NamedBindingValue> = [(
        "n".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(1)),
    )]
    .into_iter()
    .collect();

    let result = verify_postcondition(
        &invariants,
        None,
        false,
        &[],
        postcondition_inputs(&ensures, None, &pre_loop_assignments, &requires, &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("postcondition VC should encode without error");

    assert!(
        matches!(
            result,
            VerificationResult::Unknown(UnknownReason::SolverMessage(ref msg))
                if msg.contains(crate::verify::solver_tail::VACUOUS_PROOF_MESSAGE)
        ),
        "full-base contradiction should return Unknown(vacuous), got {result:?}"
    );
}

/// Direct `verify_postcondition` negative test: weak invariant should fail.
///
/// This is the lightweight replacement for `test_loop_wrong_invariant_fails`
/// which times out through `verify_loop_invariant_positional`. By calling
/// `verify_postcondition` directly with a single sub-VC, we avoid the
/// multi-VC overhead and solver timeouts from #1466. (#1466, #904)
#[test]
#[timeout(20000)]
fn test_postcondition_rejects_weak_invariant_direct() {
    // Models: loop with modified `i`, invariant `i >= 0` only (too weak),
    // ensures `i == n` where n is unmodified.
    // Without `i <= n`, the postcondition should fail: when the loop exits
    // (¬(i < n) → i >= n), we only know i >= 0 ∧ i >= n, not i == n.
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    )];
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let cond = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let modified_vars: Vec<&str> = vec!["i"];

    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };
    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &requires, &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("postcondition VC should encode without error");

    assert!(
        matches!(&result, VerificationResult::Failed(_)),
        "Postcondition should fail: invariant i >= 0 is too weak to prove i == n. \
         If this passes, postcondition VC is unsound. Got {result:?}"
    );
}

fn list_wrapper_def_for_postcondition_test() -> LogicFnDef {
    LogicFnDef::new(
        "list".to_string(),
        "Memory::list".to_string(),
        vec!["self".to_string(), "first".to_string(), "s".to_string()],
        logic_fn_call(
            "Memory::list_seg",
            vec![
                var("self"),
                var("first"),
                var("s"),
                var("NULL"),
                int(0),
                method_call(var("s"), "len", vec![]),
            ],
        ),
    )
}

fn list_reversal_list_postcondition_fixture() -> (Vec<PureExpr>, PureExpr, PureExpr, Vec<LogicFnDef>)
{
    let mem = var("self");
    let l = var("l");
    let r = var("r");
    let n = var("n");
    let null = var("NULL");
    let s = var_with_sort("s", ExprSort::Seq);
    let s_len = method_call(s.clone(), "len", vec![]);
    let s_reverse = method_call(s.clone(), "reverse", vec![]);

    let invariants = vec![
        logic_fn_call(
            "Memory::list_seg",
            vec![
                mem.clone(),
                l.clone(),
                s.clone(),
                null.clone(),
                n.clone(),
                s_len.clone(),
            ],
        ),
        logic_fn_call(
            "Memory::list_seg",
            vec![
                mem,
                r.clone(),
                s_reverse.clone(),
                null.clone(),
                sub(s_len, n),
                method_call(s.clone(), "len", vec![]),
            ],
        ),
    ];
    let condition = ne(l, null);
    let ensure = logic_fn_call("Memory::list", vec![final_expr(var("self")), r, s_reverse]);
    (
        invariants,
        condition,
        ensure,
        vec![list_wrapper_def_for_postcondition_test()],
    )
}

#[test]
#[timeout(30000)]
fn list_reversal_list_postcondition_direct_check_accepts_exit_shape() {
    let (invariants, condition, ensure, logic_fns) = list_reversal_list_postcondition_fixture();

    assert!(
        list_reversal_list_postcondition_follows_directly(
            &ensure,
            &invariants,
            Some(&condition),
            false,
            Some(&logic_fns),
        ),
        "exit l == NULL plus remaining/reversed list_seg invariants should imply list postcondition"
    );
}

#[test]
#[timeout(30000)]
fn list_reversal_list_postcondition_direct_check_accepts_view_sequence_alias() {
    let mem = var("self");
    let l = var("l");
    let r = var("r");
    let n = var("n");
    let null = var("NULL");
    let s = var_with_sort("s", ExprSort::Seq);
    let s_view = view(s.clone());
    let s_len = method_call(s.clone(), "len", vec![]);
    let s_view_reverse = method_call(s_view.clone(), "reverse", vec![]);

    let invariants = vec![
        logic_fn_call(
            "Memory::list_seg",
            vec![
                mem.clone(),
                l.clone(),
                s,
                null.clone(),
                n.clone(),
                s_len.clone(),
            ],
        ),
        logic_fn_call(
            "Memory::list_seg",
            vec![
                mem,
                r.clone(),
                s_view_reverse.clone(),
                null.clone(),
                sub(s_len.clone(), n),
                s_len,
            ],
        ),
    ];
    let condition = ne(l, null);
    let ensure = logic_fn_call(
        "Memory::list",
        vec![final_expr(var("self")), r, s_view_reverse],
    );
    let logic_fns = vec![list_wrapper_def_for_postcondition_test()];

    assert!(
        list_reversal_list_postcondition_follows_directly(
            &ensure,
            &invariants,
            Some(&condition),
            false,
            Some(&logic_fns),
        ),
        "list postcondition should match finite list_seg facts across s/s@ aliasing"
    );
}

#[test]
#[timeout(30000)]
fn list_reversal_list_postcondition_direct_check_accepts_method_replay_shape() {
    let mem = var("self");
    let l = var("l");
    let r = var("r");
    let n = var("n");
    let null = var("NULL");
    let u64_max = var("u64::MAX");
    let s = var_with_sort("s", ExprSort::Seq);
    let s_view = view(s);
    let s_view_len = method_call(s_view.clone(), "len", vec![]);
    let s_view_reverse = method_call(s_view.clone(), "reverse", vec![]);

    let list_def = LogicFnDef::new(
        "list".to_string(),
        "Memory::list".to_string(),
        vec!["self".to_string(), "first".to_string(), "s".to_string()],
        method_call(
            var("self"),
            "Memory::list_seg",
            vec![
                var("first"),
                var("s"),
                var("u64::MAX"),
                int(0),
                method_call(var("s"), "len", vec![]),
            ],
        ),
    );

    let invariants = vec![
        method_call(
            mem.clone(),
            "Memory::list_seg",
            vec![
                l.clone(),
                s_view.clone(),
                u64_max,
                n.clone(),
                s_view_len.clone(),
            ],
        ),
        method_call(
            mem.clone(),
            "Memory::list_seg",
            vec![
                r.clone(),
                s_view_reverse.clone(),
                null.clone(),
                sub(s_view_len.clone(), n),
                s_view_len,
            ],
        ),
    ];
    let condition = ne(l, null);
    let ensure = method_call(final_expr(mem), "Memory::list", vec![r, s_view_reverse]);

    assert!(
        list_reversal_list_postcondition_follows_directly(
            &ensure,
            &invariants,
            Some(&condition),
            false,
            Some(&[list_def]),
        ),
        "method-call list/list_seg replay shape should imply list postcondition"
    );
}

#[test]
#[timeout(30000)]
fn list_reversal_list_postcondition_direct_check_rejects_missing_remaining_segment() {
    let (mut invariants, condition, ensure, logic_fns) = list_reversal_list_postcondition_fixture();
    invariants.remove(0);

    assert!(
        !list_reversal_list_postcondition_follows_directly(
            &ensure,
            &invariants,
            Some(&condition),
            false,
            Some(&logic_fns),
        ),
        "the direct check must require the remaining list_seg invariant"
    );
}

#[test]
#[timeout(30000)]
fn list_reversal_list_postcondition_direct_check_rejects_missing_exit_condition() {
    let (invariants, _condition, ensure, logic_fns) = list_reversal_list_postcondition_fixture();

    assert!(
        !list_reversal_list_postcondition_follows_directly(
            &ensure,
            &invariants,
            None,
            false,
            Some(&logic_fns),
        ),
        "the direct check must require the loop exit condition"
    );
}

#[test]
#[timeout(30000)]
fn list_reversal_list_postcondition_direct_check_rejects_suffix_only_wrapper_match() {
    let (invariants, condition, ensure, mut logic_fns) = list_reversal_list_postcondition_fixture();
    logic_fns[0] = LogicFnDef::new(
        "list".to_string(),
        "OtherMemory::list".to_string(),
        logic_fns[0].params().to_vec(),
        logic_fns[0].body().clone(),
    );

    assert!(
        !list_reversal_list_postcondition_follows_directly(
            &ensure,
            &invariants,
            Some(&condition),
            false,
            Some(&logic_fns),
        ),
        "the direct check must not bind a wrapper solely because the call name shares a suffix"
    );
}

/// Reduced `list_index_mut`-style postcondition slice.
///
/// The full compat test times out through the end-to-end harness. This direct
/// loop-postcondition VC keeps the hard quantified shape:
/// all indices except the moving cursor are preserved, and the exit condition
/// (`!(ix > 0)`) must specialize the quantified invariant from `i != ix` to
/// `i != 0`.
///
/// Re: #994 (`list_index_mut` timeout-heavy residual)
#[test]
#[timeout(60000)]
fn test_postcondition_list_index_mut_cursor_quantifier_reduction() {
    use trust_wp_core::formula::ExprSort;

    let list_ref = var_with_sort("l", ExprSort::Ref(Box::new(ExprSort::Seq)));
    let current_view = view(deref(list_ref.clone()));
    let final_view = view(final_expr(list_ref));

    let current_len = method_call(current_view.clone(), "len", vec![]);
    let final_len = method_call(final_view.clone(), "len", vec![]);

    let quantified_invariant = forall(
        "i",
        implies(
            and(
                and(ge(var("i"), int(0)), lt(var("i"), current_len.clone())),
                ne(var("i"), var("ix")),
            ),
            eq(
                method_call(final_view.clone(), "index_logic", vec![var("i")]),
                method_call(current_view.clone(), "index_logic", vec![var("i")]),
            ),
        ),
    );

    let invariants = vec![
        ge(var("ix"), int(0)),
        lt(var("ix"), current_len.clone()),
        eq(final_len.clone(), current_len.clone()),
        quantified_invariant,
    ];

    let ensures = vec![forall(
        "i",
        implies(
            and(
                and(ge(var("i"), int(0)), lt(var("i"), final_len)),
                ne(var("i"), int(0)),
            ),
            eq(
                method_call(final_view, "index_logic", vec![var("i")]),
                method_call(current_view, "index_logic", vec![var("i")]),
            ),
        ),
    )];

    let condition = gt(var("ix"), int(0));
    let modified_vars: Vec<&str> = vec!["ix", "l"];
    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(45)),
        ..LoopEncoderConfig::default()
    };

    assert!(
        list_index_cursor_postcondition_follows_directly(
            &ensures[0],
            &invariants,
            Some(&condition),
            false,
        ),
        "the exact cursor-at-zero specialization should be recognized"
    );
    let mut contradictory_exit = invariants.clone();
    contradictory_exit[0] = ge(var("ix"), int(1));
    assert!(
        !list_index_cursor_postcondition_follows_directly(
            &ensures[0],
            &contradictory_exit,
            Some(&condition),
            false,
        ),
        "the structural lane must reject a premise set whose exit is contradictory"
    );
    let mut impossible_quantifier = invariants.clone();
    impossible_quantifier[3] = forall("i", PureExpr::Bool(false));
    let impossible_target = forall("i", PureExpr::Bool(false));
    assert!(
        !list_index_cursor_postcondition_follows_directly(
            &impossible_target,
            &impossible_quantifier,
            Some(&condition),
            false,
        ),
        "the structural lane must require the exact cursor-excluding range guard; \
         an arbitrary contradictory forall has no one-element witness"
    );

    let result = verify_postcondition(
        &invariants,
        Some(&condition),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &HashMap::new(), &[], &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("reduced list_index_mut postcondition VC should encode");

    assert!(
        matches!(&result, VerificationResult::Verified(_)),
        "Reduced list_index_mut postcondition should verify. Got {result:?}"
    );
}

/// Reduced `list_index_mut`-style preservation: quantified invariant with
/// shifting exclusion bound, PLUS a point invariant covering the excluded
/// index, making the whole sequence agree.
///
/// The invariants say:
///   (1) forall i. 0 <= i < len(s) && i != ix ==> index_logic(s_final, i) == index_logic(s, i)
///   (2) index_logic(s_final, ix) == index_logic(s, ix)  [point invariant]
///
/// Together these mean the entire sequence agrees. The body effect is
/// `ix → ix - 1`. Preservation of the quantified invariant is provable
/// because the newly included index (ix, no longer excluded since ix != ix-1)
/// is covered by the point invariant. Preservation of the point invariant
/// is provable because ix-1 was already covered by the quantified invariant.
///
/// This models the core pattern from `list_index_mut` where both current
/// and final views narrow together, preserving agreement at all indices.
///
/// Re: #994 (`list_index_mut` timeout-heavy residual)
#[test]
#[timeout(90000)]
fn test_preservation_quantified_shifting_exclusion() {
    use trust_wp_core::formula::ExprSort;

    let s = var_with_sort("s", ExprSort::Seq);
    let s_final = var_with_sort("s_final", ExprSort::Seq);
    let s_len = method_call(s.clone(), "len", vec![]);

    // Quantified invariant: all indices except ix agree between s and s_final
    let quantified_inv = forall(
        "i",
        implies(
            and(
                and(ge(var("i"), int(0)), lt(var("i"), s_len.clone())),
                ne(var("i"), var("ix")),
            ),
            eq(
                method_call(s_final.clone(), "index_logic", vec![var("i")]),
                method_call(s.clone(), "index_logic", vec![var("i")]),
            ),
        ),
    );

    // Point invariant: the excluded index ALSO agrees
    let point_inv = eq(
        method_call(s_final.clone(), "index_logic", vec![var("ix")]),
        method_call(s.clone(), "index_logic", vec![var("ix")]),
    );

    let invariants = vec![
        ge(var("ix"), int(0)),
        lt(var("ix"), s_len.clone()),
        ge(s_len, int(1)),
        point_inv,
        quantified_inv,
    ];

    let loop_condition = gt(var("ix"), int(0));
    let modified_vars: Vec<&str> = vec!["ix"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "ix".to_string(),
        PureExpr::BinOp(Arc::new(var("ix")), BinOp::Sub, Arc::new(int(1))),
    );

    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(45)),
        ..LoopEncoderConfig::default()
    };

    let result = verify_preservation(
        &invariants,
        Some(&loop_condition),
        &modified_vars,
        &body_effect,
        &config,
    )
    .expect("shifting-exclusion preservation VC should encode");

    // This SHOULD verify: the quantified invariant is preserved because the
    // point invariant covers the newly included index (ix), and the primed
    // point invariant (at ix-1) is covered by the old quantified invariant
    // (since ix-1 != ix when ix > 0).
    assert!(
        matches!(&result, VerificationResult::Verified(_)),
        "Shifting-exclusion preservation should verify: point invariant covers \
         the newly included index ix. Got {result:?}"
    );
}

/// Recursive logic function unfolding in preservation: ay-dpll single-round
/// E-matching limitation.
///
/// Models a simple recursive `sum(n)` function and a loop that counts up
/// while maintaining `sum(i) == acc`. The body effect increments `i` and
/// adds `i` to `acc`. Preservation requires ONE unfolding of `sum`:
///   sum(i+1) = sum(i) + (i+1)   [by definition]
///
/// With the current ay-dpll single-round E-matching, the definition axiom
/// for `sum` fires on existing terms but may not fire on newly-created
/// terms from priming. This test detects whether the solver can unfold
/// recursive functions during preservation.
///
/// Re: #994 (`list_index_mut` recursive function bottleneck)
#[test]
#[timeout(60000)]
fn test_preservation_recursive_logic_fn_one_unfolding() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // Define: sum(n) = if n <= 0 then 0 else sum(n-1) + n
    let sum_body = PureExpr::Ite(
        Arc::new(PureExpr::BinOp(
            Arc::new(var("n")),
            BinOp::Le,
            Arc::new(int(0)),
        )),
        Arc::new(int(0)),
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: "sum".to_string(),
                args: vec![PureExpr::BinOp(
                    Arc::new(var("n")),
                    BinOp::Sub,
                    Arc::new(int(1)),
                )],
            }),
            BinOp::Add,
            Arc::new(var("n")),
        )),
    );
    let mut sum_def = LogicFnDef::new(
        "sum".to_string(),
        "crate::sum".to_string(),
        vec!["n".to_string()],
        sum_body,
    );
    sum_def.set_is_recursive(true);
    sum_def.set_mode(LogicMode::Open);

    // Invariants: i >= 0, i <= bound, acc == sum(i)
    // Note: `i <= bound` (not `i < bound`) is the correct invariant because
    // after `i += 1` we only know `i_prime <= bound`, not `i_prime < bound`.
    let invariants = vec![
        ge(var("i"), int(0)),
        le(var("i"), var("bound")),
        eq(
            var("acc"),
            PureExpr::LogicFnCall {
                name: "sum".to_string(),
                args: vec![var("i")],
            },
        ),
    ];

    // Loop condition: i < bound
    let loop_condition = lt(var("i"), var("bound"));

    // Body effects: i → i + 1, acc → acc + (i + 1)
    let modified_vars: Vec<&str> = vec!["i", "acc"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(Arc::new(var("i")), BinOp::Add, Arc::new(int(1))),
    );
    body_effect.insert(
        "acc".to_string(),
        PureExpr::BinOp(
            Arc::new(var("acc")),
            BinOp::Add,
            Arc::new(PureExpr::BinOp(
                Arc::new(var("i")),
                BinOp::Add,
                Arc::new(int(1)),
            )),
        ),
    );

    let logic_fns = [sum_def];
    let config = LoopEncoderConfig {
        logic_fns: Some(&logic_fns),
        mode_overrides: Some(&[LogicMode::Open]),
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    };

    let result = verify_preservation(
        &invariants,
        Some(&loop_condition),
        &modified_vars,
        &body_effect,
        &config,
    )
    .expect("recursive sum preservation VC should encode");

    // Preservation requires: acc_prime == sum(i_prime)
    //   acc_prime = acc + (i+1) = sum(i) + (i+1) = sum(i+1) = sum(i_prime)
    // This needs ONE unfolding of sum(i+1) = sum(i) + (i+1).
    // With the one-step unfolding bridge from assert_recursive_fn_unfoldings,
    // ay has the ground fact `sum(i_prime) = ite(i_prime <= 0, 0, sum(i) + i_prime)`
    // which is sufficient to prove preservation without relying on E-matching
    // to unfold the quantified definition axiom. (#994)
    assert!(
        matches!(&result, VerificationResult::Verified(_)),
        "Recursive sum preservation should verify. Got {result:?}"
    );
}

/// Same as above but with sum registered as opaque (Default mode).
/// The ground unfoldings from `assert_recursive_fn_unfoldings` should be
/// sufficient — no quantified defining axiom needed. If this passes but the
/// Open-mode variant doesn't, the problem is the E-matching flood. (#994)
#[test]
#[timeout(45000)]
fn test_preservation_recursive_logic_fn_opaque_mode() {
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    let sum_body = PureExpr::Ite(
        Arc::new(PureExpr::BinOp(
            Arc::new(var("n")),
            BinOp::Le,
            Arc::new(int(0)),
        )),
        Arc::new(int(0)),
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: "sum".to_string(),
                args: vec![PureExpr::BinOp(
                    Arc::new(var("n")),
                    BinOp::Sub,
                    Arc::new(int(1)),
                )],
            }),
            BinOp::Add,
            Arc::new(var("n")),
        )),
    );
    let mut sum_def = LogicFnDef::new(
        "sum".to_string(),
        "crate::sum".to_string(),
        vec!["n".to_string()],
        sum_body,
    );
    sum_def.set_is_recursive(true);
    // Default mode = opaque: no defining axiom, only ground unfoldings.
    sum_def.set_mode(LogicMode::Default);

    let invariants = vec![
        ge(var("i"), int(0)),
        le(var("i"), var("bound")),
        eq(
            var("acc"),
            PureExpr::LogicFnCall {
                name: "sum".to_string(),
                args: vec![var("i")],
            },
        ),
    ];

    let loop_condition = lt(var("i"), var("bound"));

    let modified_vars: Vec<&str> = vec!["i", "acc"];
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(Arc::new(var("i")), BinOp::Add, Arc::new(int(1))),
    );
    body_effect.insert(
        "acc".to_string(),
        PureExpr::BinOp(
            Arc::new(var("acc")),
            BinOp::Add,
            Arc::new(PureExpr::BinOp(
                Arc::new(var("i")),
                BinOp::Add,
                Arc::new(int(1)),
            )),
        ),
    );

    let logic_fns = [sum_def];
    let config = LoopEncoderConfig {
        logic_fns: Some(&logic_fns),
        // Default mode = opaque — no quantified defining axiom.
        mode_overrides: Some(&[LogicMode::Default]),
        timeout: Some(Duration::from_secs(10)),
        ..LoopEncoderConfig::default()
    };

    let result = verify_preservation(
        &invariants,
        Some(&loop_condition),
        &modified_vars,
        &body_effect,
        &config,
    )
    .expect("recursive sum preservation VC should encode");

    // With opaque mode, the defining axiom is suppressed. The ground
    // unfoldings from assert_recursive_fn_unfoldings should be sufficient
    // to prove preservation.
    assert!(
        matches!(&result, VerificationResult::Verified(_)),
        "Opaque sum with ground unfoldings should verify. Got {result:?}"
    );
}

/// Body-break postcondition priming: return_expr should use post-body values.
///
/// For `loop { i += 1; if i >= n { break } }; return i`, the postcondition
/// `result >= n` is provable because:
///   - body effect: i_prime = i + 1
///   - exit guard: NOT(i_prime < n) ⟹ i_prime >= n
///   - return value: i_prime (post-body)
///
/// Without #1399 fix, return_expr = Var("i") (unprimed, pre-body), making
/// `result >= n` only `i >= n`, which is unprovable given `i_prime >= n`.
/// (#1399)
#[test]
#[timeout(30000)]
fn test_body_break_postcondition_primes_return_expr() {
    // invariant: i >= 0
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    // loop condition (body-break): i < n
    let loop_condition = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    // ensures: result >= n
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    )];
    // return_expr: Var("i") — the variable returned after the loop
    let return_expr = PureExpr::Var("i".to_string(), None);
    let modified_vars: Vec<&str> = vec!["i"];
    // body effect: i → i + 1
    let mut body_effect = HashMap::new();
    body_effect.insert(
        "i".to_string(),
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("i".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );
    // requires: n > 0 (ensures at least one iteration)
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )];

    let result = verify_postcondition(
        &invariants,
        Some(&loop_condition),
        true, // condition_is_body_break
        &modified_vars,
        postcondition_inputs(
            &ensures,
            Some(&return_expr),
            &HashMap::new(),
            &requires,
            &[],
        ),
        effects(&body_effect, &HashMap::new(), &HashMap::new()),
        &LoopEncoderConfig::default(),
    )
    .expect("postcondition VC should encode without error");

    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "Body-break postcondition should verify: with i_prime = i+1 and \
         NOT(i_prime < n), result (= i_prime) >= n is provable. Got {result:?}"
    );
}

/// Loop initialization with an existential precondition containing
/// `postcondition_mut` must Skolemize rather than encode as ay existential.
/// ay-dpll cannot handle existential quantifiers — without Skolemization
/// the result is Unknown instead of Verified. (#1364)
#[test]
#[timeout(30000)]
fn verify_initialization_skolemizes_postcondition_mut_existential() {
    // Precondition: exists<f2> f.postcondition_mut(a, f2, result)
    // This is the pattern from closure specs — the existential binds
    // the post-call state of a mutable closure.
    let existential_req = PureExpr::Exists {
        var: "f2".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("f".to_string(), None)),
            method: "postcondition_mut".to_string(),
            args: vec![
                PureExpr::Var("a".to_string(), None),
                PureExpr::Var("f2".to_string(), None),
                PureExpr::Var("r".to_string(), None),
            ],
        }),
        triggers: vec![],
    };

    // Simple invariant: i >= 0
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];

    let mut pre_loop_assignments = HashMap::new();
    pre_loop_assignments.insert(
        "i".to_string(),
        NamedBindingValue::untyped(PureExpr::Int(0)),
    );

    let result = verify_initialization(
        &[existential_req],
        &invariants,
        &pre_loop_assignments,
        &[],
        &LoopEncoderConfig::default(),
    )
    .expect("initialization with postcondition_mut existential should encode");

    // With Skolemization: the existential becomes a fresh constant,
    // precondition is satisfiable, and i=0 >= 0 is trivially provable.
    // Without Skolemization: ay returns Unknown for existential quantifiers.
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "initialization should verify when postcondition_mut existential \
         is Skolemized (not Unknown). Got {result:?}"
    );
}
/// Regression test for #2158 Location 2: frame constraint must skip variables
/// whose value expression references modified vars.
///
/// Models: `let n = v.len(); while i < n { v.push(...); i += 1 }`
/// Variable `n` is not modified directly, but its pre-loop value `v.len()`
/// references `v` which IS modified. Without the value-expression check,
/// the postcondition VC gets an unsound frame constraint `n == v.len()`
/// (asserting post-loop `v.len()` equals pre-loop `v.len()`).
#[test]
#[timeout(30000)]
fn test_postcondition_frame_skips_value_referencing_modified_var() {
    use std::collections::HashMap;

    // Model: `n = v.len()` as pre-loop assignment, `v` is modified.
    // MethodCall { receiver: Var("v"), method: "len", args: [] } models `v.len()`.
    let pre_loop_assignments: HashMap<String, NamedBindingValue> = [(
        "n".to_string(),
        NamedBindingValue::untyped(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("v".to_string(), None)),
            method: "len".to_string(),
            args: vec![],
        }),
    )]
    .into_iter()
    .collect();

    let modified_vars: Vec<&str> = vec!["i", "v"];
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let cond = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    // Ensures: i == n (should be provable from invariant + exit condition)
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    )];
    let requires = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];

    let config = LoopEncoderConfig {
        timeout: Some(std::time::Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };
    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &pre_loop_assignments, &requires, &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    )
    .expect("postcondition VC should encode without error");

    // The key invariant: this should produce a real counterexample, not an
    // unsound Verified result
    // from the spurious frame constraint `n == v.len()`. With invariant
    // `i >= 0` + exit condition `¬(i < n)` + requires `n >= 0`, we can
    // prove `i >= n`. Combined with a proper loop invariant `i <= n`, we
    // get `i == n`. Without that upper-bound invariant, this should fail.
    //
    // Before the #2158 fix, the frame constraint `n == len(v)` was asserted
    // (unsound) which could affect the result. After the fix, `n` is left
    // unconstrained (its value expression references modified `v`), and
    // the VC correctly depends on the invariant strength.
    assert!(
        matches!(&result, VerificationResult::Failed(_)),
        "Without upper-bound invariant (i <= n), postcondition i == n should not be \
         provable. Got {result:?}"
    );
}
#[test]
#[timeout(30000)]
fn test_postcondition_rejects_residual_non_deref_old() {
    // Residual Old(Var("x")) in loop postcondition should produce an
    // EncodingError, not create a fresh unconstrained `old_x` variable (#2095).
    let invariants = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )];
    let ensures = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::Int),
        )))),
    )];
    let requires = vec![];
    let cond = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("x".to_string(), None)),
    );
    let modified_vars: Vec<&str> = vec!["i"];
    let pre_loop = HashMap::new();
    let config = LoopEncoderConfig {
        timeout: Some(Duration::from_secs(5)),
        ..LoopEncoderConfig::default()
    };
    let result = verify_postcondition(
        &invariants,
        Some(&cond),
        false,
        &modified_vars,
        postcondition_inputs(&ensures, None, &pre_loop, &requires, &[]),
        effects(&HashMap::new(), &HashMap::new(), &HashMap::new()),
        &config,
    );
    assert!(
        result.is_err(),
        "residual Old(Var(x)) should produce an EncodingError, not encode silently; got {result:?}"
    );
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("residual old"),
        "error should mention residual old: {err_msg}"
    );
}
