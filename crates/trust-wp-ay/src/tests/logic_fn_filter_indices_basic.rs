// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Basic index-returning behavior ---

#[test]
#[timeout(30000)]
fn empty_input_returns_empty() {
    let result = filter_logic_fn_indices_for_goal(&[], &names(&[]));
    assert!(result.is_empty());
}

#[test]
#[timeout(30000)]
fn empty_initial_names_returns_empty() {
    let fns = vec![make_fn("a", &[])];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&[]));
    assert!(result.is_empty());
}

#[test]
#[timeout(30000)]
fn single_function_returns_its_index() {
    let fns = vec![make_fn("a", &[]), make_fn("b", &[])];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["b"]));
    assert_eq!(result, vec![1], "should return index 1 for 'b'");
}

#[test]
#[timeout(30000)]
fn linear_chain_returns_all_indices_in_order() {
    let fns = vec![
        make_fn("a", &["b"]),
        make_fn("b", &["c"]),
        make_fn("c", &[]),
    ];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["a"]));
    assert_eq!(result, vec![0, 1, 2], "chain a→b→c should include all");
}

#[test]
#[timeout(30000)]
fn disconnected_functions_not_included() {
    let fns = vec![
        make_fn("a", &["b"]),
        make_fn("b", &[]),
        make_fn("c", &[]), // disconnected
        make_fn("d", &[]), // disconnected
    ];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["a"]));
    assert_eq!(result, vec![0, 1], "disconnected c and d should not appear");
}

#[test]
#[timeout(30000)]
fn multiple_initial_names() {
    let fns = vec![make_fn("a", &[]), make_fn("b", &[]), make_fn("c", &[])];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["a", "c"]));
    assert_eq!(result, vec![0, 2]);
}

#[test]
#[timeout(30000)]
fn full_path_matching() {
    let fns = vec![make_fn("a", &[])];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["crate::test::a"]));
    assert_eq!(result, vec![0], "should match by full_path");
}

#[test]
#[timeout(30000)]
fn closure_postcondition_keeps_matching_mut_companion() {
    let fns = vec![
        make_fn("closure_postcondition_3_i_u_i", &[]),
        make_fn("closure_postcondition_mut_4_i_u_i_i", &[]),
    ];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["closure_postcondition_3_i_u_i"]));
    assert_eq!(
        result,
        vec![0, 1],
        "keeping a closure postcondition should also retain its matching mut companion"
    );
}

#[test]
#[timeout(30000)]
fn postcondition_keeps_matching_mut_companion() {
    let fns = vec![
        make_fn("postcondition", &[]),
        make_fn("postcondition_mut", &[]),
    ];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["postcondition"]));
    assert_eq!(
        result,
        vec![0, 1],
        "keeping a postcondition should also retain its matching mut companion"
    );
}

#[test]
#[timeout(30000)]
fn diamond_dependency() {
    // a → {b, c}, both b and c → d
    let fns = vec![
        make_fn("a", &["b", "c"]),
        make_fn("b", &["d"]),
        make_fn("c", &["d"]),
        make_fn("d", &[]),
    ];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["a"]));
    assert_eq!(result, vec![0, 1, 2, 3], "diamond should include all 4");
}

// --- Requires clause transitivity ---

#[test]
#[timeout(30000)]
fn requires_clause_expands_needed_set() {
    let fns = vec![
        // a's body doesn't call anything, but its requires does
        {
            let mut def = make_fn("a", &[]);
            def.set_requires(vec![logic_fn_call("b", vec![var("x")])]);
            def
        },
        make_fn("b", &[]),
        make_fn("c", &[]),
    ];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["a"]));
    assert_eq!(
        result,
        vec![0, 1],
        "requires clause should pull in b; c should stay out"
    );
}

// --- Spec axiom reverse inclusion (#1296) ---

#[test]
#[timeout(30000)]
fn ensures_clause_pulls_in_lemma_function() {
    // "id" is needed by the goal. "id_mono" is a lemma whose ensures
    // references "id". The reverse inclusion should pull id_mono in.
    let fns = vec![
        make_fn("id", &[]),
        make_fn_with_ensures("id_mono", &[], &["id"]),
    ];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["id"]));
    assert_eq!(
        result,
        vec![0, 1],
        "id_mono's ensures mentions id → should be included (#1296)"
    );
}

#[test]
#[timeout(30000)]
fn ensures_clause_does_not_pull_unrelated() {
    // "id" is needed. "other_lemma" has ensures referencing "unrelated".
    let fns = vec![
        make_fn("id", &[]),
        make_fn_with_ensures("other_lemma", &[], &["unrelated"]),
    ];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["id"]));
    assert_eq!(
        result,
        vec![0],
        "other_lemma's ensures doesn't mention id → excluded"
    );
}

#[test]
#[timeout(30000)]
fn ensures_reverse_inclusion_already_included_function_not_duplicated() {
    // "a" calls "b" in its body. "c" has ensures referencing "b".
    // Forward closure already includes a and b.
    // Reverse inclusion should add c but not duplicate b.
    let fns = vec![
        make_fn("a", &["b"]),
        make_fn("b", &[]),
        make_fn_with_ensures("c", &[], &["b"]),
    ];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["a"]));
    assert_eq!(
        result,
        vec![0, 1, 2],
        "c's ensures mentions b → included via reverse inclusion"
    );
}

#[test]
#[timeout(30000)]
fn ensures_reverse_inclusion_skips_already_forward_included() {
    // "a" calls "b". "b" has ensures that mentions "a" — but "b" is already
    // included via forward closure, so the ensures check should skip it.
    let fns = vec![make_fn("a", &["b"]), make_fn_with_ensures("b", &[], &["a"])];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["a"]));
    assert_eq!(result, vec![0, 1]);
}

#[test]
#[timeout(30000)]
fn ensures_reverse_inclusion_with_empty_ensures() {
    // Functions with empty ensures should not trigger reverse inclusion.
    let fns = vec![
        make_fn("a", &[]),
        make_fn("b", &[]), // empty ensures
    ];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["a"]));
    assert_eq!(result, vec![0], "b has no ensures → not included");
}

#[test]
#[timeout(30000)]
fn ensures_reverse_inclusion_multiple_lemmas() {
    // Goal needs "f". Two lemmas both have ensures referencing "f".
    let fns = vec![
        make_fn("f", &[]),
        make_fn_with_ensures("lemma1", &[], &["f"]),
        make_fn_with_ensures("lemma2", &[], &["f"]),
        make_fn_with_ensures("lemma3", &[], &["unrelated"]),
    ];
    let result = filter_logic_fn_indices_for_goal(&fns, &names(&["f"]));
    assert_eq!(
        result,
        vec![0, 1, 2],
        "both lemma1 and lemma2 mention f; lemma3 does not"
    );
}
