// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for free-identifier extraction and quantifier binding analysis.

use crate::ghost_macros::ident_capture::extract_free_identifiers;

#[test]
fn extract_free_identifiers_simple_expression() {
    let tokens: proc_macro2::TokenStream = "x > 0".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(idents, vec!["x"]);
}

#[test]
fn extract_free_identifiers_multiple_variables() {
    let tokens: proc_macro2::TokenStream = "a + b == c".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(idents, vec!["a", "b", "c"]);
}

#[test]
fn extract_free_identifiers_excludes_keywords() {
    let tokens: proc_macro2::TokenStream = "x > 0 && true".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(idents, vec!["x"], "keywords like `true` should be excluded");
}

#[test]
fn extract_free_identifiers_excludes_type_names() {
    let tokens: proc_macro2::TokenStream = "v.len() > 0 as usize".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(
        idents,
        vec!["v"],
        "type names and method names after `.` should be excluded"
    );
}

#[test]
fn extract_free_identifiers_excludes_quantifier_bound() {
    let tokens: proc_macro2::TokenStream = "forall < i : i32 > i >= 0".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        !idents.contains(&"i".to_string()),
        "quantifier-bound variable i should be excluded: {idents:?}"
    );
}

#[test]
fn extract_free_identifiers_deduplicates() {
    let tokens: proc_macro2::TokenStream = "x + x + x".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(idents, vec!["x"], "duplicate identifiers should be removed");
}

#[test]
fn extract_free_identifiers_no_variables() {
    let tokens: proc_macro2::TokenStream = "true".parse().unwrap();
    let idents = extract_free_identifiers(&tokens);
    assert!(
        idents.is_empty(),
        "expression with only keywords should have no free vars"
    );
}

#[test]
fn extract_free_identifiers_method_calls() {
    let tokens: proc_macro2::TokenStream = "v.len() > 0".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        idents.contains(&"v".to_string()),
        "receiver variable should be captured"
    );
    assert!(
        !idents.contains(&"len".to_string()),
        "method name after `.` should not be captured as a free variable"
    );
}

#[test]
fn extract_free_identifiers_excludes_uppercase_types() {
    let tokens: proc_macro2::TokenStream = "Some(x) == None".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(
        idents,
        vec!["x"],
        "uppercase identifiers (types/constructors) should be excluded"
    );
}

#[test]
fn extract_free_identifiers_excludes_field_names() {
    // `p.value` — `value` is a field, not a free variable
    let tokens: proc_macro2::TokenStream = "p.value == 10".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(
        idents,
        vec!["p"],
        "field name after `.` should not be captured"
    );
}

#[test]
fn extract_free_identifiers_excludes_function_calls() {
    // `__trust_wp_tuple_get_0(p)` — the function name is not a free variable
    let tokens: proc_macro2::TokenStream = "__trust_wp_tuple_get_0(p) == 10".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(
        idents,
        vec!["p"],
        "function call name should not be captured as a free variable"
    );
}

#[test]
fn extract_free_identifiers_field_and_call_combined() {
    // `p.value == __trust_wp_tuple_get_0(p)` — from the failing test fixture
    let tokens: proc_macro2::TokenStream = "p.value == __trust_wp_tuple_get_0(p)".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert_eq!(
        idents,
        vec!["p"],
        "only the receiver variable should be captured"
    );
}

// --- #1727: proof_assert! E0425/E0423 compilation error fixes ---

#[test]
fn extract_free_identifiers_excludes_path_segments() {
    // `x::transparent()` — `x` is a module path, not a variable (#1727)
    let tokens: proc_macro2::TokenStream = "x :: transparent()".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        !idents.contains(&"x".to_string()),
        "module path segment `x` before `::` should not be captured: {idents:?}"
    );
    assert!(
        !idents.contains(&"transparent".to_string()),
        "function call `transparent` should not be captured: {idents:?}"
    );
}

#[test]
fn extract_free_identifiers_excludes_char_builtin() {
    // `size_of_logic :: < char > ()` — `char` is a builtin type, not a variable (#1727)
    let tokens: proc_macro2::TokenStream = "size_of_logic :: < char > ()".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        !idents.contains(&"char".to_string()),
        "builtin type `char` should not be captured as a free variable: {idents:?}"
    );
    assert!(
        !idents.contains(&"size_of_logic".to_string()),
        "path segment `size_of_logic` should not be captured: {idents:?}"
    );
}

#[test]
fn extract_free_identifiers_nested_quantifier_bindings() {
    // `exists<prod: Seq<(K, V)>, it1: &mut IntoIter<K, V>> it1.completed()`
    // Inner `<(K, V)>` and `<K, V>` must not prematurely close the binding (#1727)
    let tokens: proc_macro2::TokenStream =
        "exists < prod : Seq < X > , it1 : Iter < Y > > it1 . completed()"
            .parse()
            .unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        !idents.contains(&"prod".to_string()),
        "quantifier-bound `prod` should be excluded: {idents:?}"
    );
    assert!(
        !idents.contains(&"it1".to_string()),
        "quantifier-bound `it1` after nested <> should be excluded: {idents:?}"
    );
}

#[test]
fn extract_free_identifiers_forall_with_nested_generics() {
    // `forall<r: Seq<_>, a: Seq<_>, b: Seq<_>> r == a.concat(b)`
    // All three bindings must be recognized despite nested `<_>` (#1727)
    let tokens: proc_macro2::TokenStream =
        "forall < r : Seq < X > , a : Seq < X > , b : Seq < X > > r == a . concat(b)"
            .parse()
            .unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        !idents.contains(&"r".to_string()),
        "quantifier-bound `r` should be excluded: {idents:?}"
    );
    assert!(
        !idents.contains(&"a".to_string()),
        "quantifier-bound `a` should be excluded: {idents:?}"
    );
    assert!(
        !idents.contains(&"b".to_string()),
        "quantifier-bound `b` should be excluded: {idents:?}"
    );
}

#[test]
fn extract_free_identifiers_mixed_bound_and_free_nested() {
    // Free variable `x` should still be captured alongside quantifier-bound vars
    let tokens: proc_macro2::TokenStream = "exists < it : Iter < T > > x > 0".parse().unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        !idents.contains(&"it".to_string()),
        "quantifier-bound `it` should be excluded: {idents:?}"
    );
    assert!(
        idents.contains(&"x".to_string()),
        "free variable `x` should still be captured: {idents:?}"
    );
}

#[test]
fn extract_free_identifiers_collections_quantifier_does_not_capture_path_or_binders() {
    // Mirrors failing proof_assert! from should_succeed/cc/collections.rs.
    let tokens: proc_macro2::TokenStream =
        "exists < prod : Seq < ( K , V ) > , it1 : & mut hash_map :: IntoIter < K , V > > \
         it1 . completed() && it0 . produces ( prod , * it1 )"
            .parse()
            .unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        idents.contains(&"it0".to_string()),
        "free variable `it0` should be captured: {idents:?}"
    );
    assert!(
        !idents.contains(&"it1".to_string()),
        "quantifier-bound `it1` should not be captured: {idents:?}"
    );
    assert!(
        !idents.contains(&"prod".to_string()),
        "quantifier-bound `prod` should not be captured: {idents:?}"
    );
    assert!(
        !idents.contains(&"hash_map".to_string()),
        "module path segment `hash_map` should not be captured: {idents:?}"
    );
}

// --- Phase 3 regression: mixed path-segment + quantifier input ---

#[test]
fn extract_free_identifiers_mixed_path_and_quantifier_keeps_true_free_vars() {
    // Regression: Ensure path segments and binders are excluded while true free vars are kept
    let tokens: proc_macro2::TokenStream = "forall < i : i32 > std :: cmp :: min(x, i) >= 0"
        .parse()
        .unwrap();
    let idents: Vec<String> = extract_free_identifiers(&tokens)
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        idents.contains(&"x".to_string()),
        "free variable `x` should be captured: {idents:?}"
    );
    assert!(
        !idents.contains(&"i".to_string()),
        "quantifier-bound `i` should be excluded: {idents:?}"
    );
    assert!(
        !idents.contains(&"std".to_string()),
        "path segment `std` should be excluded: {idents:?}"
    );
    assert!(
        !idents.contains(&"cmp".to_string()),
        "path segment `cmp` should be excluded: {idents:?}"
    );
    assert!(
        !idents.contains(&"min".to_string()),
        "function call `min` should be excluded: {idents:?}"
    );
}
