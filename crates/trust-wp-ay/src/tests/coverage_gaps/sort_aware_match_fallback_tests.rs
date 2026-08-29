// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{FuncDecl, Sort};
use ntest::timeout;
use trust_wp_core::formula::Pattern;

use super::*;

fn spec_decl_with_prefix<'a>(encoder: &'a AYEncoder, prefix: &str) -> &'a FuncDecl {
    let mut matches = encoder
        .decls()
        .spec_functions_ref()
        .iter()
        .filter(|(name, _)| name.starts_with(prefix));
    let first = matches.next().unwrap_or_else(|| {
        panic!(
            "expected spec function with prefix {prefix}, found {:?}",
            encoder.decls().spec_func_names().collect::<Vec<_>>()
        )
    });
    assert!(
        matches.next().is_none(),
        "expected exactly one spec function with prefix {prefix}, found {:?}",
        encoder
            .decls()
            .spec_func_names()
            .filter(|name| name.starts_with(prefix))
            .collect::<Vec<_>>()
    );
    first.1
}

#[test]
#[timeout(30000)]
fn unwrap_on_uninterpreted_option_uses_sort_aware_accessor() {
    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("opt", Sort::Uninterpreted("Option".to_string()))
        .expect("declare opt as generic Option");

    let result = encoder.encode_pure(&method_call(var("opt"), "unwrap", vec![]));
    assert!(
        result.is_ok(),
        "unwrap on generic Option receiver should encode without sort mismatch: {result:?}"
    );
    assert!(
        !encoder.decls().has_spec_func("spec_unwrap"),
        "non-Int unwrap fallback should not reuse the legacy Int-domain accessor"
    );

    let accessor = spec_decl_with_prefix(&encoder, "spec_unwrap__dom_");
    assert_eq!(
        accessor.domain(),
        &[Sort::Uninterpreted("Option".to_string())],
        "generic Option unwrap accessor should be declared on the Option sort"
    );
    assert_eq!(
        accessor.range(),
        &Sort::Int,
        "generic Option unwrap accessor should preserve the Int payload sort"
    );
}

#[test]
#[timeout(30000)]
fn is_some_on_uninterpreted_option_uses_sort_aware_tester() {
    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("opt", Sort::Uninterpreted("Option".to_string()))
        .expect("declare opt as generic Option");

    let result = encoder.encode_pure(&method_call(var("opt"), "is_some", vec![]));
    assert!(
        result.is_ok(),
        "is_some on generic Option receiver should encode without sort mismatch: {result:?}"
    );
    assert!(
        !encoder.decls().has_spec_func("is_some"),
        "non-Int tester fallback should not reuse the legacy Int-domain tester"
    );

    let tester = spec_decl_with_prefix(&encoder, "is_some__dom_");
    assert_eq!(
        tester.domain(),
        &[Sort::Uninterpreted("Option".to_string())],
        "generic Option tester should be declared on the Option sort"
    );
    assert_eq!(
        tester.range(),
        &Sort::Bool,
        "generic Option tester should still return Bool"
    );
}

#[test]
#[timeout(30000)]
fn match_fallback_on_iter_mut_scrutinee_uses_native_datatype() {
    // After #2231 sort compatibility broadening, Uninterpreted("IterMut") is
    // compatible with the synthesized Adt_Wrap datatype. The match encodes via
    // native datatype theory (testers/selectors) instead of UF spec functions.
    let mut encoder = AYEncoder::new();
    encoder
        .get_or_declare_var("it", Sort::Uninterpreted("IterMut".to_string()))
        .expect("declare iterator carrier");

    let expr = match_expr(
        var("it"),
        vec![
            (
                Pattern::Constructor {
                    name: "Wrap".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".into()))),
                },
                add(var("x"), int(1)),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "match on IterMut carrier should encode via native datatype: {result:?}"
    );
    // Native datatype encoding: no UF spec functions needed.
    assert!(
        !encoder.decls().has_spec_func("is_wrap"),
        "native datatype encoding should not create legacy Int-domain tester"
    );
    assert!(
        !encoder.decls().has_spec_func("payload_wrap"),
        "native datatype encoding should not create legacy Int-domain accessor"
    );
    // No sort-aware UF functions either — testers/selectors are native.
    assert!(
        encoder
            .decls()
            .spec_func_names()
            .filter(|name| name.starts_with("is_wrap") || name.starts_with("payload_wrap"))
            .count()
            == 0,
        "native datatype path should not create any UF spec functions for Wrap"
    );
}
