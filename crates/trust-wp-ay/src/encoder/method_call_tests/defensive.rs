// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Defensive error path tests for match_enc method fallbacks (#1512) ---

/// `encode_datatype_spec_method` returns `EncodingError::Unsupported` for
/// unknown method names. This defensive `_` arm guards against dispatch
/// table desynchronization — if a new method were added to the dispatcher
/// without a corresponding match arm in `datatype_spec.rs`, this error
/// would fire. Part of #1512.
#[test]
#[timeout(30000)]
fn encode_datatype_spec_method_unknown_returns_error() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_datatype_spec_method(&var("x"), "nonexistent_spec", None);
    assert!(
        result.is_err(),
        "unknown spec method should produce EncodingError, got: {result:?}"
    );
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("nonexistent_spec"),
        "error should name the unknown method, got: {msg}"
    );
}

/// `encode_fset_method` returns `EncodingError::Unsupported` for unknown
/// method names. Guards against dispatch table desynchronization — ensures
/// the defensive fallback correctly rejects unrecognized FSet methods.
/// Part of #1512.
#[test]
#[timeout(30000)]
fn encode_fset_method_unknown_returns_error() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_fset_method(&var("s"), "nonexistent_fset", &[], None);
    assert!(
        result.is_err(),
        "unknown FSet method should produce EncodingError, got: {result:?}"
    );
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("nonexistent_fset"),
        "error should name the unknown method, got: {msg}"
    );
}

/// `encode_fset_method` redirects non-Int receivers (e.g., Tokens) to
/// `encode_bool_method_predicate` for `contains` and `encode_int_method_uf`
/// for value-returning methods. This prevents sort mismatch panics when
/// the dispatch incorrectly routes a custom-type receiver to FSet. (#2316)
#[test]
#[timeout(30000)]
fn encode_fset_method_non_int_receiver_redirects_to_generic_uf() {
    let mut encoder = AYEncoder::new();
    let id = intern_sort_name("Tokens");
    let receiver = PureExpr::Var("tokens".to_string(), Some(ExprSort::Datatype(id)));
    let ns_arg = PureExpr::Var("ns".to_string(), Some(ExprSort::Int));

    // contains on non-Int receiver should redirect to Bool method predicate
    let result = encoder.encode_fset_method(&receiver, "contains", &[ns_arg.clone()], None);
    assert!(
        result.is_ok(),
        "non-Int receiver .contains() must not panic or error: {result:?}"
    );
    assert!(
        !encoder.decls.has_spec_func("fset_contains"),
        "non-Int receiver must NOT create fset_contains UF"
    );

    // len on non-Int receiver should redirect to Int method UF
    let result = encoder.encode_fset_method(&receiver, "len", &[], None);
    assert!(
        result.is_ok(),
        "non-Int receiver .len() must not panic or error: {result:?}"
    );
    assert!(
        !encoder.decls.has_spec_func("fset_len"),
        "non-Int receiver must NOT create fset_len UF"
    );
}

/// `encode_fmap_method` returns `EncodingError::Unsupported` for unknown
/// method names. Guards against dispatch table desynchronization — ensures
/// the defensive fallback correctly rejects unrecognized FMap methods.
/// Part of #1512.
#[test]
#[timeout(30000)]
fn encode_fmap_method_unknown_returns_error() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_fmap_method(&var("m"), "nonexistent_fmap", &[], None);
    assert!(
        result.is_err(),
        "unknown FMap method should produce EncodingError, got: {result:?}"
    );
    let msg = result.unwrap_err().to_string();
    assert!(
        msg.contains("nonexistent_fmap"),
        "error should name the unknown method, got: {msg}"
    );
}

// --- The collection-method ARITY rule (wp-campaign e1aff5a8) ---
//
// THE RULE: a same-named call of a DIFFERENT arity is not that collection
// method. `FMap::get`/`lookup`/`index`/`index_logic` and `FSet`/`FMap`
// `contains` each take exactly ONE key/element argument, and each arm reads
// it as `args[0]`. `Cell::get()` takes ZERO arguments and reaches the FMap
// dispatcher through a `#[logic]` model on a `Cell` receiver, so the arm has
// to match on arity before it indexes: without the guard `args[0]` panicked
// ("index out of bounds: the len is 0 but the index is 0"), which process
// isolation re-raised as `<T as Rd>::rd panicked during verification` — a
// CRASH where a verdict was owed, and a crash is not a safe failure mode.
// With the guard the call falls to the dispatcher's own default arm:
// `EncodingError::unsupported` for FSet/FMap, which fails the obligation
// CLOSED.
//
// Each test below panics (not fails) if the arity guard on its arm is
// removed. The FMap one is the shape the driver actually hit.

/// Zero-argument `get` is not an FMap lookup: no key argument exists to read.
#[test]
#[timeout(30000)]
fn encode_fmap_method_zero_arg_get_is_not_a_lookup() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_fmap_method(&var("c"), "get", &[], None);
    assert!(
        result.is_err(),
        "a zero-argument `get` is not an FMap lookup and must fail closed, got: {result:?}"
    );
    assert!(
        !encoder.decls.has_spec_func("fmap_lookup"),
        "a zero-argument `get` must NOT declare the fmap_lookup UF"
    );
}

/// The same rule on the other three FMap lookup spellings.
#[test]
#[timeout(30000)]
fn encode_fmap_method_zero_arg_lookup_spellings_are_not_lookups() {
    for method in ["lookup", "index", "index_logic"] {
        let mut encoder = AYEncoder::new();
        let result = encoder.encode_fmap_method(&var("c"), method, &[], None);
        assert!(
            result.is_err(),
            "a zero-argument `{method}` is not an FMap lookup, got: {result:?}"
        );
        assert!(
            !encoder.decls.has_spec_func("fmap_lookup"),
            "a zero-argument `{method}` must NOT declare the fmap_lookup UF"
        );
    }
}

/// Zero-argument `contains` is not an FMap membership test.
#[test]
#[timeout(30000)]
fn encode_fmap_method_zero_arg_contains_is_not_a_membership_test() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_fmap_method(&var("c"), "contains", &[], None);
    assert!(
        result.is_err(),
        "a zero-argument `contains` is not an FMap membership test, got: {result:?}"
    );
    assert!(
        !encoder.decls.has_spec_func("fmap_contains"),
        "a zero-argument `contains` must NOT declare the fmap_contains UF"
    );
}

/// Zero-argument `contains` is not an FSet membership test either.
#[test]
#[timeout(30000)]
fn encode_fset_method_zero_arg_contains_is_not_a_membership_test() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_fset_method(&var("s"), "contains", &[], None);
    assert!(
        result.is_err(),
        "a zero-argument `contains` is not an FSet membership test, got: {result:?}"
    );
    assert!(
        !encoder.decls.has_spec_func("fset_contains"),
        "a zero-argument `contains` must NOT declare the fset_contains UF"
    );
}

/// `Mapping::get` has the same one-key rule, but its default arm is the
/// generic uninterpreted method rather than an error: a zero-argument `get`
/// must reach that fallback (an opaque term asserting nothing) instead of
/// indexing a key that is not there.
#[test]
#[timeout(30000)]
fn encode_mapping_method_zero_arg_get_takes_the_generic_uf() {
    let mut encoder = AYEncoder::new();
    let result = encoder.encode_mapping_method(&var("c"), "get", &[], None);
    assert!(
        result.is_ok(),
        "a zero-argument `get` must take the generic UF fallback, got: {result:?}"
    );
    assert!(
        !encoder.decls.has_spec_func("mapping_get"),
        "a zero-argument `get` must NOT declare the mapping_get UF"
    );
}
