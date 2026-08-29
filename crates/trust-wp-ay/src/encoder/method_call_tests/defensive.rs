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
