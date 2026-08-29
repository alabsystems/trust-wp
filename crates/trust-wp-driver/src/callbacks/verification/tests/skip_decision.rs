// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::callbacks::verification::skip_decision::{
    should_skip_bodyless_trait_method, ContractClausePresence,
};

// -- should_skip_bodyless_trait_method (helper predicate only) --------------------
//
// These tests exercise the boolean predicate extracted from the verification
// skip logic. They do NOT exercise the actual `tcx.defaultness()` query guard
// that caused the ICE in #1169 — that requires a rustc session and is covered
// by the compat harness test (`result/own.rs`). (#1267 AC3)

#[test]
fn skip_bodyless_trait_method_trait_without_body() {
    assert!(
        should_skip_bodyless_trait_method(true, false),
        "trait container + no default body = skip"
    );
}

#[test]
fn skip_bodyless_trait_method_trait_with_body() {
    assert!(
        !should_skip_bodyless_trait_method(true, true),
        "trait container + default body = do NOT skip (it has a body to verify)"
    );
}

#[test]
fn skip_bodyless_trait_method_impl_without_body() {
    assert!(
        !should_skip_bodyless_trait_method(false, false),
        "impl container = do NOT skip regardless of defaultness"
    );
}

#[test]
fn skip_bodyless_trait_method_impl_with_body() {
    assert!(
        !should_skip_bodyless_trait_method(false, true),
        "impl container + body = do NOT skip"
    );
}

// -- ContractClausePresence::needs_type_invariant_injection ------------------------------

#[allow(clippy::fn_params_excessive_bools)] // Test helper for exhaustive truth-table coverage
fn make_clause_presence(req: bool, ens: bool, inv: bool, var: bool) -> ContractClausePresence {
    ContractClausePresence {
        has_requires: req,
        has_ensures: ens,
        has_invariants: inv,
        has_variants: var,
    }
}

#[test]
fn type_invariant_injection_empty_defs_returns_false() {
    let cp = make_clause_presence(false, false, false, false);
    assert!(
        !cp.needs_type_invariant_injection(false),
        "no type invariant defs = no injection regardless of contract state"
    );
}

#[test]
fn type_invariant_injection_with_defs_empty_contract() {
    let cp = make_clause_presence(false, false, false, false);
    assert!(
        cp.needs_type_invariant_injection(true),
        "type invariant defs + empty contract = injection needed"
    );
}

#[test]
fn type_invariant_injection_with_defs_and_requires() {
    let cp = make_clause_presence(true, false, false, false);
    assert!(
        !cp.needs_type_invariant_injection(true),
        "explicit requires present = no injection (contract already has clauses)"
    );
}

#[test]
fn type_invariant_injection_with_defs_and_ensures() {
    let cp = make_clause_presence(false, true, false, false);
    assert!(
        !cp.needs_type_invariant_injection(true),
        "explicit ensures present = no injection"
    );
}

#[test]
fn type_invariant_injection_with_defs_and_invariants() {
    let cp = make_clause_presence(false, false, true, false);
    assert!(
        !cp.needs_type_invariant_injection(true),
        "explicit invariants present = no injection"
    );
}

#[test]
fn type_invariant_injection_with_defs_and_variants() {
    let cp = make_clause_presence(false, false, false, true);
    assert!(
        !cp.needs_type_invariant_injection(true),
        "explicit variants present = no injection"
    );
}

#[test]
fn type_invariant_injection_with_defs_and_all_clauses() {
    let cp = make_clause_presence(true, true, true, true);
    assert!(
        !cp.needs_type_invariant_injection(true),
        "all clauses present = no injection"
    );
}

// -- ContractClausePresence::has_clauses -------------------------------------------------

#[test]
fn contract_has_clauses_all_empty() {
    assert!(
        !make_clause_presence(false, false, false, false).has_clauses(),
        "no clauses = false"
    );
}

#[test]
fn contract_has_clauses_only_requires() {
    assert!(
        make_clause_presence(true, false, false, false).has_clauses(),
        "requires only = true"
    );
}

#[test]
fn contract_has_clauses_only_ensures() {
    assert!(
        make_clause_presence(false, true, false, false).has_clauses(),
        "ensures only = true"
    );
}

#[test]
fn contract_has_clauses_only_invariants() {
    assert!(
        make_clause_presence(false, false, true, false).has_clauses(),
        "invariants only = true"
    );
}

#[test]
fn contract_has_clauses_only_variants() {
    assert!(
        make_clause_presence(false, false, false, true).has_clauses(),
        "variants only = true"
    );
}

#[test]
fn contract_has_clauses_all_present() {
    assert!(
        make_clause_presence(true, true, true, true).has_clauses(),
        "all clauses present = true"
    );
}
