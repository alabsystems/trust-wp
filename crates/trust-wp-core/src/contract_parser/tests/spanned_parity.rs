// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parity between trust-wp's two contract-expression parsers.
//!
//! One contract grammar has two hand-written recursive-descent implementations:
//! the UNSPANNED path (`parse_contract`) used for normal-fn `#[requires]` /
//! `#[ensures]`, and the SPANNED path (`parse_contract_spanned`) used for
//! TRAIT-REFINED function preconditions (driver seam:
//! `callbacks/trait_refinement/mod.rs`). They MUST lower identical input to a
//! byte-identical [`PureExpr`].
//!
//! Why it matters for `requires`: the spanned primary previously lacked the
//! `if/else`, block `{...}`, closure `|..|`, and qualified-path `<T as Trait>::C`
//! branches the unspanned primary has. So a `#[requires(...)]` clause using any of
//! them parsed on a plain fn but hard-failed with a `ClauseParseError` on a
//! trait-refined fn — a valid precondition made silently context-dependent. Worse,
//! had the spanned parser lowered a construct to a DIFFERENT `PureExpr`, the
//! precondition would be ASSUMED at entry with one meaning and PROVEN at the call
//! site with another — a false-accept. These tests pin AST parity, not merely
//! both-parse-Ok, so that class of divergence cannot recur.

use super::*;

/// Assert the two parsers agree: both succeed AND produce the identical `PureExpr`.
#[track_caller]
fn assert_parse_parity(input: &str) {
    let unspanned = parse_contract(input)
        .unwrap_or_else(|e| panic!("unspanned parse_contract({input:?}) failed: {e}"));
    let spanned = parse_contract_spanned(input)
        .unwrap_or_else(|e| panic!("spanned parse_contract_spanned({input:?}) failed: {e}"))
        .expr;
    assert_eq!(
        unspanned, spanned,
        "spanned/unspanned AST diverged for {input:?}"
    );
}

#[test]
fn if_else_precondition_parses_identically_in_both_paths() {
    assert_parse_parity("if b { result == 1 } else { result == 2 }");
    assert_parse_parity("if old(x) > 0 { old(x) + 1 } else { 0 }");
    assert_parse_parity("if a > b { a } else { if z > 0 { z } else { 0 } }");
}

#[test]
fn closure_precondition_parses_identically_in_both_paths() {
    assert_parse_parity("|z: u32| z > 0");
    assert_parse_parity("|| result > 0");
}

#[test]
fn block_precondition_parses_identically_in_both_paths() {
    assert_parse_parity("{ let x = 1; x > 0 }");
    assert_parse_parity("{ f(); 2 }");
}

#[test]
fn qualified_path_precondition_parses_identically_in_both_paths() {
    assert_parse_parity("<T as Nat>::VALUE == 0");
    assert_parse_parity("<I3<T> as Nat>::VALUE > 0");
}

/// Corpus round-trip: forms that were already shared must stay parity, and the
/// four newly-unified primary forms must now match too.
#[test]
fn contract_grammar_corpus_parses_identically_in_both_paths() {
    for input in [
        // Boolean / implication structure (already parity via shared precedence).
        "x >= 0 ==> x + 1 > 0",
        "x > 0 || y > 0",
        "a && b && c",
        // Quantifiers / old / methods (already parity).
        "forall<i: Int> i > 0",
        "old(x) == 1",
        "x.foo() == 1",
        // The four primary forms this fix unifies into the spanned path.
        "if b { 1 } else { 2 }",
        "{ let x = 1; x > 0 }",
        "|z: u32| z > 0",
        "<T as Nat>::VALUE == 0",
    ] {
        assert_parse_parity(input);
    }
}

/// Fail-CLOSED parity: a genuinely-unparseable clause must ERROR in BOTH paths.
/// A precondition that "recovers" to `true` or is silently dropped is a vacuous
/// guard — unsound — so the newly-added branches must reject malformed input just
/// as the unspanned path does, never fail open.
#[test]
fn unparseable_clause_fails_closed_in_both_paths() {
    for input in ["if x > 0 x else { 0 }", "{ x", "<T as"] {
        assert!(
            parse_contract(input).is_err(),
            "unspanned unexpectedly accepted malformed {input:?}"
        );
        assert!(
            parse_contract_spanned(input).is_err(),
            "spanned unexpectedly accepted malformed {input:?}"
        );
    }
}
