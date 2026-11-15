//@ expect: reject
//@ mechanism: `discover_proof_assert_functions` admits only `DefKind::Fn | DefKind::AssocFn` bodies, so a closure with no contract of its own never becomes a verification target and the `proof_assert!` in its body is never examined by either assertion pass; the enclosing function is credited on its own contract and the run exits 0
//@ accept-means: an assertion no pass examined is reported as nothing at all: `proof_assert: 0 verified, 0 failed, 0 errors` over a crate that contains one.
//@ WHY THE ASSERTION IS FALSE: the closure is called with 3; nothing says its argument is 7, and Creusot puts the assertion in the closure's own VC with a `true` precondition.
//@ teeth: MEASURED ACCEPTED, exit 0, with `proof_assert_verified=0 proof_assert_failed=0 proof_assert_errors=0` on the wire — a live false accept, committed RED. The contracted twin `own_assertion_in_closure_is_not_the_parents.rs` differs in the closure's contract alone and is examined.
//@ fixed-by: D-106 — `discover_proof_assert_functions` admits closure bodies, so a contract-free closure's assertions reach the standalone pass, which proves them in the closure's own (empty) precondition
//@ also-verified: parent
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
#[ensures(result@ == x@ + 1)]
pub fn parent(x: u32) -> u32 {
    let c = |y: u32| {
        proof_assert!(y@ == 7);
        y
    };
    let _ = c(3);
    x + 1
}
