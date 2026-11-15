//@ expect: reject
//@ mechanism: a closure with no contract was never a verification target (`discover_proof_assert_functions` admitted only `Fn`/`AssocFn` bodies), so its assertion was examined by no pass and the enclosing function's vacuous credit left the run clean. Once examined, it must be examined in the closure's own environment: the typeck-root fallback in `prepare_proof_assert` would have handed it the parent's `#[requires(false)]`.
//@ accept-means: a contract-free closure's assertion, false for every capture, is accepted because the function that builds the closure can never be called.
//@ WHY THE ASSERTION IS FALSE: nothing constrains the captured `x`; the closure's precondition is `true` and Creusot proves the assertion in the closure's own VC.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit, with every proof_assert counter zero. With discovery closed and the fallback RESTORED the assertion is refused as `unknown (vacuous proof)`, so this case gates the discovery half; the environment half is gated by the closure_assertion_inherits_parent_* cases, all three ACCEPTED on that same variant.
//@ fixed-by: D-106
//@ verdict: failed
//@ also-verified: parent
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(false)]
pub fn parent(x: u32) {
    let c = move || {
        proof_assert!(x@ == 1000);
    };
    c()
}
