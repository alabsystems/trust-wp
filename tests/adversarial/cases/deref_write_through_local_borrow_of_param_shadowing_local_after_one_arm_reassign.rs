//@ expect: reject
//@ mechanism: deref_write_through_local_borrow_of_param_after_one_arm_reassign with the owner a
//@ mechanism: LOCAL `x` that shadows the parameter `x` it is initialised from: the local's binding
//@ mechanism: on the arm that kept it is the parameter's symbol, which has the local's own name, so
//@ mechanism: resolving the write's self-reference against it leaves a name the lane reads at the
//@ mechanism: post-write state. A guard keyed on the owner being a parameter does not cover it.
//@ accept-means: a write through a local borrow of a local named like the parameter it copies makes
//@ accept-means: a reachable path's premises contradictory, and an assertion guarded by it is credited.
//@
//@ WHY THE ASSERTION IS FALSE, as a concrete execution: f(0, false) leaves x at 1, not 11.
//@ verdict: failed
//@ fixed-by: fix(write-back): the legacy deref handlers record the rvalue as written again (D-171)
//@ teeth: ACCEPTED at exit 0 with the governed write's resolved value handed to the legacy deref
//@ teeth: handlers; refused as vacuous with the rvalue recorded as written, where the arm that
//@ teeth: reassigned is doubled too and the whole premise set is UNSAT. The rejection rests on that
//@ teeth: contradiction, not on the post-write value: the path-local defect underneath is
//@ teeth: deref_write_through_local_borrow_of_param_in_one_arm, which is live. With D-237 the local
//@ teeth: is named apart from the parameter it shadows, the self-reference resolves to the local, and
//@ teeth: the assertion is refuted (FAILED, validated counterexample) instead of refused as vacuous.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100 && x@ > -100)]
pub fn f(x: i32, c: bool) {
    let mut x = x;
    if c {
        x = 10;
    }
    let b = &mut x;
    *b += 1;
    proof_assert!(!c ==> x@ == 11);
}
