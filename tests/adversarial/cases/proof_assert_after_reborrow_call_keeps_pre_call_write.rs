//@ expect: reject
//@ mechanism: the proof_assert lane does not havoc the pointee of a `&mut` that is reborrowed into a call. After `*acc = 2; set1(acc);` it still reads `*acc == 2`, although `set1`'s contract (`ensures(true)`) says nothing about the final value and Creusot leaves `*acc` unconstrained after the call. The function-level lane does not make this mistake on the same body: `#[ensures(^acc == 2u32)]`, or returning `*acc` under `#[ensures(result == 2u32)]`, is `unknown (incomplete)`. Only the assertion lane carries the stale write, and D-82 then credits `f` on an assertion that is false.
//@ accept-means: an assertion that reads a `&mut` pointee after a call that overwrote it is proved from the value written before the call, and the crate exits 0.
//@ WHY THE ASSERTION IS FALSE: `set1` stores 1 through the reborrow, so `*acc` is 1 at the assertion, never 2.
//@ teeth: MEASURED ACCEPTED, exit 0: `proof_assert in creusot_test::f verified ✓` and `f verified ✓`. A local `let acc = &mut x;` and a contract-free `f` are accepted the same way. With an uncontracted `set1` the crate is refused only because the function-level lane injects a fail-closed `false`; the assertion line still reads `verified ✓`. The control writes after the call.
//@ fixed-by: ?
//@ also-verified: set1
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn set1(q: &mut u32) {
    *q = 1;
}

#[ensures(true)]
pub fn f(acc: &mut u32) {
    *acc = 2;
    set1(acc);
    proof_assert!(*acc == 2u32);
}
