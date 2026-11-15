//@ expect: reject
//@ mechanism: a recursive `#[variant(n@)]` whose recursive call is handed a local written through a borrow
//@ mechanism: before the call: `let r = &mut m; *r = 5; f(m)`, and a `#[check(terminates)]` callee handed
//@ mechanism: `&mut m` whose postcondition says `(^x)@ == 5`. The recursive-call walk
//@ mechanism: (`extract_recursive_calls_from_block`) follows only projection-free assignments and binds a
//@ mechanism: non-recursive call's destination alone, so `m` is read as 0 and `0 < n` discharges the
//@ mechanism: decrease. The same body with `m = 5` written directly is refuted (`variant decrease`).
//@ mechanism: Found probing D-140's termination spelling; not a drop.
//@ accept-means: a recursive function that does not terminate is credited `verified ✓ (termination)` under
//@ accept-means: `#[check(terminates)]`, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `through_borrow(1)` calls `through_borrow(5)`, which calls itself with 5
//@ WHY THE CONTRACT IS FALSE: forever; likewise `through_callee`.
//@ fixed-by: D-140: the recursive-call walk forgets every lent local after a store through a reference and
//@ fixed-by: after a call handed an argument it may write through.
//@ teeth: MEASURED on one binary with the walk's forgetting disabled by an env knob (never committed):
//@ teeth: ACCEPTED, exit 0, both functions `verified ✓ (termination)`; with it, each is FAILED (`variant
//@ teeth: decrease`). No drop glue is involved.
//@ also-verified: set5
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[ensures((^x)@ == 5)]
pub fn set5(x: &mut u32) {
    *x = 5;
}

#[check(terminates)]
#[variant(n@)]
pub fn through_borrow(n: u32) {
    if n == 0 {
        return;
    }
    let mut m = 0u32;
    let r = &mut m;
    *r = 5;
    through_borrow(m);
}

#[check(terminates)]
#[variant(n@)]
pub fn through_callee(n: u32) {
    if n == 0 {
        return;
    }
    let mut m = 0u32;
    set5(&mut m);
    through_callee(m);
}
