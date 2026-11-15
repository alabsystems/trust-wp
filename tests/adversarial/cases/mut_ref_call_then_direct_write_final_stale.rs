//@ expect: reject
//@ mechanism: a `&mut` parameter handed to a contracted callee and then written DIRECTLY
//@ mechanism: afterwards. The call-site lane binds `^x` to the callee's declared final
//@ mechanism: (`^r == 1`) as though the parameter borrow died at the call; the later
//@ mechanism: `*x = 2` updates only the current pointee. The code that GRANTS `^x == 1`
//@ mechanism: (the call-effect lane) and the code that OWES `^x` (the last write before
//@ mechanism: the borrow is resolved) are different lanes, so the direct write never
//@ mechanism: overrides the grant. Creusot never binds `^x` at a call: the callee's
//@ mechanism: final flows into `*x` (backend/program.rs writes the reborrow's `.final`
//@ mechanism: back into the borrowed place) and `^x` is fixed only at resolution.
//@ accept-means: any postcondition about a parameter's final value can be pinned by an
//@ accept-means: intermediate call and then contradicted by the function's own last write.
//@ WHY THE PROGRAM IS WRONG: `set` leaves `*x == 1`, then `*x = 2` runs; the caller sees
//@ WHY THE PROGRAM IS WRONG: `^x == 2`. The contract claims `^x == 1`.
//@ teeth: LIVE: ACCEPTED, `trust-wp: f verified`, base_exit_code=0, `2 verified, 0 failed`.
//@ teeth: The true twin (`^x == 2`, the control) is `unknown` on the same binary, so the
//@ teeth: lane positively believes the stale value. PRE-EXISTING; found by this front's probes.
//@ also-verified: set
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == 1i32)]
pub fn set(r: &mut i32) {
    *r = 1i32;
}

#[requires(*x == 0i32)]
#[ensures(^x == 1i32)]
pub fn f(x: &mut i32) {
    set(x);
    *x = 2i32;
}
