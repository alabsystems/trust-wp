//@ expect: reject
//@ ay-not-unsat: f
//@ mechanism: moved_borrow_double_hop_write_lost seen from an ordinary caller. `go` borrows
//@ mechanism: its own local, hands it to a function whose `^r == *r` was granted by the lost
//@ mechanism: write, and reads the local back. The false premise is not confined to the
//@ mechanism: function that carries the `^` clause: it reaches every call site through the
//@ mechanism: postcondition, and `go`'s own contract mentions no `^` at all.
//@ accept-means: an ordinary caller with a plain `result@ == 0` contract, never naming a
//@ accept-means: prophecy, is proved from a final value that the callee's body contradicts.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: `go()` returns 9, and claims 0.
//@ teeth: MEASURED as ACCEPTED, exit 0, "2 verified, 0 failed".
//@ also-verified: go
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    let mut q = r;
    let s = &mut q;
    **s = 9;
}

#[ensures(result@ == 0)]
pub fn go() -> i32 {
    let mut v = 0i32;
    f(&mut v);
    v
}
