//@ expect: reject
//@ fn-failed: caller
//@ also-verified: reset
//@ mechanism: a by-value STRUCT parameter borrowed whole into a call (`reset(&mut s)`) is not
//@ mechanism: advanced by the call: after it `s` still denotes its entry value, so the precondition
//@ mechanism: about that entry value discharges a claim about the current one. `reset`'s contract
//@ mechanism: says nothing about `^t`, so the only sound reading is that `s` is unknown after the
//@ mechanism: call. The same call on a by-value `i32` parameter (`set(&mut x)`) or on a field of the
//@ mechanism: struct (`set(&mut s.a)`) is refuted; the whole-struct borrow through a named reborrow
//@ mechanism: (`let r = &mut s; reset(r);`), a return of the whole struct, and an `ensures` that
//@ mechanism: compares with the entry value (`result@ == s.a@`, no `requires`) are ACCEPTED the same
//@ mechanism: way. The TRUE twin, whose callee pins `(^t).a@ == 4`, is reported vacuous: the entry
//@ mechanism: fact `s.a@ == 3` and the call's `s.a@ == 4` land on one term.
//@ accept-means: a precondition about a by-value struct parameter survives a call that overwrote the
//@ accept-means: parameter through `&mut`, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `reset` sets `a` to 4, so `caller` returns 4 and claims 3.
//@ fixed-by: D-241: the value a by-value struct parameter holds after a `&mut` borrow of it ends is named apart from its entry value in the function lane.
//@ teeth: MEASURED ACCEPTED, exit 0, on the current build and on the build before D-141; found probing
//@ teeth: the `&mut T` final-value side of D-141, unrelated to type invariants.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct P {
    pub a: i32,
    pub b: i32,
}

#[ensures(true)]
pub fn reset(t: &mut P) {
    t.a = 4;
}

#[requires(s.a@ == 3)]
#[ensures(result@ == 3)]
pub fn caller(mut s: P) -> i32 {
    reset(&mut s);
    s.a
}
