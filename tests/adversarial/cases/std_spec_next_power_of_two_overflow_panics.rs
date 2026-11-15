//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: `next_power_of_two` on an unsigned integer panics when the power it returns does not
//@ mechanism: fit the type (overflow checks on), and its std spec stated no precondition. It now owes
//@ mechanism: `2 * self@ <= Self::MAX@ + 2`, i.e. `self` at most the type's largest power of two.
//@ accept-means: `next_power_of_two`'s spec stopped owing its overflow panic.
//@ fixed-by: D-121 — a std spec owes every panic of its function it can state.
//@ WHY THE CONTRACT IS FALSE: `f` admits `x == 129`, whose next power of two, 256, is past
//@ WHY THE CONTRACT IS FALSE: `u8::MAX`: the call panics.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, with the std spec tables reverted to the
//@ teeth: base; its twin std_spec_next_power_of_two_in_range_control differs in the bound alone.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ <= 129)]
#[ensures(true)]
pub fn f(x: u8) -> u8 {
    x.next_power_of_two()
}
