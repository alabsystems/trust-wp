//@ expect: verify
//@ mechanism: control: the loop condition's call has no `result == e` clause, so the condition reads
//@ mechanism: a symbol for the value this evaluation returns, and the callee's clauses are stated at
//@ mechanism: it beside every assumption of the condition or its negation. The body only steps
//@ mechanism: `i` below 10, so preservation needs nothing; the EXIT needs `!result ==> k >= 10u32`
//@ mechanism: to return 10. Without the clause the exit VC had a model with `i == 0` and the
//@ mechanism: function-level check refuted `result == 10u32`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (k < 10u32))]
pub fn small(k: u32) -> bool { k < 10 }

#[ensures(result ==> k < 10u32)]
#[ensures(!result ==> k >= 10u32)]
pub fn more(k: u32) -> bool { k < 10 }

#[ensures(result == 10u32)]
pub fn go() -> u32 {
    let mut i = 0u32;
    #[invariant(i <= 10u32)]
    while more(i) {
        if small(i) { i += 1; }
    }
    i
}
