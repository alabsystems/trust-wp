//@ expect: reject
//@ mechanism: the guarded spelling of clause_free_literal_switch_live_panic: under `x > 3` the
//@ mechanism: literal `false` selects the `unreachable!()` edge, and the enclosing switch charges
//@ mechanism: its own arm with `!(x > 3)`, which `hop(4)` refutes.
//@ accept-means: the literal rule covered a panic its literal selects.
//@ WHY THE CONTRACT IS FALSE: a clause-free `verified` claims no execution panics; `hop(4)` panics.
//@ verdict: failed
//@ fn-failed: hop
//@ teeth: UNVERIFIED for the cap — the enclosing arm's charge is refuted before the cap reads it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub fn hop(x: u32) -> u32 {
    if x > 3 {
        let c = false;
        if c {
            return 1;
        } else {
            unreachable!()
        }
    }
    x
}
