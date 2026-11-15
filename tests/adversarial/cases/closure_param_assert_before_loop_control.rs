//@ expect: verify
//@ mechanism: control for closure_param_loop_write_assertion_stale_entry_fact: the same closure with the assertion placed BEFORE the loop, where the entry fact still holds. The guard drops a fact only at a program point a loop's write reaches, so naming the closure's parameters correctly must not cost this.
//@ accept-means: n/a (control) — the assertion holds at entry.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn parent() {
    let c = #[requires((*y)@ == 7)]
    #[ensures(true)]
    |y: &mut u32| {
        proof_assert!((*y)@ == 7);
        let mut i = 0u32;
        #[invariant(i@ <= 1)]
        while i < 1 {
            *y = 3;
            i += 1;
        }
    };
    let _ = c;
}
