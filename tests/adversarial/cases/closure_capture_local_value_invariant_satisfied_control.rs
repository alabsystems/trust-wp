//@ expect: verify
//@ mechanism: the TRUE twin of closure_capture_local_value_invariant_free_grant_proof_assert:
//@ mechanism: identical but for the captured value actually satisfying the invariant. It
//@ mechanism: verifies TODAY for the wrong reason — the premise is free either way — and its
//@ mechanism: job is to be the thing the fix must NOT break: once the closure's construction
//@ mechanism: site owes `inv(capture)`, this obligation is dischargeable at a value the
//@ mechanism: enclosing function built and its RED twins are not. A fix that refuses both is
//@ mechanism: a blanket refusal, not a fix.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{invariant::*, prelude::*};

pub struct Zero(pub u32, pub u32);

impl Invariant for Zero {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ == 0 }
    }
}

pub fn f() {
    let x = Zero(0, 1);
    let clos = #[ensures(result@ == 0)]
    || {
        proof_assert!(x.0@ == 0);
        (*&x).0
    };
    clos();
}
