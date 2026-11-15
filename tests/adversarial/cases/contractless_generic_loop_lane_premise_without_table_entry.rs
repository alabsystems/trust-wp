//@ expect: reject
//@ also-verified: via, <Sum10 as Total>::total
//@ mechanism: D-141 skips a spec-table entry for a body whose only clauses are type-parameter
//@ mechanism: invariants and states that such a body "holds no premise either — both sides read
//@ mechanism: here". The loop lane does not read there: `verify_contract_loop_path` merges
//@ mechanism: `build_type_invariant_clauses` into the loop's base requires directly, and so do the
//@ mechanism: recursive-variant lane and the proof_assert lane. Contract-free `via<T>` is therefore
//@ mechanism: verified holding `inv_T(t)`, which discharges its loop hop into the impl, while no
//@ mechanism: call to it owes anything: a call to a body with no entry is the fail-closed opaque
//@ mechanism: lane, and a contract-free caller is a target for the grant the TABLE holds, which here
//@ mechanism: is nothing, so `hop` is examined by nothing.
//@ accept-means: a crate reported verified breaks the loop invariant of a function it credits.
//@ WHY THE PROGRAM IS WRONG: `hop()` hands `via` a `Sum10` with `a + b == 2`: the impl returns 2,
//@ WHY THE PROGRAM IS WRONG: and `via`'s invariant `r@ == 10` is false after the first iteration.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means every lane reads the premise
//@ fixed-by: from the spec-table vector the call sites owe, and a contract-free caller of a body
//@ fixed-by: granted a parameter invariant is a verification target.
//@ teeth: MEASURED ACCEPTED, exit 0, on the current build and on the build before D-141, where the
//@ teeth: loop lane charged no grant at the hop at all; D-141 made it charge, and the premise it
//@ teeth: discharges the charge with is one no call owes.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Sum10 {
    pub a: i32,
    pub b: i32,
}

impl Invariant for Sum10 {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ == 10 }
    }
}

pub trait Total {
    #[ensures(result@ == 10)]
    fn total(&self) -> i32;
}

impl Total for Sum10 {
    fn total(&self) -> i32 {
        self.a + self.b
    }
}

pub fn via<T: Total>(t: T, n: u32) -> i32 {
    let mut r = 10;
    let mut i = 0;
    #[invariant(r@ == 10)]
    while i < n {
        r = t.total();
        i += 1;
    }
    r
}

pub fn hop() -> i32 {
    via(Sum10 { a: 1, b: 1 }, 1)
}
