//@ expect: reject
//@ mechanism: an ELIDED binder whose type rustc infers from its use: `is300` takes a `u8`, so Rust's
//@ mechanism: `exists<x> is300(x)` ranges over `u8` and is false. The contract parser has no type for
//@ mechanism: `x` to state a range from (D-203 reads a WRITTEN type), and the encoder reads it over
//@ mechanism: the unbounded integers, where `x == 300` witnesses it: ay finds the negated goal
//@ mechanism: unsatisfiable, and the claim is kept from `verified` only because that proof has a
//@ mechanism: trusted step. The honoured twin
//@ mechanism: quantifier_binder_elided_inferred_machine_int_honoured_control.rs is refuted.
//@ fixed-by: OPEN (D-205, not changed): the binder's type is known only to rustc, as the type-check
//@ fixed-by: vehicle's closure parameter.
//@ accept-means: `f` claims `result == (exists<x: u8> x@ == 300)`, which is false, returns true, and
//@ accept-means: the crate exits 0.
//@ teeth: not shown: `f unknown (quantifier-unhandled)` with D-205 in force, after `UNSAT proof has
//@ teeth: unverified fallback steps`: the unbounded reading is proved and withheld.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn is300(x: u8) -> bool {
    pearlite! { x@ == 300 }
}

#[ensures(result == (exists<x> is300(x)))]
pub fn f() -> bool {
    true
}
