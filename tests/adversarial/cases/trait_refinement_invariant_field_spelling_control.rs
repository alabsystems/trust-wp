//@ expect: verify
//@ xfail: the refinement check refutes a true refinement that rests on an argument's type
//@ xfail: invariant: the impl's `requires(x.0@ > 0)` is what PositiveU32's invariant says of every
//@ xfail: argument, and the trait requires `true`, yet `trait precondition implies impl
//@ xfail: precondition` is reported FAILED. `x.0@` on the one-field PositiveU32 is read as `x@`, a
//@ xfail: view no fact relates to the field, so the invariant premise the refinement adds for the
//@ xfail: argument cannot reach the goal. The same shape over a two-field struct verifies.
//@ xfail-verdict: failed
//@ mechanism: the field spelling of trait_refinement_invariant_method_call_control; it names no
//@ mechanism: method, so it reached the goal even while the scope closure refused the method
//@ mechanism: spelling, and it was refuted then as now.
//@ fixed-by: n/a (control; open)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; measured FAILED on the campaign head)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct PositiveU32(pub u32);

impl Invariant for PositiveU32 {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ > 0 }
    }
}

pub trait FieldRefinement {
    #[requires(true)]
    fn keep(&self, x: PositiveU32) -> PositiveU32;
}

pub struct FieldOk;

impl FieldRefinement for FieldOk {
    #[requires(x.0@ > 0)]
    fn keep(&self, x: PositiveU32) -> PositiveU32 {
        x
    }
}
