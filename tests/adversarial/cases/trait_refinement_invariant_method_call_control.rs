//@ expect: verify
//@ xfail: a true refinement that rests on a one-field struct's type invariant is refuted. The
//@ xfail: impl's `x.invariant()` is read as the definition rustc resolves it to, and that body's
//@ xfail: `self.0@` on the one-field PositiveU32 is read as `self@`, a view no fact relates to the
//@ xfail: field; the invariant premise the refinement adds for the argument does not reach it
//@ xfail: either. Both directions are reported FAILED with a counterexample (`PositiveU32(0)`)
//@ xfail: the invariant excludes. The same shapes over a two-field struct verify.
//@ xfail-verdict: failed
//@ mechanism: price control, the program of the trait_project fixture's InvariantRefinementOk
//@ mechanism: (CLI e2e test_trait_refinement_invariant_positive_verifies). PositiveU32's invariant
//@ mechanism: holds of every argument, so the trait's `true` implies the impl's `x.invariant()`,
//@ mechanism: and the argument the impl returns keeps the invariant the trait's
//@ mechanism: `result.invariant()` promises. Before the refinement read a clause's calls through
//@ mechanism: rustc's resolution, the scope closure refused this clause (exit 2). Its field
//@ mechanism: spelling is trait_refinement_invariant_field_spelling_control.
//@ fixed-by: n/a (control; open)
//@ accept-means: n/a (control)
//@ teeth: n/a (price control; measured FAILED in both directions on the campaign head)
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

pub trait InvariantRefinement {
    #[requires(true)]
    #[ensures(result.invariant())]
    fn keep(&self, x: PositiveU32) -> PositiveU32;
}

pub struct InvariantRefinementOk;

impl InvariantRefinement for InvariantRefinementOk {
    #[requires(x.invariant())]
    fn keep(&self, x: PositiveU32) -> PositiveU32 {
        x
    }
}
