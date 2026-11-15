//@ expect: verify
//@ mechanism: control for trait_refinement_invariant_two_field_claims_strict: the shapes of
//@ mechanism: trait_refinement_invariant_method_call_control and _field_spelling_control over a
//@ mechanism: two-field struct. The argument's invariant `lo <= hi` holds of every argument, so the
//@ mechanism: trait's `true` implies either spelling of it in the impl's `requires`, and the
//@ mechanism: argument the impl returns keeps the invariant the trait's `result.invariant()`
//@ mechanism: promises. It verifies where the one-field spellings are refuted, so the refinement's
//@ mechanism: invariant parity holds and the one-field struct's field read is what those lose.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Range {
    pub lo: u32,
    pub hi: u32,
}

impl Invariant for Range {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.lo@ <= self.hi@ }
    }
}

pub trait RangeRefinement {
    #[requires(true)]
    #[ensures(result.invariant())]
    fn keep(&self, x: Range) -> Range;
}

pub struct RangeMethodOk;

impl RangeRefinement for RangeMethodOk {
    #[requires(x.invariant())]
    fn keep(&self, x: Range) -> Range {
        x
    }
}

pub struct RangeFieldOk;

impl RangeRefinement for RangeFieldOk {
    #[requires(x.lo@ <= x.hi@)]
    fn keep(&self, x: Range) -> Range {
        x
    }
}
