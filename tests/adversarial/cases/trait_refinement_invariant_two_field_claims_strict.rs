//@ expect: reject
//@ also-verified: <RangeTooStrong as RangeRefinement>::keep
//@ mechanism: a trait method requiring `true` of a two-field argument whose type invariant is
//@ mechanism: `lo <= hi`, and an impl requiring `lo < hi`. The refinement adds the argument's
//@ mechanism: invariant to the premise for parity with body verification; an invariant read as
//@ mechanism: more than it says (or a premise the impl's clause is matched against by its text)
//@ mechanism: would discharge the strengthened precondition.
//@ accept-means: an impl may require more than its trait method promises callers, because the
//@ accept-means: argument's type invariant was read as stronger than it is.
//@ WHY THE CONTRACT IS FALSE: a generic caller holding `Range { lo: 1, hi: 1 }`, which meets the
//@ WHY THE CONTRACT IS FALSE: invariant, meets the trait's `true` and calls the impl outside its
//@ WHY THE CONTRACT IS FALSE: `requires(x.lo@ < x.hi@)`.
//@ fn-failed: <RangeTooStrong as RangeRefinement>::keep trait refinement
//@ fixed-by: n/a (rejected on the campaign head; the body of `keep` returns its argument and is
//@ fixed-by: credited TRUE)
//@ teeth: its true twin RangeFieldOk (`lo <= hi`) in trait_refinement_invariant_two_field_control
//@ teeth: verifies on the same build, so the rejection is the strengthening, not the invariant.
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

pub struct RangeTooStrong;

impl RangeRefinement for RangeTooStrong {
    #[requires(x.lo@ < x.hi@)]
    fn keep(&self, x: Range) -> Range {
        x
    }
}
