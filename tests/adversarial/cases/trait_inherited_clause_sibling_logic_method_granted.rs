//@ expect: reject
//@ verdict: failed
//@ fn-failed: <W as Rd>::rd
//@ mechanism: an impl that inherits a clause naming a sibling LOGIC method at `Self`,
//@ mechanism: `result@ == self.val()`, and defines `val` as 5 while its body returns 6. The body owes
//@ mechanism: the clause restated at the impl, where `self.val()` is `<W as Rd>::val`, and fails it; `go`,
//@ mechanism: pinned to W's impl, is withdrawn. Paired with the twin to hold the refinement check of an
//@ mechanism: inherited contract to what it is: the clause is the trait's own text on both sides, so it
//@ mechanism: is a premise and never a goal, and a refinement that treated it as a goal could not tell
//@ mechanism: this crate from its twin.
//@ fixed-by: D-110
//@ accept-means: `go` claims `result@ == 5` and returns 6.
//@ teeth: none shown: no build of trust-wp has accepted it (MEASURED at the parent of D-110 and at D-110: `<W as Rd>::rd FAILED ✗ (postcondition)` and `go` withdrawn). It is the reject half of the pair whose twin shows the refinement of an inherited contract states no clause goal; what keeps this half rejected is the body obligation, which owes the restated clause.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Rd {
    #[logic]
    fn val(self) -> Int;
    #[ensures(result@ == self.val())]
    fn rd(self) -> u32;
}

pub struct W;

impl Rd for W {
    #[logic(open)]
    fn val(self) -> Int {
        pearlite! { 5 }
    }
    fn rd(self) -> u32 {
        6
    }
}

#[ensures(result@ == 5)]
pub fn go() -> u32 {
    W.rd()
}
