//@ expect: reject
//@ mechanism: a trait law whose own postcondition check died of an ENCODING REFUSAL stayed live as a spec axiom. Verifying `Spec::bumped`'s `#[ensures]` hides every same-trait logic fn, so `base` is not registered and the clause cannot be encoded; the refusal was counted as an error but never recorded as an unverified axiom, so the unproved law still discharged `hop`.
//@ fixed-by: record the refusal on the unverified-axiom path, the sole input to downstream neutralization
//@ accept-means: an `#[ensures]` nobody proved is still available to callers, so a hop can be credited a claim its own premises do not support — at `T = i32`, where the impl makes `base` and `bumped` the identity, the contract demands `t == t + 1`
//@ teeth: `hop verified ✓` before the arm recorded the refusal; deleting the law or correcting it withdraws the credit, so it came from the law alone. Since D-156 the grant's `self.base()` is read at the impl, so the impl is refuted rather than refused and the crate's verdict is that genuine counterexample; `hop` still rests on nothing. l_law_reject_refused_law_credits_hop_generic_impl keeps the encoding refusal itself
//@ verdict: failed
//@ fn-failed: <i32 as Spec>::bumped
//@ refused-with: hop unknown (refutation withheld
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub trait Spec {
    #[logic]
    fn base(self) -> Int;
    #[logic]
    #[ensures(result == self.base() + 1int)]
    fn bumped(self) -> Int;
}
impl Spec for i32 {
    #[logic(open)]
    fn base(self) -> Int { pearlite! { self@ } }
    #[logic(open)]
    fn bumped(self) -> Int { pearlite! { self@ } }
}
#[requires(v@ == t.bumped())]
#[ensures(result@ == t.base() + 1int)]
pub fn hop<T: Spec>(t: T, v: i32) -> i32 { v }
