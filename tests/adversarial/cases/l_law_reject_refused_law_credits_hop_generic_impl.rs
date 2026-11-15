//@ expect: reject
//@ mechanism: the grant `result == self.base() + 1int` owed by a GENERIC impl (`impl<U> Spec for W<U>`). Its `self.base()` has a receiver whose type still carries a parameter, so the discharge cannot read it at the impl and it stays the declaration at an abstract `Self`: the discharge dies of an encoding refusal. The refusal must withdraw the grant, exactly as a refutation does, so `hop` rests on nothing.
//@ accept-means: an `#[ensures]` nobody proved is still available to callers. At `T = W<i32>` the impl makes `base` and `bumped` both 0, so `hop(W(5), 0)` is admitted (`0 == bumped`) and returns 0 while the contract demands `0 == base + 1 == 1`.
//@ teeth: the twin of l_law_reject_refused_law_credits_hop at a concrete impl, whose grant D-156 now reads at the impl and refutes; this case keeps the refusal arm itself under test.
//@ verdict: unknown
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
pub struct W<U>(pub U);
impl<U> Spec for W<U> {
    #[logic(open)]
    fn base(self) -> Int { pearlite! { 0 } }
    #[logic(open)]
    fn bumped(self) -> Int { pearlite! { 0 } }
}
#[requires(v@ == t.bumped())]
#[ensures(result@ == t.base() + 1int)]
pub fn hop<T: Spec>(t: T, v: i32) -> i32 { v }
