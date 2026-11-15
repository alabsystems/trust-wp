//@ expect: verify
//@ mechanism: the same abstract-receiver hop over a law the only impl genuinely HONOURS (`bumped(self) = self@ + 1int`, so `bumped == base + 1` really holds). Neutralization strips the unproved law to a bare declaration, the solver models it as FALSE, and trust-wp published that model as `hop FAILED ✗ (postcondition)` — a counterexample to a contract that is true.
//@ accept-means: n/a (control): the only impl establishes the grant, so `hop` must verify. A `failed` is the false counterexample coming back; an `unknown (refutation withheld: ...)` is the discharge refusing the grant's clause again.
//@ fixed-by: D-156 — the discharge reads the grant's `self.base()` at the impl as `<i32 as Spec>::base`, so `<i32 as Spec>::bumped` establishes it and `hop` rests on a discharged grant
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
    fn bumped(self) -> Int { pearlite! { self@ + 1int } }
}
#[requires(v@ == t.bumped())]
#[ensures(result@ == t.base() + 1int)]
pub fn hop<T: Spec>(t: T, v: i32) -> i32 { v }
