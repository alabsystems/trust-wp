//@ expect: verify
//@ mechanism: a trait logic method's `ensures` names a call on a receiver of an ASSOCIATED type
//@ mechanism: (`inner.ok()`, `inner: Self::In`), which the grant resolves to the declaration
//@ mechanism: `Inner::ok` (the method at an abstract `Self`). Each logic impl owes the grant (D-110);
//@ mechanism: at `O` the receiver's type is `I`, so the clause reads `<I as Inner>::ok(inner)`, the
//@ mechanism: impl rustc selects there, whose body is `true`. `<O as Outer>::holds` discharges it and
//@ mechanism: `uses_grant`, which uses the grant for every `T: Outer`, keeps its credit. The shape of
//@ mechanism: tests/should_succeed/bug/464.rs, whose impl states the trait's clause as its own.
//@ fixed-by: D-156
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control). Before D-156 the discharge refused the clause ("names call
//@ teeth: `...Inner::ok(..)`, which stands for the method at an abstract `Self`"), withdrew the grant
//@ teeth: and left `uses_grant` unknown. Its isolating twin trait_logic_decl_clause_assoc_receiver_at_impl_false.rs
//@ teeth: differs in `<I as Inner>::ok`'s body only.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Inner {
    #[logic]
    fn ok(self) -> bool;
}

pub trait Outer {
    type In: Inner;

    #[logic]
    #[ensures(result ==> inner.ok())]
    fn holds(self, inner: Self::In) -> bool;
}

pub struct I;
pub struct O;

impl Inner for I {
    #[logic(open)]
    fn ok(self) -> bool {
        pearlite! { true }
    }
}

impl Outer for O {
    type In = I;

    #[logic(open)]
    fn holds(self, _inner: I) -> bool {
        pearlite! { true }
    }
}

#[ensures(o.holds(i) ==> i.ok())]
pub fn uses_grant<T: Outer>(o: T, i: T::In) {}
