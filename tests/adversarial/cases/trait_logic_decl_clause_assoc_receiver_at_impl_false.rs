//@ expect: reject
//@ verdict: unknown
//@ mechanism: the isolating twin of trait_logic_decl_clause_assoc_receiver_at_impl_control.rs:
//@ mechanism: `<I as Inner>::ok` is `false`. The grant `Outer::holds`'s `result ==> inner.ok()`, read
//@ mechanism: at `O`, is `true ==> <I as Inner>::ok(inner)`, which is false, so `<O as Outer>::holds`
//@ mechanism: does not discharge it, the grant is withdrawn, and `uses_grant` rests on nothing.
//@ fixed-by: D-156 (the discharge reads a declaration call at the impl as the implementation rustc selects for its receiver's type there)
//@ accept-means: `uses_grant` claims `o.holds(i) ==> i.ok()` for every `T: Outer`; at `T = O`, `o.holds(i)` is `true` and `i.ok()` is `false`.
//@ teeth: the pair isolates the instantiated obligation: the same crate with `ok`'s body `true`
//@ teeth: verifies. Before D-156 this crate was refused, not refuted (the clause named the declaration
//@ teeth: `Inner::ok`), so it was never accepted; what it pins is that the obligation read at `O` is
//@ teeth: the one the grant owes there. trait_logic_decl_clause_inherent_shadow_at_impl.rs pins
//@ teeth: WHICH `ok` that is.
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
        pearlite! { false }
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
