//@ expect: reject
//@ verdict: unknown
//@ mechanism: `I` has an INHERENT logic method `ok` (`true`) beside its `Inner` impl of `ok`
//@ mechanism: (`false`). In the trait's clause `inner.ok()` with `inner: Self::In` names `Inner::ok`:
//@ mechanism: nothing else is visible at an associated type bounded by `Inner`. Instantiated at `O`
//@ mechanism: it is `<I as Inner>::ok`, so `<O as Outer>::holds` owes `true ==> false` and fails.
//@ mechanism: A method call written at `I` would pick the inherent `ok` instead: an obligation read
//@ mechanism: by re-resolving the call's spelling at the impl proves `true ==> true` and hands `uses_grant`
//@ mechanism: a grant that is false at `O`.
//@ fixed-by: D-156 (the declaration is instantiated by rustc's instance resolution of the trait item, never by a receiver-style lookup)
//@ accept-means: `uses_grant` claims `o.holds(i) ==> i.ok()` (the trait's `ok`) for every `T: Outer`; at `T = O` the trait's `ok` is `false`.
//@ teeth: MEASURED with a local knock-out that instantiated the declaration by the receiver type's
//@ teeth: inherent item first: ACCEPTED, `<O as Outer>::holds establishes the postcondition` and
//@ teeth: `uses_grant verified ✓`. Without the knock-out, `<O as Outer>::holds FAILED`.
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

impl I {
    #[logic(open)]
    pub fn ok(self) -> bool {
        pearlite! { true }
    }
}

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
