//@ expect: reject
//@ mechanism: a logic body calls a trait's logic method through a generic bound by its fully qualified path, `<T as Tr>::m(y)`, and the trait method requires `x > 0`. No implementation is known, so the precondition owed is the trait method's, which rustc names. Pins the generic spelling the resolution record reads (D-136); a control would differ in the caller's `requires` and fails on an encoder gap the walk does not touch (the encoder does not resolve a trait method call on a type parameter). Found probing sideways from D-120.
//@ accept-means: a generic logic function that calls a trait's logic method outside its precondition is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `caller` calls `<T as Tr>::m(0)`, and `Tr::m` requires `x > 0` of every implementation's caller.
//@ teeth: UNVERIFIED, a shape gate: rejected with D-120 open too, since the spelling `m` names the contracted trait method and D-119 item 2 owes what a spelling names; with D-136 it FAILS on the callee precondition through the resolution as well.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[requires(x > 0)]
    fn m(x: Int) -> Int;
}

#[logic]
#[ensures(true)]
pub fn caller<T: Tr>(y: Int) -> Int {
    <T as Tr>::m(y)
}
