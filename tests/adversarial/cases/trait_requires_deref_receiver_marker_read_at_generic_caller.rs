//@ expect: reject
//@ mechanism: `Api`'s `requires(!self.m())` is written where `Self: Tr` is not known, so rustc's method
//@ mechanism: probe reads it through the `Deref<Target = W>` supertrait: `<W as Tr>::m(&**self)`. The callee
//@ mechanism: text path keeps only the trait method rustc resolved (`SpecCalls::trait_method_resolved`:
//@ mechanism: `Tr::m`, the resolved `Self` dropped) in a generic marker over the parameter `Self`. At
//@ mechanism: `caller`, whose `U: Api + Tr` is its own parameter, `instantiated_marker` makes it the
//@ mechanism: declaration `Tr::m` at `U`, and `caller`'s own `requires(!u.m())` (rustc reads that one at
//@ mechanism: `U`) discharges it. The impl-`Self` spelling is
//@ mechanism: trait_requires_deref_receiver_marker_read_at_impl_self.rs.
//@ accept-means: a call is credited whose precondition, as Rust reads it, is false.
//@ WHY IT IS FALSE: `g`'s precondition is `!<W as Tr>::m(..)`, `false` whatever `U` is, and `caller`'s
//@ WHY IT IS FALSE: precondition says nothing about `W`; Creusot's `vc_caller` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0 (`caller verified ✓`; the call-site trace prints `marker=0 ->
//@ teeth: Tr::m`, the declaration) with D-163 and D-164 in force, and at the campaign tip.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means a generic marker is written only
//@ fixed-by: where rustc resolved the call with its `Self` equal to the generic parameter the marker is
//@ fixed-by: instantiated at, and the call is refused otherwise.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::ops::Deref;

pub trait Tr {
    #[logic]
    fn m(&self) -> bool;
}
pub struct W;
impl Tr for W {
    #[logic(open)]
    fn m(&self) -> bool {
        true
    }
}

pub trait Api: Deref<Target = W> {
    #[requires(!self.m())]
    fn g(&self);
}

#[requires(!u.m())]
pub fn caller<U: Api + Tr>(u: U) {
    u.g();
}
