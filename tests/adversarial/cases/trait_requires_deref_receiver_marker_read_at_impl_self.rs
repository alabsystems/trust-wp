//@ expect: reject
//@ mechanism: `Api`'s `requires(!self.m())` is written where `Self: Tr` is not known, so rustc's method
//@ mechanism: probe reads it through the `Deref<Target = W>` supertrait: `<W as Tr>::m(&**self)`. The callee
//@ mechanism: text path (`identity_typed::resolve_family_calls_in_text`) types the receiver as the generic
//@ mechanism: `Self`, and asks rustc's type check only which trait METHOD the call resolved to
//@ mechanism: (`SpecCalls::trait_method_resolved`): `Tr::m`, the resolved `Self` (`W`) dropped. The generic
//@ mechanism: marker it writes carries that declaration and the parameter `Self`, and
//@ mechanism: `instantiate_generic_markers` instantiates it at the impl's `Self = Z` to `<Z as Tr>::m`, which
//@ mechanism: implements that declaration, so D-163's check that the instance implements the method rustc
//@ mechanism: resolved passes. `caller` owes `!<Z as Tr>::m(z)`, which is `true`.
//@ accept-means: a call is credited whose precondition, as Rust reads it, is false.
//@ WHY IT IS FALSE: `<W as Tr>::m` is `true`, so the precondition `z.g()` owes is `false` for every `z`;
//@ WHY IT IS FALSE: Creusot's `vc_caller` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0 (`caller verified ✓`; the call-site trace prints `marker=0 ->
//@ teeth: <Z as Tr>::m`) with D-163 and D-164 in force, and at the campaign tip, whose marker carried no
//@ teeth: resolution at all.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means a generic marker is written only
//@ fixed-by: where rustc resolved the call with its `Self` equal to the generic parameter the marker is
//@ fixed-by: instantiated at, and the call is refused otherwise.
//@ also-verified: <Z as Api>::g
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
pub struct Z;
impl Tr for W {
    #[logic(open)]
    fn m(&self) -> bool {
        true
    }
}
impl Tr for Z {
    #[logic(open)]
    fn m(&self) -> bool {
        false
    }
}
impl Deref for Z {
    type Target = W;
    fn deref(&self) -> &W {
        &W
    }
}

pub trait Api: Deref<Target = W> {
    #[requires(!self.m())]
    fn g(&self);
}

impl Api for Z {
    fn g(&self) {}
}

pub fn caller(z: Z) {
    z.g();
}
