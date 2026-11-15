//@ expect: reject
//@ mechanism: the inherited-default rule must apply only where the impl does NOT define the item: here the impl overrides `f` with 2 and `get` returns the default's value, 1
//@ accept-means: `Self::f()` was bound to the trait's default body although the impl overrides it
//@ verdict: failed
//@ fn-failed: <() as Foo>::get
//@ teeth: demonstrated — with both override guards disabled by a local knob (`inherited_self_default`'s impl-defines check and `inherited_default`'s `Instance::try_resolve` check), this case is ACCEPTED and `inherited_default_overridden_control` FAILED; either guard alone keeps it rejected
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Foo {
    #[logic(open)]
    fn f() -> Int {
        1
    }
    fn get(&self) -> i32;
}

impl Foo for () {
    #[logic(open)]
    fn f() -> Int {
        2
    }
    // WRONG: Self::f() is this impl's f, 2; get() returns 1.
    #[ensures(result@ == Self::f())]
    fn get(&self) -> i32 {
        1
    }
}
