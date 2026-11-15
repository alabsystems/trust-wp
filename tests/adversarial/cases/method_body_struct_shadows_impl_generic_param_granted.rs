//@ expect: reject
//@ mechanism: the generic parameter is the IMPL's: `impl<W: Tr> Holder<W>` has a method whose body
//@ mechanism: declares a struct `W`, and the method's contract calls `W::k()`. The method's body is
//@ mechanism: nearer the clause than the impl's generics, so Rust reads the struct's inherent `k`
//@ mechanism: (0). The resolver finds `W` among the generics of the method's parent, reads Tr's
//@ mechanism: declaration (10), and the method, which returns 10, is credited.
//@ fixed-by: D-198 — a generic parameter's name is read as the parameter only where no block
//@ fixed-by: between the clause and the item that declares it binds the name
//@ fixed-by: (`identity::visible_generic_type_param`, `block_scope::lookup_within`); otherwise the
//@ fixed-by: scope lookup reads it, or it is refused.
//@ accept-means: `m` claims `result@ == W::k()` with Rust's `W` the body's struct (0), returns 10, and
//@ accept-means: the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`Holder::<W>::m verified ✓`) with D-197 in force.
//@ teeth: With D-198: `Holder::<W>::m FAILED ✗ (postcondition)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[ensures(result == 10)]
    fn k() -> Int;
}

pub struct Holder<W>(W);

impl<W: Tr> Holder<W> {
    #[ensures(result@ == W::k())]
    pub fn m(&self) -> u32 {
        struct W;
        impl W {
            #[logic(open)]
            fn k() -> Int {
                pearlite! { 0 }
            }
        }
        10
    }
}
