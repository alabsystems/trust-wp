//@ expect: reject
//@ also-verified: f, creusot_test::<S as Tr>::k
//@ mechanism: the call-site side of body_struct_shadows_generic_param_path_granted.rs. `f<W: Tr>`
//@ mechanism: declares a struct `W` in its body and claims `result@ == W::k()`, which Rust reads as
//@ mechanism: the struct's inherent `k` (0): the clause stands at the top of the body, where the
//@ mechanism: body's items shadow the generic parameter. `f` returns 0, so its contract is TRUE. The
//@ mechanism: callee-contract resolver asks for a generic parameter before the block scopes, spells
//@ mechanism: `W::k()` as a generic marker, and the call `f::<S>()` re-resolves it to `<S as Tr>::k`
//@ mechanism: (10): `caller`, which returns `f::<S>()` (0), is credited with `result@ == 10`.
//@ fixed-by: D-198 — a generic parameter's name is read as the parameter only where no block
//@ fixed-by: between the clause and the item that declares it binds the name
//@ fixed-by: (`identity::visible_generic_type_param`, `block_scope::lookup_within`); otherwise the
//@ fixed-by: scope lookup reads it, or it is refused.
//@ accept-means: `caller` claims `result@ == 10` and returns 0; ACCEPTED means that credit is printed.
//@ teeth: MEASURED: `caller verified ✓` with D-197 in force (`f` itself refuted: its clause read at
//@ teeth: the parameter).
//@ teeth: With D-198: `f verified ✓`, `caller FAILED ✗ (postcondition)`: the callee text names the
//@ teeth: struct's `k` and no marker reaches the call site.
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

pub struct S;
impl Tr for S {
    #[logic(open)]
    #[ensures(result == 10)]
    fn k() -> Int {
        pearlite! { 10 }
    }
}

#[ensures(result@ == W::k())]
pub fn f<W: Tr>() -> u32 {
    struct W;
    impl W {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
    }
    0
}

#[ensures(result@ == 10)]
pub fn caller() -> u32 {
    f::<S>()
}
