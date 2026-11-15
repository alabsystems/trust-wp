//@ expect: reject
//@ mechanism: `f<W: Tr>` declares a struct `W` in its own body, and its contract calls `W::k()`. Rust
//@ mechanism: resolves a name innermost first: the body's items shadow the function's generic
//@ mechanism: parameters (`W::only_struct()` compiles in that body, `W::k` on the parameter does
//@ mechanism: not), and Creusot and the type-check vehicle place the clause at the top of the body,
//@ mechanism: so `W::k()` is the struct's inherent logic `k` (0). The resolver asks whether `W`
//@ mechanism: names a generic parameter BEFORE it asks the block scopes, reads Tr's declaration,
//@ mechanism: whose `ensures` says 10, and `f`, which returns 10, is credited.
//@ fixed-by: D-198 — a generic parameter's name is read as the parameter only where no block
//@ fixed-by: between the clause and the item that declares it binds the name
//@ fixed-by: (`identity::visible_generic_type_param`, `block_scope::lookup_within`); otherwise the
//@ fixed-by: scope lookup reads it, or it is refused.
//@ accept-means: `f` claims `result@ == W::k()` with Rust's `W` the body's struct (0), returns 10, and
//@ accept-means: the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-197 in force.
//@ teeth: With D-198: `f FAILED ✗ (postcondition)`: `W::k()` is the struct's `k`.
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

#[ensures(result@ == W::k())]
pub fn f<W: Tr>() -> u32 {
    struct W;
    impl W {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
    }
    10
}
