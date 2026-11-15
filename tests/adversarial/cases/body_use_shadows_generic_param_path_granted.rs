//@ expect: reject
//@ mechanism: `f<W: Tr>` imports the crate's `Z` as `W` in its own body (`use crate::Z as W;`), and
//@ mechanism: its contract calls `W::k()`. An import in the body shadows the generic parameter as a
//@ mechanism: body item does, and the clause stands at the top of the body, so Rust reads `W::k()`
//@ mechanism: as `Z::k` (0). The resolver asks whether `W` names a generic parameter before it asks
//@ mechanism: the block scopes, reads Tr's declaration, whose `ensures` says 10, and `f`, which
//@ mechanism: returns 10, is credited.
//@ fixed-by: D-198 — a generic parameter's name is read as the parameter only where no block
//@ fixed-by: between the clause and the item that declares it binds the name
//@ fixed-by: (`identity::visible_generic_type_param`, `block_scope::lookup_within`); otherwise the
//@ fixed-by: scope lookup reads it, or it is refused.
//@ accept-means: `f` claims `result@ == W::k()` with Rust's `W` the imported `Z` (0), returns 10, and
//@ accept-means: the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-197 in force.
//@ teeth: With D-198: `f FAILED ✗ (postcondition)`: `W::k()` is `Z::k`.
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

pub struct Z;
impl Z {
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 0 }
    }
}

#[ensures(result@ == W::k())]
pub fn f<W: Tr>() -> u32 {
    use crate::Z as W;
    10
}
