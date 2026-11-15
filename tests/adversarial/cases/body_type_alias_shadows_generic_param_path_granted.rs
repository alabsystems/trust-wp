//@ expect: reject
//@ mechanism: `f<W: Tr>` declares a type alias `type W = crate::Z;` in its own body, and its contract
//@ mechanism: calls `W::k()`. The alias shadows the generic parameter at the top of the body, so Rust
//@ mechanism: reads `W::k()` as `Z::k` (0). The resolver asks whether `W` names a generic parameter
//@ mechanism: before it asks the block scopes, reads Tr's declaration (10), and `f`, which returns
//@ mechanism: 10, is credited.
//@ fixed-by: D-198 — a generic parameter's name is read as the parameter only where no block
//@ fixed-by: between the clause and the item that declares it binds the name
//@ fixed-by: (`identity::visible_generic_type_param`, `block_scope::lookup_within`); otherwise the
//@ fixed-by: scope lookup reads it, or it is refused.
//@ accept-means: `f` claims `result@ == W::k()` with Rust's `W` the alias of `Z` (0), returns 10, and
//@ accept-means: the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-197 in force.
//@ teeth: With D-198: REFUSED (`unknown`): the alias is not an ADT the resolver reads, and `W::k` is
//@ teeth: left unresolved.
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
    type W = crate::Z;
    10
}
