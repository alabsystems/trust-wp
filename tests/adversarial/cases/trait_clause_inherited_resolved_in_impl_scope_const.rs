//@ expect: reject
//@ verdict: unknown
//@ refused-with: ambiguous__constant__K
//@ mechanism: a trait method's clause is written in the TRAIT's module, and an impl method without a
//@ mechanism: contract of its own is verified against it; trust-wp resolves the inherited clause's
//@ mechanism: names in the IMPL method's scope instead (the owner passed to the logic-identity
//@ mechanism: resolver and to name lookup is the impl method). The refinement check already refuses
//@ mechanism: such scope-dependent clauses ("refinement is not checked on scope-dependent names"),
//@ mechanism: but the impl's own VC is granted `verified` on the impl-scope reading.
//@ mechanism: Here the scope-dependent name is a `const`: `K` is `t::K` in the trait's module and
//@ mechanism: `i::K` in the impl's.
//@ accept-means: the impl method was credited on the inherited clause read with the impl
//@ accept-means: module's `K`.
//@ WHY THE CONTRACT IS FALSE: the inherited clause is `result == t::K`, which is 1, and `W.m()`
//@ WHY THE CONTRACT IS FALSE: returns 0.
//@ fixed-by: D-111 — the crate gives the bare `K` two meanings (`t::K` and `i::K`), so no clause is
//@ fixed-by: given a value for it: the inherited clause is refused in the impl's lane.
//@ teeth: `<i::W as t::Tr>::m verified` at the reviewed head (the same impl returning 5 is
//@ teeth: FAILED, so the clause IS in the impl's VC).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub mod t {
    use creusot_std::prelude::*;
    pub const K: u32 = 1;
    pub trait Tr {
        #[ensures(result == K)]
        fn m(&self) -> u32;
    }
}
pub mod i {
    use creusot_std::prelude::*;
    pub const K: u32 = 0;
    use super::t::Tr;
    pub struct W;
    impl Tr for W {
        fn m(&self) -> u32 { 0 }
    }
}
