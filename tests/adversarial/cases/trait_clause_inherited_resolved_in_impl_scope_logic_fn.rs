//@ expect: reject
//@ fn-failed: <i::W as t::Tr>::m
//@ mechanism: a trait method's clause is written in the TRAIT's module, and an impl method without a
//@ mechanism: contract of its own is verified against it; trust-wp resolves the inherited clause's
//@ mechanism: names in the IMPL method's scope instead (the owner passed to the logic-identity
//@ mechanism: resolver and to name lookup is the impl method). The refinement check already refuses
//@ mechanism: such scope-dependent clauses ("refinement is not checked on scope-dependent names"),
//@ mechanism: but the impl's own VC is granted `verified` on the impl-scope reading.
//@ mechanism: Here the scope-dependent name is a logic function: `k` is `a::k` in the trait's
//@ mechanism: module and `b::k` in the impl's.
//@ accept-means: the impl method was credited on the inherited clause read with the impl
//@ accept-means: module's `k`.
//@ WHY THE CONTRACT IS FALSE: the inherited clause is `result@ == a::k(x@)`, i.e. `result == x`,
//@ WHY THE CONTRACT IS FALSE: and `W.m(1)` returns 0.
//@ fixed-by: D-110 — an inherited clause is restated as the trait method's granted text, resolved in
//@ fixed-by: the trait's scope (trait_inherited_clause_scope_dependent_name_granted); the impl FAILS.
//@ teeth: `<i::W as t::Tr>::m verified` at the reviewed head (the same impl returning 5 is
//@ teeth: FAILED, so the clause IS in the impl's VC).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k(p: Int) -> Int { p }
}
pub mod b {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k(_p: Int) -> Int { 0 }
}
pub mod t {
    use creusot_std::prelude::*;
    use super::a::k;
    pub trait Tr {
        #[ensures(result@ == k(x@))]
        fn m(&self, x: u32) -> u32;
    }
}
pub mod i {
    use creusot_std::prelude::*;
    use super::b::k;
    use super::t::Tr;
    pub struct W;
    impl Tr for W {
        fn m(&self, x: u32) -> u32 { 0 }
    }
}
