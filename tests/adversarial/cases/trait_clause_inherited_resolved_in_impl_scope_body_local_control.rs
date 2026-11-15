//@ expect: verify
//@ mechanism: control for trait_clause_inherited_resolved_in_impl_scope_body_local: the impl returns 1,
//@ mechanism: which is `<t::S as V>::v(t::S)`.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control. FAILED before D-110 restated the inherited clause in the
//@ teeth: trait's scope: the clause was owed as `result@ == <u32 as V>::v(S)` over the body's local.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait V {
    #[logic]
    fn v(self) -> Int;
}
impl V for u32 {
    #[logic(open)]
    fn v(self) -> Int { 0 }
}
pub mod t {
    use creusot_std::prelude::*;
    pub struct S;
    impl super::V for S {
        #[logic(open)]
        fn v(self) -> Int { 1 }
    }
    use super::V;
    pub trait Tr {
        #[ensures(result@ == S.v())]
        fn m(&self) -> u32;
    }
}
pub mod i {
    use super::t::Tr;
    pub struct W;
    impl Tr for W {
        #[allow(non_snake_case)]
        fn m(&self) -> u32 { let S = 1u32; S }
    }
}
