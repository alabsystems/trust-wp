//@ expect: reject
//@ fn-failed: <i::W as t::Tr>::m
//@ mechanism: the body-local spelling of trait_clause_inherited_resolved_in_impl_scope_unit_struct.
//@ mechanism: The trait's clause `result@ == S.v()` is written in module `t`, where `S` is the unit
//@ mechanism: struct `t::S`. The impl in module `i` writes no clause, so it is verified against
//@ mechanism: that text, and its body binds a local `S: u32`. The logic-identity resolver types a
//@ mechanism: receiver that names a body local of the OWNER before it asks for a unit struct
//@ mechanism: (`Resolver::receiver_type`), and the owner of an inherited clause is the impl method,
//@ mechanism: so `S.v()` is dispatched to `<u32 as V>::v` instead of `<t::S as V>::v`. D-178
//@ mechanism: guards only the unit-struct lookup, which this reading never reaches. No
//@ mechanism: `requires`/`ensures` can mean a `let` of the body by a bare name: a clause is
//@ mechanism: type-checked at the head of its own owner's body, and an inherited one was not
//@ mechanism: type-checked in the impl's body at all.
//@ accept-means: the impl method was credited on the inherited clause read with the impl body's local
//@ accept-means: `S` as the receiver.
//@ WHY THE CONTRACT IS FALSE: the inherited clause is `result@ == <t::S as V>::v(t::S)`, which is 1,
//@ WHY THE CONTRACT IS FALSE: and `W.m()` returns 0.
//@ fixed-by: D-110 — an inherited clause is restated as the trait method's granted text, resolved in
//@ fixed-by: the trait's scope (trait_inherited_clause_scope_dependent_name_granted); the impl FAILS.
//@ teeth: `<i::W as t::Tr>::m verified` at the reviewed head, and with the driver crate checked out
//@ teeth: at the campaign base in place. The isolating twin
//@ teeth: trait_clause_inherited_resolved_in_impl_scope_body_local_control.rs returns 1 and FAILS on
//@ teeth: `result@ == <u32 as V>::v(S)`, so the receiver IS read as the body local.
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
        fn m(&self) -> u32 { let S = 0u32; S }
    }
}
