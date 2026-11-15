//@ expect: reject
//@ mechanism: a trait method's clause is written in the TRAIT's module, and an impl method without a
//@ mechanism: contract of its own is verified against it; trust-wp resolves the inherited clause's
//@ mechanism: names in the IMPL method's scope instead (the owner passed to the logic-identity
//@ mechanism: resolver and to name lookup is the impl method). The refinement check already refuses
//@ mechanism: such scope-dependent clauses ("refinement is not checked on scope-dependent names"),
//@ mechanism: but the impl's own VC is granted `verified` on the impl-scope reading.
//@ mechanism: Here the scope-dependent name is a unit struct receiver (D-172): `S` is `t::S` in the
//@ mechanism: trait's module and `i::S` in the impl's.
//@ accept-means: the impl method was credited on the inherited clause read with the impl
//@ accept-means: module's `S`.
//@ WHY THE CONTRACT IS FALSE: the inherited clause is `result@ == t::S.v()`, which is 1, and
//@ WHY THE CONTRACT IS FALSE: `W.m()` returns 0.
//@ fixed-by: D-178 — for an owner that inherits its trait method's clauses, unit_struct_value_type
//@ fixed-by: types `S` only where the trait method's scope gives the same answer; here the two
//@ fixed-by: disagree, so the receiver has no type and the impl is refused, not credited. Reading the
//@ fixed-by: clause in the trait's scope is the trait-logic-impl front's restating of inherited
//@ fixed-by: clauses (trait_inherited_clause_scope_dependent_name_granted).
//@ teeth: `<i::W as t::Tr>::m verified` at the head that introduced D-172 (the same impl returning
//@ teeth: 5 is FAILED, so the clause IS in the impl's VC); refused before D-172 typed the receiver.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait V {
    #[logic]
    fn v(self) -> Int;
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
    use creusot_std::prelude::*;
    pub struct S;
    impl super::V for S {
        #[logic(open)]
        fn v(self) -> Int { 0 }
    }
    use super::t::Tr;
    pub struct W;
    impl Tr for W {
        fn m(&self) -> u32 { 0 }
    }
}
