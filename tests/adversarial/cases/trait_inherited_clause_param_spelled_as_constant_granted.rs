//@ expect: reject
//@ verdict: failed
//@ fn-failed: g
//@ also-verified: <A as t::Tr>::id
//@ mechanism: a required trait method names its parameter `K`, and the crate's one constant is also
//@ mechanism: `K` (in another module). A bodyless declaration binds no pattern, so the constant table
//@ mechanism: counts one meaning for `K` and maps it to the constant's value. The inherited clause
//@ mechanism: `result == K` must still mean the parameter on both sides: the impl owes it renamed to
//@ mechanism: its own parameter `k` (the restated grant, D-110), and a generic caller is handed it with
//@ mechanism: `K` bound to the argument. Read as the constant anywhere, the grant and the obligation
//@ mechanism: part: `g` would be credited `result == 10` for a call that returns 3.
//@ fixed-by: n/a (regression guard beside D-110's renaming and D-111's constant table)
//@ accept-means: `g` claims `result == 10` and returns `x.id(3)`, which is 3; A's impl returns its argument, which is what the trait's clause says, so `<A as t::Tr>::id` is a true credit.
//@ teeth: MEASURED before D-110: rejected as here (`g FAILED`), with A's impl refuted as well, because the impl read the inherited text in its own names and `K` there was the constant. At D-110: `<A as t::Tr>::id verified ✓`, `g FAILED ✗`. The isolating twin trait_inherited_clause_param_spelled_as_constant_honoured_twin.rs claims 3 and verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(non_snake_case)]
extern crate creusot_std;
use creusot_std::prelude::*;

pub mod c {
    pub const K: i32 = 10;
}

pub mod t {
    use creusot_std::prelude::*;
    pub trait Tr {
        #[ensures(result == K)]
        fn id(&self, K: i32) -> i32;
    }
}

pub struct A;

// Inherits `result == K` over the trait's parameter, which this impl calls `k`.
impl t::Tr for A {
    fn id(&self, k: i32) -> i32 {
        k
    }
}

#[ensures(result == 10i32)]
pub fn g<T: t::Tr>(x: &T) -> i32 {
    x.id(3)
}
