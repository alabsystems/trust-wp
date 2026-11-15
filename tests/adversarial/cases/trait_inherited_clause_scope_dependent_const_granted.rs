//@ expect: reject
//@ verdict: unknown
//@ refused-with: `__lfidU__ambiguous__constant__K` was not resolved to one definition by the driver
//@ mechanism: the constant sibling of trait_inherited_clause_scope_dependent_name_granted.rs. The trait's
//@ mechanism: clause `result == K` means `a::K` (0). Restating the inherited clause in the trait's
//@ mechanism: scope resolves logic functions, but a bare constant is substituted by short name alone,
//@ mechanism: for the grant and the body alike: both read `b::K` (10), so `<b::W as a::Rd>::rd`, which
//@ mechanism: returns 10, was credited with a contract that says 0.
//@ accept-means: `<b::W as a::Rd>::rd` claims `result == a::K`, which is 0, and returns 10.
//@ fixed-by: D-111 (a bare constant name the crate gives more than one meaning is refused wherever the table substitutes it)
//@ teeth: MEASURED before D-111: `<b::W as a::Rd>::rd verified ✓` beside `go FAILED` and `gen_read FAILED` (both read 10 for `K` as well). At the fix every clause spelling the name is refused and no function in the crate is credited on it; const_short_name_unique_control.rs, one constant spelled everywhere, verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    pub const K: u32 = 0;
    pub trait Rd {
        #[ensures(result == K)]
        fn rd(&self) -> u32;
    }
}

pub mod b {
    pub const K: u32 = 10;
    pub struct W;
    // No clauses of its own: inherits `result == K` as text.
    impl super::a::Rd for W {
        fn rd(&self) -> u32 {
            10
        }
    }
}

use a::Rd;

#[ensures(result == 0u32)]
pub fn go() -> u32 {
    b::W.rd()
}

#[ensures(result == 0u32)]
pub fn gen_read<T: Rd>(t: &T) -> u32 {
    t.rd()
}
