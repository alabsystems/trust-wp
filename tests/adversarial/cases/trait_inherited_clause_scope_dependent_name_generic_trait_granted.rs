//@ expect: reject
//@ verdict: failed
//@ fn-failed: <b::W as a::Rd<u8>>::rd
//@ mechanism: the GENERIC-trait spelling of trait_inherited_clause_scope_dependent_name_granted.rs. `W`
//@ mechanism: implements `Rd<u8>` and inherits `result@ == k()`; every caller is handed it in the trait's
//@ mechanism: module (`a::k`, 0) and the body was held to it in the impl's module (`b::k`, 10). The
//@ mechanism: restatement instantiates the trait's call-site spec at the impl's trait arguments, so this
//@ mechanism: spelling exercises that instantiation where the trait has parameters of its own.
//@ fixed-by: D-110
//@ accept-means: `go` claims `result@ == 0` and returns 10; `gen_read` claims it for every `T: Rd<U>`, `W` at `u8` included.
//@ teeth: MEASURED at the parent of D-110: `<b::W as a::Rd<u8>>::rd verified ✓`, `go verified ✓` and `gen_read verified ✓` beside the refinement refusal, with no withdrawal. At the fix the body owes `a::k`, fails, and both callers are withdrawn. The isolating twin trait_inherited_clause_scope_dependent_name_generic_trait_honoured_twin.rs (returning 0) verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 0 }
    }
    pub trait Rd<T> {
        #[ensures(result@ == k())]
        fn rd(&self, t: T) -> u32;
    }
}

pub mod b {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 10 }
    }
    pub struct W;
    impl super::a::Rd<u8> for W {
        fn rd(&self, t: u8) -> u32 {
            10
        }
    }
}

use a::Rd;

#[ensures(result@ == 0)]
pub fn go() -> u32 {
    b::W.rd(1u8)
}

#[ensures(result@ == 0)]
pub fn gen_read<U, T: Rd<U>>(t: &T, u: U) -> u32 {
    t.rd(u)
}
