//@ expect: reject
//@ verdict: unknown
//@ mechanism: an impl that DECLARES its own clause with the same text as its trait method's,
//@ mechanism: `result@ == k()`, in a module where `k()` means something else: `b::k` (10) for the impl,
//@ mechanism: `a::k` (0) for the trait. The body honours its own clause (returns 10) and generic callers
//@ mechanism: are handed the trait's. Only the refinement check stands between the two contracts, and
//@ mechanism: it refused the pair on the scope-dependent name; the verbatim exemption, which compared
//@ mechanism: clause TEXT, then dropped that refusal for an impl that had declared rather than inherited
//@ mechanism: its clauses, so `gen_read` kept the trait's grant through an impl that never established it.
//@ fixed-by: D-110 (the verbatim exemption is gone: every refinement refusal records the impl undischarged)
//@ accept-means: `gen_read` claims `result@ == 0` for every `T: Rd`; at `T = b::W` it returns 10, and `go_generic` claims the same through it.
//@ teeth: MEASURED at the parent of D-110: `gen_read verified ✓` and `go_generic verified ✓` beside the refinement refusal, with no withdrawal. At the fix both are withdrawn. The impl's own `verified ✓` is TRUE (it returns its own `b::k`). There is no twin that verifies today: the refinement check refuses every clause naming a logic function, so trait_own_clause_equal_text_same_scope_control.rs (one `k` in the crate) is the xfail control that carries this price.
//@ also-verified: <b::W as a::Rd>::rd
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
    pub trait Rd {
        #[ensures(result@ == k())]
        fn rd(&self) -> u32;
    }
}

pub mod b {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 10 }
    }
    pub struct W;
    impl super::a::Rd for W {
        #[ensures(result@ == k())]
        fn rd(&self) -> u32 {
            10
        }
    }
}

use a::Rd;

#[ensures(result@ == 0)]
pub fn gen_read<T: Rd>(t: &T) -> u32 {
    t.rd()
}

#[ensures(result@ == 0)]
pub fn go_generic() -> u32 {
    gen_read(&b::W)
}
