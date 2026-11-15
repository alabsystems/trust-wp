//@ expect: reject
//@ verdict: failed
//@ fn-failed: <b::W as a::Rd>::rd
//@ mechanism: the glob-import spelling of trait_inherited_clause_scope_dependent_name_granted.rs.
//@ mechanism: The trait's module sees `k` only through `use crate::x::*` (x's `k` is 0); the impl's
//@ mechanism: module declares its own `k` (10). An impl that declares no clauses inherits
//@ mechanism: `result@ == k()`, which Rust resolves in the trait's module to `x::k`. The restated
//@ mechanism: grant (D-110) must find the glob-imported name there, so the body owes `x::k` and every
//@ mechanism: caller is handed `x::k`; read in the impl's module the body owed `b::k`.
//@ fixed-by: D-110 (an inherited contract is restated as the trait method's call-site spec, resolved in the trait's scope)
//@ accept-means: `go` claims `result@ == 0` and returns 10; `gen_read` claims it for every `T: Rd`, W included.
//@ teeth: MEASURED before D-110: `<b::W as a::Rd>::rd verified ✓`, `go verified ✓` and `gen_read verified ✓`, rejected only by the refinement check's refusal of `k(..)`. At D-110: the body is refuted and both callers are withdrawn. The isolating twin trait_inherited_clause_glob_import_name_honoured_twin.rs (returns 0) verifies at D-110 and was refuted before it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod x {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k() -> Int {
        pearlite! { 0 }
    }
}

pub mod a {
    #[allow(unused_imports)]
    use creusot_std::prelude::*;
    #[allow(unused_imports)]
    use crate::x::*;
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
    // No clauses of its own: inherits `result@ == k()`.
    impl super::a::Rd for W {
        fn rd(&self) -> u32 {
            10
        }
    }
}

use a::Rd;

#[ensures(result@ == 0)]
pub fn go() -> u32 {
    b::W.rd()
}

#[ensures(result@ == 0)]
pub fn gen_read<T: Rd>(t: &T) -> u32 {
    t.rd()
}
