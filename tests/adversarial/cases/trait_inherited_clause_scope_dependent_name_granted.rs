//@ expect: reject
//@ verdict: failed
//@ fn-failed: <b::W as a::Rd>::rd
//@ mechanism: an impl that declares no clauses inherits the trait's clause TEXT, and the text was
//@ mechanism: resolved in the impl's module: `k()` in `a::Rd::rd`'s `result@ == k()` is `a::k` (0)
//@ mechanism: for every caller handed the trait contract, and was `b::k` (10) for the body obligation of
//@ mechanism: `<b::W as a::Rd>::rd`, which returns 10 and verified. The refinement check refused the
//@ mechanism: pair (`names call k(..), which cannot be resolved in the clause's own scope`), and
//@ mechanism: `verify_trait_impl_refinements` dropped a refusal on an impl whose clauses equal the
//@ mechanism: trait's verbatim, reasoning that the body obligation "was stated over exactly that
//@ mechanism: text". Equal text is not equal meaning when a name in it is scope-dependent. So nothing
//@ mechanism: was recorded, and `go` (pinned to W's impl) and `gen_read` kept a grant whose meaning
//@ mechanism: the code that runs never established.
//@ fixed-by: D-110 (an inherited contract is restated as the trait method's call-site spec, resolved in the trait's scope and instantiated at the impl; the verbatim exemption is gone)
//@ accept-means: `go` claims `result@ == 0` and returns 10; `gen_read` claims it for every `T: Rd`, W included.
//@ teeth: MEASURED at the parent commit: `<b::W as a::Rd>::rd verified ✓`, `go verified ✓` and `gen_read verified ✓` with no withdrawal, and the twin returning 0 failed its body obligation, withdrawing both callers: the verdicts were inverted with respect to the truth. At the fix the body owes `a::k`, fails, and both callers are withdrawn; the isolating twin trait_inherited_clause_scope_dependent_name_honoured_twin.rs (returning 0) verifies all three.
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
    // No clauses of its own: inherits `result@ == k()` as text.
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
