//@ expect: reject
//@ verdict: failed
//@ fn-failed: <W as Rd>::rd
//@ mechanism: an impl that inherits its trait method's clauses and names the parameters in another
//@ mechanism: order. A caller is handed `result@ == x@ + k()` over the FIRST argument; the inherited
//@ mechanism: text was read by the impl's own names, where `x` is the SECOND parameter, so the body
//@ mechanism: returning its second parameter verified. The refinement check compares positions and
//@ mechanism: would have caught it, but `k()` made it refuse on a scope-dependent name, and the
//@ mechanism: verbatim exemption dropped that refusal: `go` kept the grant.
//@ fixed-by: D-110 (the inherited clause is restated in the impl's parameter names position by position, or refused)
//@ accept-means: `go` claims `result@ == 1` and returns 2; `<W as Rd>::rd` claims the trait's clause over its first parameter and returns its second.
//@ teeth: MEASURED at the parent commit: `<W as Rd>::rd verified ✓` and `go verified ✓` beside the refinement refusal, with no withdrawal. Without `k()` the refinement goal fails and withdraws `go`, but the impl's own `verified ✓` stood as well. The isolating twin trait_inherited_clause_renamed_params_honoured_twin.rs returns the first parameter and verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 0 }
}

pub trait Rd {
    #[ensures(result@ == x@ + k())]
    fn rd(&self, x: u32, y: u32) -> u32;
}

pub struct W;

// The inherited `x` is the trait's FIRST parameter, which this impl calls `y`.
impl Rd for W {
    fn rd(&self, y: u32, x: u32) -> u32 {
        x
    }
}

#[ensures(result@ == 1)]
pub fn go() -> u32 {
    W.rd(1, 2)
}
