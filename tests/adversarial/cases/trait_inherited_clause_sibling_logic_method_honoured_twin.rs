//@ expect: verify
//@ mechanism: the isolating twin of trait_inherited_clause_sibling_logic_method_granted: the body returns
//@ mechanism: 5, which is `<W as Rd>::val`, so the inherited `result@ == self.val()` holds and `go` keeps
//@ mechanism: its credit. The refinement of an inherited contract compares the trait's text with itself,
//@ mechanism: so its clauses are premises, not goals: read as goals, each side's `self.val()` was a
//@ mechanism: separate unresolved symbol and the tautology was printed `trait refinement FAILED ✗`,
//@ mechanism: withdrawing the true `go`.
//@ fixed-by: D-112 (an inherited contract's clauses are premises of its refinement, never goals)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED at D-110 as `<W as Rd>::rd trait refinement FAILED ✗` with counterexample `__uf_int_aux_0 = 0`, `__uf_int_aux_1 = 1`, and `go` withdrawn; at the parent of D-110 `go` was credited, the refinement refusal exempted; at D-112 `<W as Rd>::rd refinement verified ✓` and `go verified ✓`)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Rd {
    #[logic]
    fn val(self) -> Int;
    #[ensures(result@ == self.val())]
    fn rd(self) -> u32;
}

pub struct W;

impl Rd for W {
    #[logic(open)]
    fn val(self) -> Int {
        pearlite! { 5 }
    }
    fn rd(self) -> u32 {
        5
    }
}

#[ensures(result@ == 5)]
pub fn go() -> u32 {
    W.rd()
}
