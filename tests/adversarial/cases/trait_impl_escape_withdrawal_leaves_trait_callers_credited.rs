//@ expect: reject
//@ mechanism: D-118's escape join withdraws an impl's credit AFTER the trait-credit join has
//@ mechanism: settled which callers rest on an undischarged trait contract. `<S as Tr>::m` hands a
//@ mechanism: closure that indexes an unconstrained slice to `Option::map`; the closure is refuted
//@ mechanism: and `escape_credit_join::demote` withdraws `<S as Tr>::m`, but the withdrawal never
//@ mechanism: reaches `TraitCreditJoin::undischarged`, so every caller credited on `Tr::m`'s
//@ mechanism: contract keeps its credit. The default-body spelling (`Dt::m`, run by `D`) is the
//@ mechanism: same. The code that owes the obligation (the escape join) and the code that grants
//@ mechanism: the callers' credit (the trait join) do not read one verdict.
//@ accept-means: `generic_caller`, `conc` and `default_caller` are reported `verified` although each
//@ accept-means: panics on `(Some(0), &[])` inside the closure the impl hands to `Option::map`.
//@ WHY THE CONTRACT IS FALSE: at `T = S` (and `T = D`) the only body of `m` indexes `w[0]` with `w`
//@ WHY THE CONTRACT IS FALSE: empty.
//@ fixed-by: D-122: every withdrawal after the contract loop enters one ledger with the trait join,
//@ fixed-by: and a withdrawn implementation (or default body) is recorded as not discharging the
//@ fixed-by: contract it owes; the two joins run to a fixpoint before any caller settles.
//@ teeth: MEASURED: on the binary before D-122 `<S as Tr>::m` and `Dt::m` are withdrawn and
//@ teeth: `generic_caller`, `conc` and `default_caller` verified; after it all three are withdrawn,
//@ teeth: "it assumed trait method contract `Tr::m`" / "`Dt::m`". The isolating pair is
//@ teeth: trait_impl_guarded_escape_callers_control, whose guarded closure verifies, so the impl and
//@ teeth: both callers keep their credit before and after.
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

pub trait Tr {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>, w: &[u32]) -> u32;
}

pub struct S;

impl Tr for S {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>, w: &[u32]) -> u32 {
        let _ = o.map(|j| w[j]);
        1
    }
}

#[ensures(result@ == 1)]
pub fn generic_caller<T: Tr>(t: &T, o: Option<usize>, w: &[u32]) -> u32 {
    t.m(o, w)
}

#[ensures(result@ == 1)]
pub fn conc(o: Option<usize>, w: &[u32]) -> u32 {
    S.m(o, w)
}

pub trait Dt {
    #[ensures(result@ == 1)]
    fn m(&self, o: Option<usize>, w: &[u32]) -> u32 {
        let _ = o.map(|j| w[j]);
        1
    }
}

pub struct D;
impl Dt for D {}

#[ensures(result@ == 1)]
pub fn default_caller<T: Dt>(t: &T, o: Option<usize>, w: &[u32]) -> u32 {
    t.m(o, w)
}
