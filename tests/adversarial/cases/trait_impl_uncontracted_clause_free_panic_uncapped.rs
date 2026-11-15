//@ expect: reject
//@ mechanism: `cap_clause_free_verdict` returns early for every body with a `trait_origin`, on the
//@ mechanism: premise that an impl method answers to its trait's contract. An impl of a trait method
//@ mechanism: that carries no contract inherits nothing (`apply_trait_contract_inheritance` copies
//@ mechanism: nothing), so the impl is as clause-free as an inherent method: its lane discharges
//@ mechanism: only the arithmetic that made it a verification target. The std call below is a panic
//@ mechanism: site no lane checks (its spec states no panic precondition). The inherent spelling of
//@ mechanism: the same body (trait_impl_uncontracted_panic_inherent_twin_capped) is capped at
//@ mechanism: `unknown (partial: panic paths unchecked (...))`; the impl is reported `verified`.
//@ mechanism: The same exemption credits an impl of a std trait
//@ mechanism: (std_trait_impl_clause_free_panic_uncapped).
//@ accept-means: a clause-free impl method whose body panics on every call is credited `verified`,
//@ accept-means: and the crate exits 0.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means the cap exempts only an impl
//@ fixed-by: method that actually inherited a contract, not every body with a `trait_origin`. The
//@ fixed-by: credit is also invisible to D-70's per-function gate, whose name pattern cannot read
//@ fixed-by: `<S as Tr>::m` (D-105); this case catches it only because the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: a clause-free `verified` claims that no execution panics. `v` holds
//@ WHY THE CONTRACT IS FALSE: `usize::MAX` zero-sized elements, its capacity, and pushing one more
//@ WHY THE CONTRACT IS FALSE: panics with "capacity overflow" on every call of `m`.
//@ teeth: MEASURED as ACCEPTED, exit 0, `<S as Tr>::m verified ✓`, on the same binary that reports
//@ teeth: the inherent twin `S::m unknown (partial: panic paths unchecked (...))`.
//@ note: the panic is a zero-sized push because `Vec::push` is a std call whose spec states no
//@ note: panic precondition (zst_vec_push_len_overflow_std_spec_silent). A std call whose spec owes
//@ note: its panic (D-121) fails in the body's own lane, before the cap this case isolates.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    fn m(&self, x: u8) -> usize;
}

pub struct S;

impl Tr for S {
    fn m(&self, x: u8) -> usize {
        let _y = x / 2 + 1;
        let mut v: Vec<()> = vec![(); usize::MAX];
        v.push(());
        v.len()
    }
}
