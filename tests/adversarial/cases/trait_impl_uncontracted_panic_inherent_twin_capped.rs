//@ expect: reject
//@ verdict: unknown
//@ mechanism: the inherent twin of trait_impl_uncontracted_clause_free_panic_uncapped, identical
//@ mechanism: but for `impl S` in place of `impl Tr for S`. With no `trait_origin`,
//@ mechanism: `cap_clause_free_verdict` caps the clause-free body at `unknown (partial: panic paths
//@ mechanism: unchecked (...))`, which is what isolates the RED twin's accept to the `trait_origin`
//@ mechanism: exemption rather than to anything about the body.
//@ accept-means: the clause-free cap stopped firing on an unchecked std call.
//@ fixed-by: the clause-free cap (`cap_clause_free_verdict`).
//@ WHY THE CONTRACT IS FALSE: a clause-free `verified` claims that no execution panics. `v` holds
//@ WHY THE CONTRACT IS FALSE: `usize::MAX` zero-sized elements, its capacity, and pushing one more
//@ WHY THE CONTRACT IS FALSE: panics with "capacity overflow" on every call of `m`.
//@ teeth: structural: `S::m unknown (partial: panic paths unchecked (...))` on the binary that
//@ teeth: reports its trait-impl twin `verified`.
//@ note: the panic is a zero-sized push because `Vec::push` is a std call whose spec states no
//@ note: panic precondition (zst_vec_push_len_overflow_std_spec_silent). A std call whose spec owes
//@ note: its panic (D-121) fails in the body's own lane, before the cap this case isolates.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S;

impl S {
    pub fn m(&self, x: u8) -> usize {
        let _y = x / 2 + 1;
        let mut v: Vec<()> = vec![(); usize::MAX];
        v.push(());
        v.len()
    }
}
