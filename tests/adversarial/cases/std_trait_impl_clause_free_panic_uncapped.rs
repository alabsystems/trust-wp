//@ expect: reject
//@ mechanism: the std-trait spelling of trait_impl_uncontracted_clause_free_panic_uncapped. `Default`
//@ mechanism: carries no contract a local impl inherits, so `<S as Default>::default` is a clause-free
//@ mechanism: body, a verification target only for its arithmetic, and `cap_clause_free_verdict`'s
//@ mechanism: early return for every `trait_origin` reports it `verified` although its std call is
//@ mechanism: a panic site no lane checks.
//@ accept-means: a clause-free impl of a std trait whose body panics on every call is credited
//@ accept-means: `verified`, and the crate exits 0.
//@ fixed-by: OPEN — committed RED rather than hidden; the same exemption as its twin.
//@ WHY THE CONTRACT IS FALSE: a clause-free `verified` claims that no execution panics. `v` holds
//@ WHY THE CONTRACT IS FALSE: `usize::MAX` zero-sized elements, its capacity, and pushing one more
//@ WHY THE CONTRACT IS FALSE: panics with "capacity overflow" on every call of `default`.
//@ teeth: MEASURED as ACCEPTED, exit 0, `<S as std::default::Default>::default verified ✓`.
//@ note: the panic is a zero-sized push because `Vec::push` is a std call whose spec states no
//@ note: panic precondition (zst_vec_push_len_overflow_std_spec_silent). A std call whose spec owes
//@ note: its panic (D-121) fails in the body's own lane, before the cap this case isolates.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S(pub usize);

impl Default for S {
    fn default() -> S {
        let a: u8 = 7;
        let _y = a / 2 + 1;
        let mut v: Vec<()> = vec![(); usize::MAX];
        v.push(());
        S(v.len())
    }
}
