//@ expect: verify
//@ mechanism: trait-contract credit — over-refusal control (the impl DOES discharge)
//@ fixed-by: s67 (wp-s67, trait-contract credit ledger + demotion)
//@ accept-means: n/a (control) — the impl proves the very contract the generic caller is handed.
//@ teeth: n/a — over-refusal control for the credit withdrawal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W;

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool;
}

// No clauses of its own: it inherits the trait's contract verbatim and proves
// it. The generic caller's grant is therefore paid for.
impl Rd for W {
    fn rd(&self) -> bool {
        true
    }
}

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

#[ensures(result)]
pub fn go() -> bool {
    gen_read::<W>(&W)
}
