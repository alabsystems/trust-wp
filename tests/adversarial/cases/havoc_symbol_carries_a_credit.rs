//@ expect: reject
//@ mechanism: a by-value local captured by a mutating closure is never advanced past the call.
//@ mechanism: The capture owner keeps its ENTRY symbol `p`, and the closure's post-state credit
//@ mechanism: (`p.1@ == 1`) is asserted over that very symbol — so one symbol is at once the
//@ mechanism: pre-call value the caller's `#[requires]` constrains and the post-call value the
//@ mechanism: closure's `#[ensures]` constrains. The write the closure performed on the OTHER
//@ mechanism: field is therefore not forgotten but positively contradicted: `p.0@ == 1` survives
//@ mechanism: `p.0 = 9`. Grant and obligation are the same symbol in two different states.
//@ accept-means: any write a closure makes to a captured by-value local can be erased by the
//@ accept-means: caller's own precondition. A `#[requires]` over a capture is silently promoted
//@ accept-means: to a postcondition about it, so every claim about a mutated capture that
//@ accept-means: repeats an entry premise verifies, and the true post-state is refuted instead.
//@ fixed-by: D-55
//@ WHY THE CONTRACT IS FALSE: `returns_entry_value((1, 0))` returns 9 — the closure assigns
//@ WHY 9 to `p.0` before the tuple field is read back. Compiled and run as a plain program it
//@ WHY prints 9; the postcondition claims 1.
//@ teeth: ACCEPTED on this tree and on the campaign build tree's own engine binary (exit 0,
//@ teeth: `2 verified, 0 failed, 0 errors`), so the hole pre-exists this case. Three separating
//@ teeth: runs show the credit, not a mere havoc, is what carries it: (a) the TRUE twin claiming
//@ teeth: the real post-state `result@ == 9` is REFUTED with a counterexample — the entry value
//@ teeth: is being asserted, not merely remembered; (b) the same body with the `#[requires]`
//@ teeth: removed proves nothing at all (the symbol then carries no credit); (c) the same body
//@ teeth: with the assertion placed BEFORE the call verifies and is TRUE, so the accept is
//@ teeth: created by the call, not by the shape of the claim.
//@ also-verified: returns_entry_value::{closure#3}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(p.0@ == 1i32)]
#[ensures(result@ == 1i32)]
pub fn returns_entry_value(mut p: (i32, i32)) -> i32 {
    let mut clos = #[ensures(p.1@ == 1i32)]
    || {
        p.0 = 9i32;
        p.1 = 1i32;
    };
    clos();
    p.0
}
