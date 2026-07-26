// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! proof_assert reading a LOCAL after a write through a borrow of it.
//!
//! Regression for the resolve_drop class: the cutoff-time substitution map
//! must rebind a deref-written local to its POST-write value. Before the fix,
//! `x`'s entry-time binding (`x -> 12`) survived alongside the writeback
//! (`x == 13`), manufacturing UNSAT base premises (vacuous "proof"), and the
//! assertion text `x@` was rewritten to the stale entry value.
//!
//! Covers both the plain `&mut` chain and the `Box<&mut _>` chain
//! (reference/creusot tests/should_succeed/resolve_drop.rs).

use trust_wp::proof_assert;

fn plain_borrow_write() {
    let mut x = 12;
    let b = &mut x;
    *b += 1;
    proof_assert!(x@ == 13);
}

fn boxed_borrow_write() {
    let mut x = 12;
    let b = Box::new(&mut x);
    **b += 1;
    proof_assert!(x@ == 13);
}

fn main() {
    plain_borrow_write();
    boxed_borrow_write();
}
