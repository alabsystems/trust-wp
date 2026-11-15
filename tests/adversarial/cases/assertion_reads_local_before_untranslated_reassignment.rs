//@ expect: reject
//@ mechanism: the `proof_assert!` substitution walk (`SubstitutionVisitor::on_assign_local`) binds a local
//@ mechanism: only when it translates the right-hand side, and on an assignment it cannot translate keeps the
//@ mechanism: local's EARLIER binding: after `let mut a = 0usize; a = q as usize;` (a pointer-to-integer cast)
//@ mechanism: or `m = (x + f64::EPSILON) as u32` (an associated constant the operator path does not evaluate)
//@ mechanism: the assertion reads `a == 0`. D-169 binds such an assignment to a symbol of its site in the
//@ mechanism: primary walk; this walk has no such binding. `on_assign_projected` returns early in the same way
//@ mechanism: for a field write it cannot translate. f16_operation_read_as_earlier_value_in_assertion.rs is
//@ mechanism: the `f16` route into it that D-217 closes.
//@ accept-means: `ptr_cast(5 as *const u8)` and `assoc_const(5.0)` reach their assertion with a nonzero
//@ accept-means: value; an accept claims each assertion holds.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means the walk binds an untranslated
//@ fixed-by: assignment as the primary walk does (D-169's site symbol), never to the earlier value.
//@ teeth: ACCEPTED on the campaign tip and with D-217 (each assertion verified, exit 0).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unused_assignments)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn ptr_cast(q: *const u8) {
    let mut a = 0usize;
    a = q as usize;
    proof_assert!(a == 0usize);
}

pub fn assoc_const(x: f64) {
    let mut m = 0u32;
    m = (x + f64::EPSILON) as u32;
    proof_assert!(m == 0u32);
}
