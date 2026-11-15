//@ expect: verify
//@ mechanism: the other half of the disjoint-capture pair — the field the closure DOES write,
//@ mechanism: read back through the closure's own postcondition. It verifies, so the capture
//@ mechanism: owner's post-call state does carry the closure's credit; what it also still carries
//@ mechanism: is the caller's entry premise about the field the closure wrote behind the
//@ mechanism: contract's back. Both controls verifying is what makes the adversarial twin's
//@ mechanism: accept a contradiction rather than a coverage gap.
//@ teeth: verifies on this tree (exit 0), and it is the run that shows the closure postcondition
//@ teeth: is genuinely in scope after the call — so the entry premise surviving alongside it is
//@ teeth: one symbol holding two states at once.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(p.0@ == 1i32)]
#[ensures(result@ == 1i32)]
pub fn disjoint_capture_written_field(mut p: (i32, i32)) -> i32 {
    let mut clos = #[ensures(p.1@ == 1i32)]
    || {
        p.1 = 1i32;
    };
    clos();
    p.1
}
