//@ expect: verify
//@ mechanism: control: every `&u8` points at a value below 256, and `f` returns true. The isolating
//@ mechanism: twin of quantifier_binder_reference_to_machine_int_read_unbounded_granted.rs.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; with D-203 the binder is spelled with the refusal marker, as
//@ teeth: its twin's header records; verified with D-204)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == (forall<r: &u8> (*r)@ < 256))]
pub fn f() -> bool {
    true
}
