//@ expect: verify
//@ xfail: completeness (s34-owned, depth-2 field path) — the write `o.i.x += 1` leaves `^o` unconstrained: ay returns a counterexample with `o_final == o_current` (`Out(In(1), 1)`), so the value-carrier final value carries no field update through TWO nested named-struct projections. Measured 2026-09-13 on wp-s33 @ 34297f75: the depth-1 shapes verify (`s34_field_named_single_control`, and a two-field depth-1 probe `#[ensures((^p).a == p.a + 1u64)] p.a += 1` — ACCEPTED), while the same depth-2 shape with the extra outer field removed still FAILS, so the gap is the nesting depth, not the untracked sibling field. This control was a compile error before the spec type-check vehicle fixtures were respelled (f925badd); it FAILED in both measurements taken since (69e796af, 34297f75).
//@ mechanism: stale identity final value for a write through &mut to a field of a struct/newtype/tuple — over-refusal control
//@ fixed-by: s34 value-carrier functional field updates
//@ accept-means: n/a (control) — this contract is TRUE.
//@
//@ Same shape as s34_field_nested_struct with the true postcondition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct In {
    pub x: u64,
}

pub struct Out {
    pub i: In,
    pub k: u64,
}

#[requires(o.i.x < 100u64)]
#[ensures((^o).i.x == o.i.x + 1u64)]
pub fn mut_o(o: &mut Out) {
    o.i.x += 1;
}
