//@ expect: verify
//@ mechanism: control for proof_assert_param_entry_value_in_ghost_block.rs: in a `ghost!` block after
//@ mechanism: a write, a by-value parameter reads its current value and a copy taken before the write
//@ mechanism: keeps the entry value and its `#[requires]`; an unwritten field keeps its entry fact.
//@ accept-means: n/a (control) — every claim here holds in every execution.
//@ fixed-by: n/a (control)
//@ teeth: on D-240 one assertion of `ghost_copy_keeps_entry` and one of `ghost_field_ok` are FAILED;
//@ teeth: all verified with D-241.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct P {
    pub a: i32,
    pub b: i32,
}

#[requires(x@ == 0)]
pub fn ghost_copy_keeps_entry(mut x: u32) {
    let y = x;
    x = 5;
    ghost! {
        proof_assert!(y@ == 0);
        proof_assert!(x@ == 5);
    };
    let _ = x;
}

#[requires(p.b@ == 3)]
pub fn ghost_field_ok(mut p: P) {
    p.a = 7;
    ghost! {
        proof_assert!(p.a@ == 7);
        proof_assert!(p.b@ == 3);
    };
    let _ = p;
}
