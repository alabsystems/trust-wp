//@ expect: verify
//@ mechanism: the TRUE twin of logic_int_arithmetic_in_program_context_panics: the `Int` operations
//@ mechanism: whose run-time body is the logical one stay open in program code (the constructor, a
//@ mechanism: comparison between two `Int`s, `From` of a machine integer of at most 64 bits), and
//@ mechanism: `Int` arithmetic inside `ghost!`, which never runs, is read as the logical operation.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — natively `exact` returns `true` and `in_ghost` returns; each verified before and
//@ teeth: after `Int` arithmetic is refused in program code.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result)]
pub fn exact() -> bool {
    let a = Int(5);
    let b = Int::from(6u64);
    a < b && a == Int(5)
}

#[ensures(true)]
pub fn in_ghost() {
    let x: Ghost<Int> = ghost!(Int(i128::MAX));
    ghost! {
        let y = *x + Int(1);
        proof_assert!(y > *x);
    };
}
