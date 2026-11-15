//@ expect: reject
//@ mechanism: a MIR Drop inside a loop carrying NO #[invariant] owes its unchecked user Drop::drop obligation
//@ fixed-by: s44 (wp-s44, Drop arm of the unannotated-loop walker) — re-pinned by the s62 merge
//@ accept-means: the primary extractor skips an invariant-less loop body, so a `Drop` terminator reached only through the loop header was never a drop site; `dropper_loop` always panics in D::drop and can never return x.
//@ verdict: failed
//@ refused-with: dropper_loop unknown (refutation withheld: goal set carries a fail-closed
//@ teeth: the union guard for the s62 merge — the Drop arm is the ONLY thing that can reject this shape (the loop body's MIR holds no call and no Assert), so removing it makes this verify.
//@ teeth: D-141 RE-PIN (not a weakening). The tooth was `dropper_loop FAILED`, and that FAILED was a
//@ teeth: model of the path guard around the fail-closed `false` this case exists to owe:
//@ teeth: the violated goal was `g ==> false`, which every model of `g` refutes, so it showed
//@ teeth: only that the refused construct is reached.
//@ teeth: Its twin s62m_drop_glue_unannotated_loop_quiet_drop_control, whose contract is TRUE,
//@ teeth: printed `dropper_loop FAILED` with the counterexample `x = 0` on the build that read only a bare
//@ teeth: `false` as a marker, and the same `unknown` as this case on the build that reads a
//@ teeth: guarded one.
//@ teeth: The marker is still owed, so `dropper_loop` is still refused and cannot be credited; only
//@ teeth: the spelling changed, and `refused-with:` names this function's own refusal.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

struct D;

impl Drop for D {
    fn drop(&mut self) {
        panic!("boom")
    }
}

// `_d` is dropped at the end of EVERY iteration, inside a loop that carries no
// `#[invariant]`. The drop glue panics, so `dropper_loop` never returns and the
// postcondition is false. The only obligation that can see it is the walker's
// `Drop` arm: the loop body's MIR holds a `Drop` terminator and nothing else
// this extractor could refuse.
#[ensures(result@ == x@)]
pub fn dropper_loop(x: u8) -> u8 {
    let mut i = 0u8;
    while i < 1u8 {
        let _d = D;
        i += 1u8;
    }
    x
}
