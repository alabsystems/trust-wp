//@ expect: reject
//@ mechanism: a parameter the body WROTE, then drop glue that writes it, then a `proof_assert!` of its
//@ mechanism: ENTRY value: `x = 7; { let _g = G(&mut x); } proof_assert!(x@ == 0)` under
//@ mechanism: `#[requires(x@ == 0)]`, where `G::drop` stores 5. The proof_assert lane reads a `#[requires]`
//@ mechanism: fact about a parameter as a fact about its current binding. Without the glue the write
//@ mechanism: collides with that fact and the assertion is refused as a vacuous proof. D-140's substitution
//@ mechanism: walk re-binds the parameter to a FRESH symbol at the hand-off, which collides with nothing, so
//@ mechanism: the entry precondition comes back as a premise about the value the glue wrote and the
//@ mechanism: assertion is proved. Spellings: a by-value scalar parameter, a `&mut` parameter's pointee
//@ mechanism: (`*x = 7; G(&mut *x)`), a by-value struct parameter reassigned (`p = P { x: 7 }; G(&mut p.x)`),
//@ mechanism: and the hand-off of a call (`x = 7; consume(G(&mut x))`, `consume` verified). The same bodies
//@ mechanism: asserting the value the body wrote (`== 7`) are refuted with D-140 (see
//@ mechanism: proof_assert_mut_param_written_value_stale_after_drop_glue). proof_assert_entry_requires_pins_param_after_drop_glue
//@ mechanism: is the spelling with no write before the glue, accepted with and without D-140.
//@ accept-means: a `proof_assert!` claiming a parameter still holds its entry value is credited after the
//@ accept-means: body overwrote it and drop glue overwrote it again, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: at each assertion the asserted value is 5 (the glue's store, after the body's
//@ WHY THE CONTRACT IS FALSE: 7); the precondition says only that it was 0 at entry.
//@ fixed-by: D-140: the proof_assert lane withdraws the entry facts naming a parameter a hand-off before
//@ fixed-by: the assertion may re-bind (as D-38 does for a loop), and those naming a by-value parameter its
//@ fixed-by: substitution re-binds by a plain write.
//@ teeth: MEASURED, each function as its own crate, on one binary with D-140's hand-off disabled by an
//@ teeth: env knob (never committed): each function is refused (`unknown`, vacuous proof; the struct
//@ teeth: spelling FAILED); with the hand-off and no withdrawal, each assertion and function is `verified`
//@ teeth: and the crate exits 0; with the withdrawal (the hand-off's alone suffices), each is FAILED.
//@ teeth: Control: proof_assert_param_entry_requires_revived_reads_only_control (a `Drop` that only reads,
//@ teeth: asserting the written 7).
//@ also-verified: <G<'_> as std::ops::Drop>::drop, consume
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = 5;
    }
}

pub struct P {
    pub x: u32,
}

#[requires(x@ == 0)]
pub fn scalar_param(mut x: u32) {
    x = 7;
    {
        let _g = G(&mut x);
    }
    proof_assert!(x@ == 0);
}

#[requires((*x)@ == 0)]
pub fn mut_pointee(x: &mut u32) {
    *x = 7;
    {
        let _g = G(&mut *x);
    }
    proof_assert!((*x)@ == 0);
}

#[requires(p.x@ == 0)]
pub fn struct_param(mut p: P) {
    p = P { x: 7 };
    {
        let _g = G(&mut p.x);
    }
    proof_assert!(p.x@ == 0);
}

#[requires(true)]
pub fn consume(_g: G<'_>) {}

#[requires(x@ == 0)]
pub fn verified_consume(mut x: u32) {
    x = 7;
    consume(G(&mut x));
    proof_assert!(x@ == 0);
}
