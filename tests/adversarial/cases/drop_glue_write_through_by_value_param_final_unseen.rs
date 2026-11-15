//@ expect: reject
//@ mechanism: a by-value parameter that HOLDS a `&mut` (`g: G<'_>`, whose `Drop` impl stores 5 through
//@ mechanism: it) has its glue run inside the function: at its own scope-end `Drop` (after an early
//@ mechanism: `return` too), at the `Drop` of a local it was moved into (`let _k = g`, a tuple, an
//@ mechanism: `Option`), and inside a callee handed it by move (`mem::drop(g)`, a generic
//@ mechanism: `consume(g)`). The lane that gives a parameter its final value (`mut_borrow`) followed a
//@ mechanism: `Drop` as a no-op and read `^g.0` as the last value the body stored through `g.0`, so
//@ mechanism: `(^g.0)@ == 0` held after `*g.0 = 0` although the glue stores 5 after it. D-140's other
//@ mechanism: lanes re-bind only the locals the value reaches and leave out the dropped local itself
//@ mechanism: and the call's arguments, which cannot be read again; the final value of what a
//@ mechanism: parameter holds is read after them all the same.
//@ accept-means: a function is credited with a final value of the borrow its parameter holds that the
//@ accept-means: parameter's drop glue overwrites before the borrow ends.
//@ WHY THE CONTRACT IS FALSE: called as `f(G(&mut c))` with `c = 7`, each function leaves `c` at 5:
//@ WHY THE CONTRACT IS FALSE: the borrow `g.0` ends after `G::drop` stored 5 through it, so its final
//@ WHY THE CONTRACT IS FALSE: value is 5. Compiled and run as a plain program, each prints 5.
//@ fixed-by: the parameter-final lane re-reads a hand-off (`mut_borrow::traversal::terminator`):
//@ fixed-by: every parameter the glue's reach tracks is havocked, and a call leaves out only the
//@ fixed-by: parameters whose final value it takes from the callee's `^`.
//@ teeth: MEASURED: ACCEPTED, exit 0, all seven functions `verified`, on the binary before D-140 and
//@ teeth: on the one with D-140's other lanes but not this one; with it each is FAILED.
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

#[ensures(true)]
pub fn consume<T>(_t: T) {}

#[ensures((^g.0)@ == 0u32)]
pub fn dropped_at_scope_end(g: G<'_>) {
    *g.0 = 0;
}

#[ensures((^g.0)@ == 0u32)]
pub fn moved_into_a_local(g: G<'_>) {
    *g.0 = 0;
    let _k = g;
}

#[ensures((^g.0)@ == 0u32)]
pub fn packed_into_a_tuple(g: G<'_>) {
    *g.0 = 0;
    let _k = (g, 1u32);
}

#[ensures((^g.0)@ == 0u32)]
pub fn moved_into_an_option(g: G<'_>) {
    *g.0 = 0;
    let _o = Some(g);
}

#[ensures((^g.0)@ == 0u32)]
pub fn dropped_after_an_early_return(g: G<'_>, b: bool) {
    *g.0 = 0;
    if b {
        return;
    }
    *g.0 = 0;
}

#[ensures((^g.0)@ == 0u32)]
pub fn handed_to_mem_drop(g: G<'_>) {
    *g.0 = 0;
    drop(g);
}

#[ensures((^g.0)@ == 0u32)]
pub fn handed_to_a_generic_callee(g: G<'_>) {
    *g.0 = 0;
    consume(g);
}
