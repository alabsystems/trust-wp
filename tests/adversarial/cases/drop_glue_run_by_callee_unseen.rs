//@ expect: reject
//@ mechanism: a value whose drop glue writes is handed BY MOVE to a callee, which drops it:
//@ mechanism: `std::mem::drop`, a generic `consume<T>(t: T)` and a verified `sink(g: G)`. The glue runs
//@ mechanism: inside the callee, so no MIR `Drop` of the host sees it, and the callee's contract says
//@ mechanism: nothing about `c`, which it cannot name. The host read `c` after the call at its value
//@ mechanism: before the borrow.
//@ accept-means: a host is reported `verified` although the callee drops the `G`, whose `Drop` impl sets `c`
//@ accept-means: to 5 before the host returns `c`.
//@ WHY THE CONTRACT IS FALSE: every host returns 5: `mem::drop`, `consume` and `sink` each drop their argument at their
//@ WHY THE CONTRACT IS FALSE: end.
//@ fixed-by: D-140: a call handed by move a value whose glue may write, to a callee other than a
//@ fixed-by: standard-library function known to keep its arguments (the list the panic lane's
//@ fixed-by: `call_drop_obligation` reads), re-binds what that value reaches on the return edge.
//@ teeth: MEASURED: with D-140's hand-off disabled every host is ACCEPTED, exit 0, `verified`; with it
//@ teeth: each is `unknown`.
//@ also-verified: <G<'_> as std::ops::Drop>::drop, consume, sink
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

#[requires(true)]
pub fn consume<T>(t: T) {
    let _ = t;
}

#[requires(true)]
pub fn sink(g: G<'_>) {
    let _ = g;
}

#[ensures(result@ == 0)]
pub fn by_mem_drop() -> u32 {
    let mut c = 0u32;
    let g = G(&mut c);
    std::mem::drop(g);
    c
}

#[ensures(result@ == 0)]
pub fn by_generic_consume() -> u32 {
    let mut c = 0u32;
    consume(G(&mut c));
    c
}

#[ensures(result@ == 0)]
pub fn by_verified_sink() -> u32 {
    let mut c = 0u32;
    sink(G(&mut c));
    c
}
