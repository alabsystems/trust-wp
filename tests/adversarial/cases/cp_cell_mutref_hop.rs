//@ expect: reject
//@ mechanism: `W<'a>` holds `&'a mut Cell<u8>`. `&mut Cell<u8>` is itself `Freeze`, so the
//@ mechanism: whole-type interior-mutability test does not see the cell, and the walk into the
//@ mechanism: field used to recurse straight past the `&mut` hop into the core `Adt` arm, which
//@ mechanism: inspects only `Cell`'s type arguments (`[u8]`). `W` therefore looked like an
//@ mechanism: ordinary value type, so instantiating `conflate<T: Rd>` at `T = W` carried no
//@ mechanism: obligation and `<W as Rd>` passed the trait-refinement gate. `conflate` was proved
//@ mechanism: under the model that shared access to a `T` never changes its logical value, which
//@ mechanism: `wr()` breaks by writing through the cell.
//@ fixed-by: s44 v4 (wp-s44): a `&mut` hop tests its pointee for interior mutability, like the
//@ fixed-by: shared/raw-pointer hop beside it
//@ accept-means: `go_true` credited with `result == true` AND `go_false` credited with
//@ accept-means: `result == false` for the SAME call. `wr()` adds 1, so the two `rd()` reads
//@ accept-means: around it never agree and `conflate` returns false for EVERY cell at runtime:
//@ accept-means: `go_true`'s contract is false and both cannot hold.
//@ verdict: failed
//@ refused-with: go_true unknown (refutation withheld
//@ teeth: wp-s81 RE-PIN (not a weakening). The tooth used to be `go_true FAILED`, and that
//@ teeth: FAILED was trust-wp refuting the `false` IT injected for this call — the very shape
//@ teeth: wp-s81 D1 stops publishing as a counterexample. The call still owes `false`, so the
//@ teeth: instantiation is still refused and still cannot be credited; only the SPELLING of the
//@ teeth: refusal changed, from `FAILED` to `unknown (refutation withheld: ...)`. The pin moved
//@ teeth: to `refused-with:` so it still names THIS function's own refusal — a regression that
//@ teeth: credited `go_true` would still be caught.
//@ teeth: A/B measured this session, debug driver, same workspace and harness-target.
//@ teeth: On wp-campaign ce1d56fc: `trust-wp: conflate verified ✓`, `trust-wp: go_true verified ✓`
//@ teeth: AND `trust-wp: go_false verified ✓`, with `<W<'a> as Rd>::wr refinement verified ✓`.
//@ teeth: On wp-s44 33b54931: `trust-wp: go_true FAILED ✗` and `trust-wp: go_false FAILED ✗`,
//@ teeth: and all three `<W<'a> as Rd>` refinements report
//@ teeth: `unknown (interior-mutable Self: ...)`.
//@ teeth: `<W<'a> as Rd>::rd FAILED ✗` on BOTH sides (its own `result == self.m()` is false for a
//@ teeth: real cell), so the crate is rejected either way — the teeth are the `fn-failed` line,
//@ teeth: which campaign does not produce.
//@ teeth: Over-refusal twin: cp_cell_mutref_hop_control (`&'a mut u8` field), `go verified ✓` on
//@ teeth: both sides.
//@ also-verified: conflate, <W<'a> as Rd>::wr
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

use std::cell::Cell;

pub struct W<'a> {
    c: &'a mut Cell<u8>,
}

pub trait Rd {
    #[logic]
    fn m(self) -> u8;
    #[ensures(result == self.m())]
    fn rd(&self) -> u8;
    #[ensures(true)]
    fn wr(&self);
}

impl<'a> Rd for W<'a> {
    #[logic]
    fn m(self) -> u8 {
        pearlite! { 0u8 }
    }
    fn rd(&self) -> u8 {
        self.c.get()
    }
    fn wr(&self) {
        self.c.set(self.c.get().wrapping_add(1))
    }
}

#[ensures(result == true)]
pub fn conflate<T: Rd>(t: &T) -> bool {
    let a = t.rd();
    t.wr();
    let b = t.rd();
    a == b
}

#[ensures(result == true)]
pub fn go_true(c: &mut Cell<u8>) -> bool {
    let w = W { c };
    conflate::<W>(&w)
}

#[ensures(result == false)]
pub fn go_false(c: &mut Cell<u8>) -> bool {
    let w = W { c };
    let r = conflate::<W>(&w);
    !r
}
