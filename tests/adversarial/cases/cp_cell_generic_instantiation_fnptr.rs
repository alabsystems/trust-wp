//@ expect: reject
//@ mechanism: identical to cp_cell_generic_instantiation, with ONE coercion in between: `go`
//@ mechanism: reaches `conflate::<Cell<u8>>` through a fn POINTER. Spec resolution follows the
//@ mechanism: pointer back to the unique `FnDef` the local was initialised from and credits that
//@ mechanism: callee's postcondition, so the instantiation obligation must follow the SAME
//@ mechanism: resolution — a callee whose contract is credited at a call site owes, at that same
//@ mechanism: site, every obligation its instantiation carries.
//@ fixed-by: s44 v3 (wp-s44): both type-driven call obligations resolve the callee through
//@ fixed-by: `resolved_callee`, the chain `resolve_call` itself walks, instead of matching
//@ fixed-by: `TyKind::FnDef` on the operand's own type.
//@ accept-means: `go` credited with `result == true` while it returns `false` for EVERY cell at
//@ accept-means: runtime: `wr()` adds 1, so the two `rd()` reads around it never agree. One
//@ accept-means: `as fn(_) -> _` coercion inside a single fully verified crate bought the
//@ accept-means: postcondition and owed nothing.
//@ verdict: failed
//@ refused-with: go unknown (refutation withheld
//@ teeth: wp-s81 RE-PIN (not a weakening). The tooth used to be `go FAILED`, and that
//@ teeth: FAILED was trust-wp refuting the `false` IT injected for this call — the very shape
//@ teeth: wp-s81 D1 stops publishing as a counterexample. The call still owes `false`, so the
//@ teeth: instantiation is still refused and still cannot be credited; only the SPELLING of the
//@ teeth: refusal changed, from `FAILED` to `unknown (refutation withheld: ...)`. The pin moved
//@ teeth: to `refused-with:` so it still names THIS function's own refusal — a regression that
//@ teeth: credited `go` would still be caught.
//@ teeth: measured on wp-campaign 54fe868b and on wp-s44 at the merge commit 007961fc (debug
//@ teeth: driver): `trust-wp: go verified ✓`, vacuous=0, panics=0 — a FALSE ACCEPT. After the fix
//@ teeth: (dbb64e54): `trust-wp: go FAILED ✗ (postcondition)`. The credit really did flow through
//@ teeth: the pointer: on the same base `#[ensures(result == false)] fn neg(c) { !f(c) }` was
//@ teeth: `neg verified ✓` and is `neg FAILED ✗` after.
//@ also-verified: conflate, <std::cell::Cell<u8> as Rd>::wr
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

use std::cell::Cell;

pub trait Rd {
    #[logic]
    fn m(self) -> u8;
    #[ensures(result == self.m())]
    fn rd(&self) -> u8;
    #[ensures(true)]
    fn wr(&self);
}

impl Rd for Cell<u8> {
    #[logic]
    fn m(self) -> u8 {
        pearlite! { 0u8 }
    }
    fn rd(&self) -> u8 {
        self.get()
    }
    fn wr(&self) {
        self.set(self.get().wrapping_add(1))
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
pub fn go(c: &Cell<u8>) -> bool {
    let f: fn(&Cell<u8>) -> bool = conflate::<Cell<u8>>;
    f(c)
}
