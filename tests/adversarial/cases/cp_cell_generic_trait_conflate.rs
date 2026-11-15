//@ expect: reject
//@ mechanism: generic `&T` receiver instantiated at Cell: two `rd()` reads around `wr()` through a
//@ mechanism: generic shared reference must not be one value when the impl's logic model reads the
//@ mechanism: cell. An impl whose `Self` exposes interior mutability (`Cell<u8>`) gets NO refinement
//@ mechanism: credit, so the impl's `rd` cannot be credited with the trait's model postcondition
//@ mechanism: around a `wr()` that writes through the shared reference.
//@ fixed-by: s44 v2 (wp-s44): impls and generic instantiations exposing interior mutability fail closed
//@ accept-means: `a == b` around `t.wr()` verified; false for T = Cell<u8> holding a nonzero value.
//@ accept-means: Equivalently `<Cell<u8> as Rd>::rd` credited with `result == self.m()` — the value
//@ accept-means: model applied to a cell, which `conflate`'s `a == b` then reads as a proof.
//@ note: wp-campaign's s55 re-pin of this case (`refused-with: conflate unknown (refutation
//@ note: withheld:`) replaced the OLD `fn-failed: conflate` pin. This front had already replaced
//@ note: that same pin, for a different reason: the fixture's contracts changed (`wr` gained
//@ note: `#[ensures(true)]`, the impl's duplicated `rd` ensures went away), so `conflate` itself
//@ note: is `verified ✓` here and the teeth moved onto the IMPL's verdict. The s55 rule still
//@ note: governs that impl verdict — see the `verdict:`/`refused-with:` pin below, which was
//@ note: re-measured on the merged tree.
//@ spelling: Creusot has no logic `inner` on Cell (creusot-std models no Cell contents), so the
//@ spelling: impl's model is `#[logic(opaque)]` + `dead`, as in Creusot traits/16_impl_cloning.rs.
//@ verdict: failed
//@ fn-failed: <std::cell::Cell<u8> as Rd>::rd
//@ teeth-credit: Re-pinned 2026-09-18 (wp-s69, validated refutations): back to `verdict: failed` +
//@ teeth-credit: `fn-failed`. s55's rule stands — no FAILED without a VALIDATED model — and the
//@ teeth-credit: impl's `rd` now HAS one: `result == self.m()` with `m` opaque is a query the
//@ teeth-credit: solver answers SAT with a model ay validates (m() ≠ self.get()), instead of the
//@ teeth-credit: structural `Failed(empty)` the s55 gate had to withhold. The `unknown (refutation
//@ teeth-credit: withheld:` spelling below is the s55-era measurement, kept for the record; it is
//@ teeth-credit: no longer the honest line, `FAILED ✗` with `model_validated=true` is.
//@ teeth-credit: Re-pinned 2026-09-14 on the merge of wp-campaign 03a35447 (s55). The pin used to
//@ teeth-credit: be `verdict: failed` + `fn-failed: <std::cell::Cell<u8> as Rd>::rd`. The impl's
//@ teeth-credit: `rd` still does not verify; s55 merely stops the driver PRINTING `FAILED` for a
//@ teeth-credit: verdict whose only evidence was `trust-wp-structural-provenance` rather than an
//@ teeth-credit: accepted, model-validated SAT snapshot, so the honest line is now
//@ teeth-credit: `trust-wp: <std::cell::Cell<u8> as Rd>::rd unknown (refutation withheld: solver
//@ teeth-credit: evidence was trust-wp-structural-provenance, not a satisfying counterexample
//@ teeth-credit: model)`. Measured on the merged tree: 2 verified, 0 failed, 4 errors, and all
//@ teeth-credit: three impl items still report `refinement unknown (interior-mutable Self: ...)`.
//@ teeth-credit: `(refutation withheld:` stays inside the pin so a plain solver timeout — which
//@ teeth-credit: also prints `rd unknown` — cannot satisfy it.
//@ teeth: the generic half alone (`conflate<T: Rd>` with no impl in the crate) verifies by the
//@ teeth: Creusot value model for `&T`; the teeth are the impl refusal and the instantiation
//@ teeth: obligation (cp_cell_generic_instantiation), not the generic body. Measured on wp-s44 at
//@ teeth: the merge commit 007961fc with campaign's `dead` spelling: `<Cell<u8> as Rd>::rd
//@ teeth: FAILED ✗ (postcondition)` and all three impl items reported "refinement unknown
//@ teeth: (interior-mutable Self: ...)". `conflate` itself is `verified ✓` — that is the honest
//@ teeth: residual named above, so the case is pinned on the IMPL's verdict, not on `conflate`.
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
    #[logic(opaque)]
    fn m(self) -> u8 {
        dead
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
