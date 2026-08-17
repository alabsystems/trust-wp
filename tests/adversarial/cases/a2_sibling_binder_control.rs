//@ expect: verify
//@ xfail: Fix A (932a7de) refuses the `^`-collapse on the Option<&mut T> payload fail-closed, so
//@ xfail: the honest prophecy facts cannot be produced yet. Re-entry is Fix B (prophecy slots in
//@ xfail: datatype carriers) — memory/fixb-prophecy-slots-design.md. Creusot proves this contract.
//@ mechanism: sibling-binder prophecy fusion — the TRUE contract of the same split-first shape
//@ fixed-by: n/a (open; blocked on Fix B)
//@ accept-means: n/a (control). An XPASS is the signal that Fix B landed and works; when it
//@ accept-means: happens, a2_sibling_binder_fusion MUST still reject — check both together.
//@ timeout: 300
//@
//@ This is the honest half of the take_first_mut story: trust-wp verified this contract before
//@ 932a7de, but the proof rested on the false lemma the adversarial sibling case exercises. The
//@ pass was withdrawn deliberately (241 = 243 − take_first_mut − partially_opaque).
//@ teeth: ★VERIFIED (xfail direction). Same knob: this control XPASSES with Fix A disabled, exactly
//@ teeth: reproducing the pre-932a7de take_first_mut pass that the audit adjudicated as resting on the
//@ teeth: false lemma. Control and adversarial flip TOGETHER — that is the signature of the defect.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use std::mem;

#[ensures(match result {
    Some(r) => {
        *r == (**self_)[0] && ^r == (^*self_)[0] &&
        (**self_)@.len() > 0 && (^*self_)@.len() > 0
    }
    None => (*^self_)@ == Seq::empty() && (^*self_)@ == Seq::empty(),
})]
pub fn take_first_honest<'a, T>(self_: &mut &'a mut [T]) -> Option<&'a mut T> {
    match mem::take(self_).split_first_mut() {
        None => None,
        Some((first, rem)) => {
            *self_ = rem;
            Some(first)
        }
    }
}
