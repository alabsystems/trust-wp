//@ expect: verify
//@ xfail: D-127 counts a drop of a value holding a borrow as a store through it, whatever the
//@ xfail: `Drop` impl's body does (it is not read), so the host's read of `c` is stale and fails
//@ xfail: closed; the write-through twin is the false accept that rule closes.
//@ mechanism: control for drop_impl_write_through_held_mut_unseen and
//@ mechanism: drop_glue_runs_capture_writing_closure_unseen: a `Drop` impl that only READS through
//@ mechanism: the `&mut` its value holds leaves `c` at 0, and the host must keep verifying.
//@ accept-means: n/a (control)
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        let _ = *self.0;
    }
}

#[ensures(result@ == 0)]
pub fn host() -> u32 {
    let mut c = 0u32;
    {
        let _g = G(&mut c);
    }
    c
}
