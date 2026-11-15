//@ expect: verify
//@ mechanism: control for drop_glue_write_through_by_value_param_final_unseen: the same functions over
//@ mechanism: a holder with no `Drop` impl (`H<'_>`) and over a guard whose `Drop` impl only reads
//@ mechanism: through the borrow (`R<'_>`). No glue stores after `*h.0 = 0`, so the borrow's final
//@ mechanism: value is 0 and each function must keep verifying.
//@ accept-means: n/a (control)
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct H<'a>(pub &'a mut u32);

pub struct R<'a>(pub &'a mut u32);

impl Drop for R<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        let _ = *self.0;
    }
}

#[ensures(true)]
pub fn consume<T>(_t: T) {}

#[ensures((^h.0)@ == 0u32)]
pub fn plain_dropped_at_scope_end(h: H<'_>) {
    *h.0 = 0;
}

#[ensures((^h.0)@ == 0u32)]
pub fn plain_handed_to_a_generic_callee(h: H<'_>) {
    *h.0 = 0;
    consume(h);
}

#[ensures((^r.0)@ == 0u32)]
pub fn reading_guard_dropped_at_scope_end(r: R<'_>) {
    *r.0 = 0;
}

#[ensures((^r.0)@ == 0u32)]
pub fn reading_guard_handed_to_mem_drop(r: R<'_>) {
    *r.0 = 0;
    drop(r);
}
