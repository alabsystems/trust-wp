//@ expect: reject
//@ mechanism: the `#[trusted]` spelling of drop_impl_write_through_held_mut_unseen and of
//@ mechanism: drop_glue_runs_capture_writing_closure_unseen. A trusted `Drop` impl is not verified, and
//@ mechanism: its contract (`requires(true)`, no `ensures`) says nothing about what it writes; D-140 reads
//@ mechanism: the impl's MIR, not its contract, to decide whether its glue may write, so trusting the body
//@ mechanism: changes nothing.
//@ accept-means: a host is reported `verified` although a trusted guard's `Drop` impl sets `c` to 5, directly
//@ accept-means: or through the closure it runs.
//@ WHY THE CONTRACT IS FALSE: both hosts return 5.
//@ fixed-by: D-140
//@ teeth: MEASURED: with D-140's hand-off disabled both hosts are `verified` (the run is never a
//@ teeth: clean accept, because no crate holding a `#[trusted]` item is, but the per-function gate
//@ teeth: flags both credits); with it both are `unknown`. A trusted `Drop` impl that only reads
//@ teeth: leaves its host `verified` (probed; it cannot be a control for the same reason).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[trusted]
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = 5;
    }
}

pub struct Guard<F: FnMut()>(pub F);

impl<F: FnMut()> Drop for Guard<F> {
    #[trusted]
    #[requires(true)]
    fn drop(&mut self) {
        (self.0)()
    }
}

#[ensures(result@ == 0)]
pub fn held() -> u32 {
    let mut c = 0u32;
    {
        let _g = G(&mut c);
    }
    c
}

#[ensures(result@ == 0)]
pub fn closure() -> u32 {
    let mut c = 0u32;
    {
        let _g = Guard(|| c = 5);
    }
    c
}
