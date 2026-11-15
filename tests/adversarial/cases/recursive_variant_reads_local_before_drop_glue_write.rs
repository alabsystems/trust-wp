//@ expect: reject
//@ mechanism: a recursive `#[variant(n@)]` whose recursive call is handed a local after drop glue wrote
//@ mechanism: it: `let mut m = 0; { let _g = G(&mut m); } f(m)` (and `mem::drop(g)`), with `G::drop` storing
//@ mechanism: 5. The recursive-call walk (`extract_recursive_calls_from_block`) follows a `Drop` and a
//@ mechanism: non-recursive call to their targets without re-binding, so the argument is read as 0 and
//@ mechanism: `0 < n` discharges the decrease. The same body with `m = 5` written directly is refuted
//@ mechanism: (`variant decrease`). The walk also misses a store through a borrow and a callee's `^`:
//@ mechanism: recursive_variant_reads_local_before_borrow_write.
//@ accept-means: a recursive function that does not terminate is credited `verified ✓ (termination)` under
//@ accept-means: `#[check(terminates)]`, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `scope_end(1)` calls `scope_end(5)`, which calls `scope_end(5)` forever
//@ WHY THE CONTRACT IS FALSE: (the glue stores 5 into `m` before each call); likewise `mem_drop`.
//@ fixed-by: D-140: the recursive-call walk forgets a local the body lends out where a `Drop` or a call
//@ fixed-by: may write it (`locals_changed_by_handoff`), so the call is handed a fresh value.
//@ teeth: MEASURED on one binary with the walk's forgetting disabled by an env knob (never committed):
//@ teeth: ACCEPTED, exit 0, both functions `verified ✓ (termination)`; with it, each is FAILED (`variant
//@ teeth: decrease`). Control: recursive_variant_drop_glue_reads_only_control, verified either way.
//@ also-verified: <G<'_> as std::ops::Drop>::drop
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

#[check(terminates)]
#[variant(n@)]
pub fn scope_end(n: u32) {
    if n == 0 {
        return;
    }
    let mut m = 0u32;
    {
        let _g = G(&mut m);
    }
    scope_end(m);
}

#[check(terminates)]
#[variant(n@)]
pub fn mem_drop(n: u32) {
    if n == 0 {
        return;
    }
    let mut m = 0u32;
    let g = G(&mut m);
    std::mem::drop(g);
    mem_drop(m);
}
