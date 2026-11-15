//@ expect: reject
//@ mechanism: the termination spelling of loop_body_local_drop_glue_write_unseen_by_invariant: a loop
//@ mechanism: `#[variant(n@)]` whose decrease is read through a body-local that drop glue writes,
//@ mechanism: `let mut m = n - 1; { let _g = G(&mut m); } n = m;` (and `mem::drop(g)`), with `G::drop`
//@ mechanism: storing 5. The loop lane checks the variant against `m`'s value before the glue
//@ mechanism: (`n - 1`), so a loop that never exits is credited under `#[check(terminates)]`. The same
//@ mechanism: body with the store written directly (`m = 5`) or through a borrow (`let r = &mut m;
//@ mechanism: *r = 5`) is refuted (`loop invariant`), and `n = n` is refuted.
//@ accept-means: a loop that does not terminate is credited `verified` under `#[check(terminates)]`.
//@ WHY THE CONTRACT IS FALSE: from `n = 10` the glue sets `n` to 5 on the fifth iteration and on every
//@ WHY THE CONTRACT IS FALSE: one after it (`m = 4`, then 5): the loop never exits.
//@ fixed-by: D-140: the loop-body walk forgets a body-local the body lends out where a `Drop` or a call
//@ fixed-by: may write it, so the decrease is checked against a value nothing constrains.
//@ teeth: MEASURED on one binary with the walk's forgetting disabled by an env knob (never committed):
//@ teeth: ACCEPTED, exit 0, `scope_end` and `mem_drop` verified; with it, each is FAILED (`loop
//@ teeth: invariant`). Control: loop_variant_drop_glue_reads_only_control, verified either way.
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
#[requires(true)]
pub fn scope_end() {
    let mut n = 10u32;
    #[variant(n@)]
    while n > 0 {
        let mut m = n - 1;
        {
            let _g = G(&mut m);
        }
        n = m;
    }
}

#[check(terminates)]
#[requires(true)]
pub fn mem_drop() {
    let mut n = 10u32;
    #[variant(n@)]
    while n > 0 {
        let mut m = n - 1;
        let g = G(&mut m);
        std::mem::drop(g);
        n = m;
    }
}
