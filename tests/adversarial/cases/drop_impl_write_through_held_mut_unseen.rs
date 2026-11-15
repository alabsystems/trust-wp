//@ expect: reject
//@ mechanism: a `Drop` impl that writes through a `&mut` its value holds. D-4 gives drop glue no
//@ mechanism: logical effect, arguing that ownership prevents use-after-drop; but the memory a held
//@ mechanism: `&mut` points to is not the dropped value, and the host reads it after the borrow ends.
//@ mechanism: The same struct passed BY VALUE to a verified callee that writes through it, with no
//@ mechanism: `Drop` impl, is the call lane's twin of the defect: by_value_held_mut_written_by_callee_unseen.
//@ accept-means: `host` is reported `verified` although dropping `_g` sets `c` to 5 before `host`
//@ accept-means: returns it.
//@ WHY THE CONTRACT IS FALSE: `host()` returns 5; compiled and run as a plain program it prints 5.
//@ WHY THE CONTRACT IS FALSE: The `Drop` impl's own credit is TRUE: it states nothing and panics nowhere.
//@ fixed-by: D-140, which revises D-4: a `Drop` whose glue may run a writing `Drop` impl re-binds
//@ fixed-by: every local the dropped value reaches by reference flow, in every lane that reads it;
//@ fixed-by: and, independently, D-127: a drop of a value holding a borrow counts as a store through
//@ fixed-by: that borrow, so the host's read of `c` after it is stale and fails closed.
//@ teeth: MEASURED as ACCEPTED, exit 0, `host verified`, on the binary before D-118, at D-118's
//@ teeth: head, with D-140's hand-off disabled on a tree without D-127, and before D-127 on a tree
//@ teeth: without D-140; `host` is `unknown` under either decision alone, and stays `unknown` on a
//@ teeth: tree with both when a local knob disables D-127's drop arm. The isolating pair is
//@ teeth: drop_impl_reads_held_mut_control (the same host, a `Drop` body that only reads) and
//@ teeth: drop_impl_writes_own_field_control (a body that stores, but into its own plain field):
//@ teeth: D-140 verifies both, and D-127's drop arm, which does not read the body, refuses both.
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

#[ensures(result@ == 0)]
pub fn host() -> u32 {
    let mut c = 0u32;
    {
        let _g = G(&mut c);
    }
    c
}
