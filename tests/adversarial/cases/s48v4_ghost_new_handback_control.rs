//@ expect: verify
//@ xfail: the honest twin of s48v4_ghost_new_handback is NOT provable today: advancing `x` at the `Ghost::new` call havocs it, so the TRUE post-write value is unrecoverable. Measured on this program: `status=unknown reason=sort-coercion bridge in negated goal`, base_exit_code=2. Retire this xfail when a write through a reborrow handed back out of a ghost container flows back to the borrowed place — the same fix that empties MUT_REBORROW_PROJECTION_PATHS_KNOWN_UNSOUND.
//@ mechanism: control for the `Ghost::new` handback arm — the same program asserting the value the write actually leaves behind.
//@ accept-means: n/a (control)
//@ teeth: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
use creusot_std::ghost::Ghost;

pub fn k() {
    let mut x = 5i32;
    ghost! {
        let h = Ghost::new(&mut x);
        let r: &mut i32 = h.into_inner();
        *r = 7;
    };
    proof_assert!(x == 7i32);
}
