//@ expect: reject
//@ mechanism: D-118 rule 4 records a closure that writes through a captured `&mut` "wherever it goes
//@ mechanism: except a direct call", but it looks only at `Call` terminators and unsizing casts. A
//@ mechanism: closure moved into a user struct by an aggregate and run by that struct's `Drop` impl
//@ mechanism: goes through neither: the drop glue is a `Drop` terminator, which D-4 gives no
//@ mechanism: logical effect. The host reads `c` after the guard's scope at its value before the
//@ mechanism: borrow.
//@ accept-means: `host` is reported `verified` although dropping the guard runs the closure, which
//@ accept-means: sets `c` to 5 before `host` returns it.
//@ WHY THE CONTRACT IS FALSE: `host()` returns 5; compiled and run as a plain program it prints 5.
//@ fixed-by: D-140: the guard's `Drop` impl hands `&mut self.0` to a call, so its glue may write, and
//@ fixed-by: the drop re-binds what the guard reaches, the closure's captured `c` included. The
//@ fixed-by: `#[trusted]` spelling is drop_impl_trusted_write_through_held_mut_unseen.
//@ fixed-by: drop_impl_write_through_held_mut_unseen is the closure-free form of the defect.
//@ teeth: MEASURED on the binary before D-118, at D-118's head and with D-140's hand-off disabled:
//@ teeth: the `Drop` impl FAILED (it cannot state `F`'s precondition) and `host` verified on each.
//@ teeth: With D-140 `host` is `unknown`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Guard<F: FnMut()>(pub F);

impl<F: FnMut()> Drop for Guard<F> {
    #[requires(true)]
    fn drop(&mut self) {
        (self.0)()
    }
}

#[ensures(result@ == 0)]
pub fn host() -> u32 {
    let mut c = 0u32;
    {
        let _g = Guard(|| c = 5);
    }
    c
}
