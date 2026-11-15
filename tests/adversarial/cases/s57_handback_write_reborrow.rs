//@ expect: reject
//@ mechanism: same defect as s57_handback_write_callee_only, reached through an explicit reborrow `&mut *p` instead of a bare `p`. The reborrow is extracted as the parameter carrier too, so the identity collapse is unchanged; the guard has to key on the STORE, not on the syntactic return form.
//@ fixed-by: wp-s57 435abd9b
//@ accept-means: the refusal is keyed on the return expression's shape rather than on the write, so writing `&mut *p` is enough to get the entry pointee back.
//@ WHY THE PROGRAM IS WRONG: `*result` is 9 at the return; `*p` is the entry value.
//@ teeth: A/B'd: ACCEPTED (`trust-wp: hb_reborrow verified`,
//@ teeth: `base_exit_code=0`) on a wp-campaign ce1d56fc build of this sandbox
//@ teeth: as an isolated probe of the `&mut *p` reborrow-return spelling, rejected here.
//@ verdict: failed
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == p)]
pub fn hb_reborrow(p: &mut u32) -> &mut u32 {
    *p = 9;
    &mut *p
}
