//@ expect: reject
//@ mechanism: as logic_body_item_shadows_free_fn, through a glob: the owner's body imports
//@ mechanism: `c::*`, whose `k` shadows the crate root's `use a::k` for the clause, which is
//@ mechanism: type-checked at the head of that body. A glob counts when what it globs has a child
//@ mechanism: of the clause's name (logic/identity.rs glob_may_import).
//@ accept-means: the clause was read with `a::k` although the body's glob brings in `c::k`.
//@ WHY THE CONTRACT IS FALSE: `c::k(x)` is `x + 2`; `g(0)` returns 0.
//@ teeth: LIVE exit-0 false accept on the campaign tip 2e903433 (its logic-identity resolver);
//@ teeth: rejected by refusal once the glob withholds the module's answer.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k(p: Int) -> Int { p }
}
pub mod c {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k(p: Int) -> Int { p + 2 }
}
use a::k;

#[ensures(result@ == k(x@))]
pub fn g(x: u32) -> u32 {
    #[allow(unused_imports)]
    use crate::c::*;
    x
}
