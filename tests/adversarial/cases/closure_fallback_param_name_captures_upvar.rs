//@ expect: reject
//@ also-verified: h
//@ mechanism: a closure's destructured parameter is registered under the positional name `arg0`
//@ mechanism: (`name_unnamed_params` keeps it apart from the closure's other PARAMETERS only). The
//@ mechanism: closure captures the enclosing function's parameter, also named `arg0`, and its
//@ mechanism: clause names that capture; the clause is read with `arg0` bound to the closure's own
//@ mechanism: parameter, so `arg0.1` is the pattern's second component instead of the capture's.
//@ mechanism: D-177 then states `p` as `(arg0.0)` over the same name.
//@ accept-means: a closure clause's captured variable was read as the closure's own destructured
//@ accept-means: parameter because the two share the positional fallback name.
//@ WHY THE CONTRACT IS FALSE: `h((0, 9))` calls `f((1, 1))`, which returns 2; the clause says
//@ WHY THE CONTRACT IS FALSE: `1 + arg0.1`, which is 10.
//@ fixed-by: D-179 — the closure's destructured parameter is `__twp_arg0`, apart from the capture,
//@ fixed-by: and a clause that reads `arg0` with no parameter of that name is refused, since every
//@ fixed-by: call of the closure binds `arg0` to an argument by position.
//@ teeth: ACCEPTED (exit 0, `h::{closure#0} verified`) at the reviewed head. With every crate at the
//@ teeth: campaign base the closure is credited the same way and only `h` FAILED, on the call's
//@ teeth: `requires` read with `p` free; `#[ensures(result == arg0.1)] |(_p, q): (u32, u32)| q`, which
//@ teeth: names no binding, is ACCEPTED on both. The twin that names the enclosing parameter `w` and
//@ teeth: is otherwise identical has the closure FAILED on both, so the clause's `arg0` IS read as the
//@ teeth: closure's parameter. `h` itself is true (the call's arguments are below 100) and is
//@ teeth: credited on purpose.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(non_snake_case)]
pub fn h(arg0: (u32, u32)) -> u32 {
    let f = #[requires(p < 100u32 && _q < 100u32)]
    #[ensures(result == p + arg0.1)]
    |(p, _q): (u32, u32)| p + _q;
    let _ = arg0;
    f((1, 1))
}
