//@ expect: reject
//@ mechanism: a logic function whose parameter is a destructuring PATTERN (`(p, _q): (Int, Int)`)
//@ mechanism: is registered with a positional fallback name for that parameter (name_unnamed_params:
//@ mechanism: a non-`Binding` pattern is unnamed), while its body text still says `p`. `p` is then
//@ mechanism: bound by nothing in the definition, and unfolding the body at a use site substitutes
//@ mechanism: the parameters only, so the free `p` is read in the CALLER's scope: here it is captured
//@ mechanism: by the caller's own parameter `p`. Creusot destructures the argument (`let (p, _) = x`).
//@ mechanism: Here the parameter IS a binding (`whole @ (p, _q)`), so it is named `whole`, and the
//@ mechanism: sub-pattern's `p` is the free name.
//@ accept-means: the logic body's sub-pattern binding `p` was read as the caller's parameter `p`.
//@ WHY THE CONTRACT IS FALSE: `k((a, b))` is `a`; `g(5, 1, 2)` returns 5, not 1.
//@ fixed-by: D-177 — a definition names each pattern binding as its parameter's projection
//@ fixed-by: (here `p` is `whole.0`) in its body and clauses, so an unfolding substitutes the argument
//@ fixed-by: for it; a binding with no projection keeps the definition opaque and refuses the run.
//@ teeth: ACCEPTED (exit 0) at the reviewed head and at its base alike.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic(open)]
pub fn k(whole @ (p, _q): (Int, Int)) -> Int { p }

#[ensures(result@ == k((a@, b@)))]
pub fn g(p: u32, a: u32, b: u32) -> u32 { p }
