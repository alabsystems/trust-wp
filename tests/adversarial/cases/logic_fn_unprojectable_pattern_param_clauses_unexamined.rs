//@ expect: reject
//@ verdict: error
//@ refused-with: is kept opaque and its clauses are refused
//@ also-verified: g
//@ mechanism: a logic function whose parameter pattern binds a name with no projection of the
//@ mechanism: parameter (here through the reference the pattern spells, `&(p, _q)`) is kept opaque by
//@ mechanism: D-177 and its clauses are dropped, since they mention a name nothing can state. What is
//@ mechanism: dropped is then examined by nobody: `k`'s own `ensures` was never checked, and with
//@ mechanism: every other function verified the run said nothing was wrong.
//@ accept-means: the run exited 0 although `k`'s `ensures` was dropped unexamined.
//@ WHY THE CONTRACT IS FALSE: `k(&(1, 0))` is 1, not above 1000. `g` is true and is credited on
//@ WHY THE CONTRACT IS FALSE: purpose.
//@ fixed-by: D-177 — a logic definition kept opaque for a binding with no projection refuses the
//@ fixed-by: run, as a clause that does not parse does.
//@ teeth: exit 0 (`g verified`, nothing about `k`) with the refusal of the run removed and the
//@ teeth: rest of D-177 in place (measured in place); the twin
//@ teeth: logic_fn_projectable_pattern_param_ensures_checked.rs, the same function over a by-value
//@ teeth: pattern, is refuted on its own `ensures`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
#[ensures(result > 1000)]
pub fn k(&(p, _q): &(Int, Int)) -> Int { p }

#[ensures(result == 1u32)]
pub fn g() -> u32 { 1 }
