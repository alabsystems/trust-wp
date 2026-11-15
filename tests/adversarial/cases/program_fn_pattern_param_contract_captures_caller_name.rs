//@ expect: reject
//@ also-verified: g
//@ mechanism: a PROGRAM function whose parameter is a destructuring pattern (`(a, _b): (u32, u32)`)
//@ mechanism: states a contract over the pattern's binding `a`, which rustc accepts (the clause is
//@ mechanism: type-checked in the body, where `a` is bound). The callee's parameter is registered
//@ mechanism: under a positional fallback name (name_unnamed_params), so when a caller instantiates
//@ mechanism: the callee's `ensures` only the parameters are substituted and `a` stays free; it is
//@ mechanism: read in the CALLER's scope, where the caller's own parameter `a` captures it.
//@ accept-means: the callee's postcondition was instantiated with the caller's `a` instead of the
//@ accept-means: first component of the argument.
//@ WHY THE CONTRACT IS FALSE: `h(1)` is `g((7, 1))`, which returns 7, not 1. `g` itself is
//@ WHY THE CONTRACT IS FALSE: true and is credited on purpose (`also-verified`).
//@ fixed-by: D-177 — the callee's clause text names the binding as its parameter's projection
//@ fixed-by: (`a` is `__twp_arg0.0`), the one text its own verification and every caller read.
//@ teeth: ACCEPTED (exit 0) at the reviewed head and at its base alike.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == a)]
pub fn g((a, _b): (u32, u32)) -> u32 { a }

#[ensures(result == a)]
pub fn h(a: u32) -> u32 { g((7, a)) }
