//@ expect: reject
//@ mechanism: body extraction returned None for an unconditionally panicking body and the ensures(true) was credited as verified
//@ accept-means: a function whose body always panics was accepted. FALSE: f(0) panics.
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: verified on 213fc6e (review probe r7, 'body extraction returned None')
//@ verdict: failed
//@ fn-failed: f
//@ teeth: wp-s81 PINNED HARDER. The goal that rejects this body is the literal `false`
//@ teeth: extraction injects for a body that can never return — Creusot states the same
//@ teeth: goal (the Abort is unreachable) and trust-wp really can refute it. wp-s81 D1
//@ teeth: withholds refutations over injected `false` goals, so this one is carved out by
//@ teeth: COUNT (`panic_unreachability_obligations`) and the pin below is what stops the
//@ teeth: carve-out from being dropped: without it this case silently degrades to
//@ teeth: `unknown` and nobody notices.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(_x: i32) {
    panic!()
}
