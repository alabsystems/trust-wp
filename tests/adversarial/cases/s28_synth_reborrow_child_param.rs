//@ expect: reject
//@ mechanism: a plain reborrow child of `x` was named `x_rbN` (N = MIR local), the same PureExpr::Var as a parameter spelled `x_rb3`; children are now `x$rbN`.
//@ fixed-by: wp-s28 v8 (reborrow child names in the `$` namespace)
//@ accept-means: g proved it wrote 7 through x_rb3, which it never touches.
//@ teeth: exit-0 false accept on 42eabec9 (review-probes/sound1/p_rb3); control s28_synth_reborrow_child_param_control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: x_rb3 is never written
#[ensures(^x_rb3 == 7u32)]
pub fn g(x: &mut u32, x_rb3: &mut u32) { let y = &mut *x; *y = 7u32; }
