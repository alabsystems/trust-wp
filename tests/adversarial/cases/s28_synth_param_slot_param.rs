//@ expect: reject
//@ mechanism: an unnamed `&mut` parameter slot was named `_param_N`, spellable by a second parameter `_param_1`; slots are now `$param_N`.
//@ fixed-by: wp-s28 v8 (parameter-slot names in the `$` namespace)
//@ accept-means: g proved it wrote 8 through _param_1 while writing 7.
//@ teeth: unknown on 42eabec9 (review-probes/sound1/p_param); not shown exploitable before the rename.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// WRONG: the body writes 7, not 8
#[requires(*_param_1 != 7u32)]
#[ensures(^_param_1 == 8u32)]
pub fn g(_: &mut u32, _param_1: &mut u32) { *_param_1 = 7u32; }
