//@ expect: reject
//@ mechanism: logic/discovery.rs get_param_names_from_hir named a `_` logic parameter `arg{idx}`, duplicating a real parameter literally named `arg{idx}`; the later substitution binding won when the body was unfolded.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ accept-means: f(a, b) was unfolded to b.
//@ teeth: exit-0 false accept on wp-campaign 3eede3c2 (review rev28/l1); FAILED after the fix.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// logic fn whose `_` fallback name `arg1` collides with a real parameter `arg1`.
#[logic]
pub fn f(arg1: Int, _: Int) -> Int { arg1 }
// WRONG: f(a, b) == a, and the body returns b.
#[ensures(result@ == f(a@, b@))]
pub fn g(a: u32, b: u32) -> u32 { b }
