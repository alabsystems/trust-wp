//@ expect: verify
//@ mechanism: logic/discovery.rs get_param_names_from_hir named a `_` logic parameter `arg{idx}`, duplicating a real parameter literally named `arg{idx}`; the later substitution binding won when the body was unfolded.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ teeth: control: verifies after the fix.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
pub fn f(arg2: Int, _: Int, _: Int) -> Int { arg2 }
#[ensures(result@ == f(a@, b@, c@))]
pub fn g(a: u32, b: u32, c: u32) -> u32 { a }
