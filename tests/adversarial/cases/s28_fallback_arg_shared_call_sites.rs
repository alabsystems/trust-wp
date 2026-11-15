//@ expect: reject
//@ mechanism: an untranslatable call argument became the placeholder Var("arg{idx}"), which aliased a caller variable literally named `arg{idx}` and was shared by every call with the same argument position.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ accept-means: id(K1) and id(K2) were equated with the same placeholder.
//@ teeth: exit-0 false accept on c743b394 (probes6/p_fb4).
//@ also-verified: id
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[derive(Clone, Copy, PartialEq)]
pub struct P { pub x: u32 }
pub const K1: P = P { x: 1 };
pub const K2: P = P { x: 2 };
#[ensures(result == v)]
pub fn id(v: P) -> P { v }
// WRONG: id(K1).x == 1 and id(K2).x == 2.
#[ensures(result)]
pub fn g() -> bool { id(K1).x == id(K2).x }
