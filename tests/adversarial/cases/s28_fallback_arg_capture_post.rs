//@ expect: reject
//@ mechanism: an untranslatable call argument became the placeholder Var("arg{idx}"), which aliased a caller variable literally named `arg{idx}` and was shared by every call with the same argument position.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ accept-means: g proved result == its own arg0 from id(K).
//@ teeth: exit-0 false accept on c743b394 (probes6/p_fb1); the same file with the parameter renamed q FAILED.
//@ also-verified: id
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[derive(Clone, Copy, PartialEq)]
pub struct P { pub x: u32 }
pub const K: P = P { x: 7 };
#[ensures(result == v)]
pub fn id(v: P) -> P { v }
#[ensures(result == arg0)]
pub fn g(arg0: P) -> P { id(K) }
