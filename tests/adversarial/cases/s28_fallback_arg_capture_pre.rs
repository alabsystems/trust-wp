//@ expect: reject
//@ mechanism: an untranslatable call argument became the placeholder Var("arg{idx}"), which aliased a caller variable literally named `arg{idx}` and was shared by every call with the same argument position.
//@ fixed-by: wp-s28 (anon-param name generators / fresh fallback call-argument placeholders)
//@ accept-means: need(K)`s precondition was discharged by the caller`s requires on arg0.
//@ teeth: exit-0 false accept on c743b394 (probes6/p_fb5); renamed q FAILED.
//@ also-verified: need
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[derive(Clone, Copy, PartialEq)]
pub struct P { pub x: u32 }
pub const K: P = P { x: 7 };
#[requires(v.x > 100u32)]
pub fn need(v: P) {}
// WRONG: K.x == 7 violates need's precondition.
#[requires(arg0.x > 100u32)]
pub fn g(arg0: P) { need(K) }
