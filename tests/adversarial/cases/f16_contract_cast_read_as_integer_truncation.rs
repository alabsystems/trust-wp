//@ expect: reject
//@ mechanism: a contract lowers `e as u8` to the integer arithmetic Rust's `as` performs between integer types,
//@ mechanism: and leaves a non-integer operand to the encoder, which refuses arithmetic over a float. Before
//@ mechanism: D-217 an `f16`/`f128` value had no sort and was read at the integer sort, so the clauses below
//@ mechanism: were identities of integer truncation, true of every integer; the float casts saturate instead.
//@ mechanism: Under D-217 the value is its format's uninterpreted sort and the arithmetic over it is refused,
//@ mechanism: as it is over an `f32`.
//@ accept-means: `narrow_through_u16(300.0)`: `(300.0 as u16) as u8` is `44` and `300.0 as u8` is `255`;
//@ accept-means: `through_i8(-1.0)`: `(-1.0 as i8) as u8` is `255` and `-1.0 as u8` is `0`; the same for
//@ accept-means: `wide_through_u16(300.0)`. An accept claims each pair is equal.
//@ refused-with: over a float operand
//@ fixed-by: D-217
//@ teeth: a pin: on the merged campaign tip before D-217 ay did not decide the integer reading (each
//@ teeth: `unknown (timeout)`), so nothing was credited, and the `refused-with` line was absent; the campaign
//@ teeth: tip, where an `f16` was a real number, withheld each refutation as a sort-coercion bridge. Under
//@ teeth: D-217 each clause is refused at encoding.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(f16)]
#![feature(f128)]

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((h as u16) as u8 == h as u8)]
pub fn narrow_through_u16(h: f16) {}

#[ensures((h as i8) as u8 == h as u8)]
pub fn through_i8(h: f16) {}

#[ensures((q as u16) as u8 == q as u8)]
pub fn wide_through_u16(q: f128) {}
