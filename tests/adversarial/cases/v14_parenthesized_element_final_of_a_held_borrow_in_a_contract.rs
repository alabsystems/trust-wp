//@ expect: reject
//@ mechanism: a contract's `^` of an element of a `&mut` parameter's view, written so the element is
//@ mechanism: its operand (`^(x@[0])`, and the index spelling `^(x[0])` is the same read). The contract
//@ mechanism: lane's `held_through_a_mutable_parameter` walked `*` and field getters only and `holds`
//@ mechanism: exempts `x@`, so nothing refused it; Phase 3 distributed `^` into the view's element,
//@ mechanism: `(^x)@[0]`, the element the OUTER borrow is left with (D-129). The unparenthesized
//@ mechanism: `^x@[0]` is a different claim: the parser reads `^x@` as `(^x)@` (as Creusot does), so it
//@ mechanism: compares the element the outer borrow is left with to its current one, which an untouched
//@ mechanism: body makes equal, and it is TRUE; only the parenthesized operand is a held borrow's final.
//@ accept-means: a contract stating that a borrow the caller keeps in an array or `Vec` is resolved at
//@ accept-means: return is proved (or proved by ay and withheld by a certificate gate alone).
//@ WHY THE CONTRACT IS FALSE: the element borrow is the caller's after the call; writing 7 through it
//@ WHY THE CONTRACT IS FALSE: after the call makes `^(x@[0])` 7 while `*(x@[0])` was 1.
//@ fixed-by: D-129 (the contract lane walks views and elements to the parameter)
//@ refused-with: final value of a value held through the `&mut` parameter `x`
//@ teeth: MEASURED (debug driver, ay 57a37e51): on 2c859203 vec_view reached ay, which answered unsat
//@ teeth: (`unknown (proof-trusted)`, the certificate gate alone), and arr_view and arr_view_bool were
//@ teeth: unknown (quantifier-unhandled); arr_index was refused at placement there too, by the `holds`
//@ teeth: walk. With D-129 all four are refused at placement.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^(x@[0]) == *(x@[0]))]
pub fn arr_view(x: &mut [&mut i32; 1]) {}

#[ensures(^(x@[0]) == *(x@[0]))]
pub fn arr_view_bool(x: &mut [&mut bool; 1]) {}

#[requires(x@.len() == 1)]
#[ensures(^(x@[0]) == *(x@[0]))]
pub fn vec_view(x: &mut Vec<&mut i32>) {}

#[ensures(^(x[0]) == *(x[0]))]
pub fn arr_index(x: &mut [&mut i32; 1]) {}
