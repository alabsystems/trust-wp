//@ expect: reject
//@ mechanism: a logic function's parameters are values: a `&mut i32` parameter is one value and a
//@ mechanism: clause passes the current value of the borrow it names. A final read inside it
//@ mechanism: (`^q`, `resolve(q)`) therefore read the current one, so `unchanged(p)` (`^q == *q`)
//@ mechanism: folded to a tautology over one value, and `flipped(p)` beside `^p == *p + 1` made a
//@ mechanism: caller vacuous. Every D-107/D-102 refusal of a final value reads the clause's own
//@ mechanism: syntax and never saw the `^` the helper hides.
//@ accept-means: a function is credited with its `&mut` parameter left unchanged although its body
//@ accept-means: writes it, lends it into another parameter, writes it through a cell, or passes it
//@ accept-means: to a callee that writes it; or a caller derives `false` from a true callee.
//@ WHY THE CONTRACT IS FALSE: `set5`, `set5_flipped` and `set5_wraps` store 5 under `*p != 5`;
//@ WHY THE CONTRACT IS FALSE: `stash_logic` stores the borrow in `slot` and `stash_logic_caller`
//@ WHY THE CONTRACT IS FALSE: writes 5 through it under `*x != 5`; `push_logic` moves it into `v`,
//@ WHY THE CONTRACT IS FALSE: whose holder may write it; `cell_set` sets the cell to 5 (an entry
//@ WHY THE CONTRACT IS FALSE: content 1 refutes it); `keep_logic_caller`'s callee stores 7 under
//@ WHY THE CONTRACT IS FALSE: `*p != 7`; `derive_false` ends, so `false` does not hold.
//@ fixed-by: D-108 (a logic function reading a final value is withdrawn where it is defined, and
//@ fixed-by: the encoder's door refuses every goal that may name it)
//@ teeth: MEASURED (debug driver): f6039647 verifies `set5`, `set5_flipped`, `set5_wraps`,
//@ teeth: `stash_logic`, `stash_logic_caller`, `push_logic`, `cell_set` and `keep_logic_caller`,
//@ teeth: and `derive_false` is vacuous; on D-108 each is refused by name and `keep` verifies.
//@ also-verified: keep
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::cell::Cell;

use creusot_std::prelude::*;

#[logic(open, prophetic)]
pub fn unchanged(q: &mut i32) -> bool {
    pearlite! { ^q == *q }
}

#[logic(open, prophetic)]
pub fn flipped(q: &mut i32) -> bool {
    pearlite! { *q == ^q }
}

#[logic(open, prophetic)]
pub fn wraps(q: &mut i32) -> bool {
    pearlite! { unchanged(q) }
}

#[logic(open, prophetic)]
pub fn cell_unchanged(q: &mut Cell<i32>) -> bool {
    pearlite! { ^q == *q }
}

#[requires(*p != 5i32)]
#[ensures(unchanged(p))]
pub fn set5(p: &mut i32) {
    *p = 5;
}

#[requires(*p != 5i32)]
#[ensures(flipped(p))]
pub fn set5_flipped(p: &mut i32) {
    *p = 5;
}

#[requires(*p != 5i32)]
#[ensures(wraps(p))]
pub fn set5_wraps(p: &mut i32) {
    *p = 5;
}

#[ensures(unchanged(p))]
pub fn stash_logic<'a>(p: &'a mut i32, slot: &mut Option<&'a mut i32>) {
    *slot = Some(p);
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn stash_logic_caller(x: &mut i32) {
    let mut slot: Option<&mut i32> = None;
    stash_logic(x, &mut slot);
    if let Some(r) = slot {
        *r = 5;
    }
}

#[ensures(unchanged(p))]
pub fn push_logic<'a>(p: &'a mut i32, v: &mut Vec<&'a mut i32>) {
    v.push(p);
}

#[ensures(cell_unchanged(x))]
pub fn cell_set(x: &mut Cell<i32>) {
    x.set(5);
}

#[ensures(^v == *v)]
pub fn keep(v: &mut i32, p: &mut i32) {
    *p = 7;
}

#[requires(*p != 7i32)]
#[ensures(unchanged(p))]
pub fn keep_logic_caller(v: &mut i32, p: &mut i32) {
    keep(v, &mut *p)
}

#[requires(*p < 100i32)]
#[ensures(^p == *p + 1i32 && flipped(p))]
pub fn inc_and_flipped(p: &mut i32) {
    *p += 1;
}

#[requires(*x < 100i32)]
#[ensures(false)]
pub fn derive_false(x: &mut i32) {
    inc_and_flipped(x);
}
