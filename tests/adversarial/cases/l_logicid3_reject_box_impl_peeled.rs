//@ expect: reject
//@ mechanism: a receiver-style logic call auto-derefs through `Box`, and the encoder gives
//@ mechanism: `Box<T>` exactly `T`'s solver sort, so `peel_transparent_boxes` strips the box
//@ mechanism: before selecting a definition. Here the FAMILY itself has a member defined on
//@ mechanism: the box (`impl Peek for Box<W>`), which is the definition Rust selects for a
//@ mechanism: `Box<W>` receiver. Peeling anyway binds `W::peek` (5) to a call that means
//@ mechanism: `<Box<W> as Peek>::peek` (7).
//@ accept-means: a box receiver was resolved to the INNER type's logic definition while Rust
//@ accept-means: selects the box's own, so every clause over a boxed receiver is discharged
//@ accept-means: against a different definition than the program runs.
//@ teeth: ACCEPTED (false accept, exit 1) on 2026-09-20 with the `any_box_impl` bail-out
//@ teeth: stubbed to `false` (always peel) — a one-line local revert; see
//@ teeth: docs/s77-decision-test-teeth.md (S4). The same stub reddens the unit tests
//@ teeth: `a_box_impl_in_the_family_stops_the_peel` and
//@ teeth: `the_box_bailout_does_not_disturb_an_unboxed_receiver`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct W(pub u32);
pub trait Peek { #[logic(open)] fn peek(&self) -> Int; }
impl W { #[logic(open)] pub fn peek(&self) -> Int { pearlite!{5} } }
impl Peek for Box<W> { #[logic(open)] fn peek(&self) -> Int { pearlite!{7} } }
#[ensures(b.peek() == 5)]
pub fn g(b: &Box<W>) {}
