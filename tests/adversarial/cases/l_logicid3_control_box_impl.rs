//@ expect: verify
//@ mechanism: the control for l_logicid3_reject_box_impl_peeled — the SAME two definitions,
//@ mechanism: with each clause naming the one Rust actually selects: the box's own `peek` for
//@ mechanism: a `Box<W>` receiver, `W::peek` for an unboxed one. The peel bail-out must not
//@ mechanism: cost the unboxed receiver its definition.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct W(pub u32);
pub trait Peek { #[logic(open)] fn peek(&self) -> Int; }
impl W { #[logic(open)] pub fn peek(&self) -> Int { pearlite!{5} } }
impl Peek for Box<W> { #[logic(open)] fn peek(&self) -> Int { pearlite!{7} } }
#[ensures(b.peek() == 7)]
pub fn g(b: &Box<W>) {}
#[ensures(w.peek() == 5)]
pub fn h(w: &W) {}
