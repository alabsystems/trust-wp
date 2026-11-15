//@ expect: reject
//@ mechanism: two enum variants carrying DIFFERENT types whose logic functions collide on the
//@ mechanism: short name `val`. Each arm spells `_.val()`; only the arm's own field type says
//@ mechanism: which definition that is. If the match-arm type carry gives every arm the same
//@ mechanism: type (the scrutinee's, or the first variant's field), `y.val()` in the `Two` arm
//@ mechanism: binds `A::val` (5) instead of `B::val` (7).
//@ accept-means: an arm binding was typed from the wrong variant, so a postcondition written
//@ accept-means: over a match is discharged against another variant's logic definition.
//@ accept-means: Refuted by `g(E::Two(B))`: the second arm requires 7 == 5.
//@ teeth: ACCEPTED (false accept, exit 1) on 2026-09-20 with `constructor_field_types`
//@ teeth: stubbed to hand every arm the FIRST variant's field types — a one-line local revert;
//@ teeth: see docs/s77-decision-test-teeth.md (S12). The same stub reddens the unit test
//@ teeth: `logic::identity::tests::match_arm_bindings_carry_the_variant_field_type`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct A;
pub struct B;
impl A { #[logic(open)] pub fn val(self) -> Int { pearlite!{5} } }
impl B { #[logic(open)] pub fn val(self) -> Int { pearlite!{7} } }
pub enum E { One(A), Two(B) }
#[ensures(match e { E::One(x) => x.val() == 5, E::Two(y) => y.val() == 5 })]
pub fn g(e: E) {}
