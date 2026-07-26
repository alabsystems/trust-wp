// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Direct mutable Ghost dereference in program context should FAIL.

use std::ops::DerefMut;

use trust_wp_std::{ghost, ghost::Ghost};

#[allow(dead_code)]
pub fn explicit_mutate_ghost_in_program() {
    let mut g: Ghost<i32> = ghost! { 2 };
    let slot: &mut i32 = g.deref_mut();
    *slot = 3;
}

fn main() {}
