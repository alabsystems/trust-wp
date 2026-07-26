// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost program-context checks that should FAIL.
//!
//! Ghost values may be created and inspected inside `ghost!` blocks. Direct
//! runtime use in ordinary program code is rejected.

use trust_wp_std::{ghost, ghost::Ghost};

#[allow(dead_code)]
pub fn create_ghost_in_program() {
    let _g = Ghost::new(1);
}

#[allow(dead_code)]
pub fn deref_ghost_in_program() {
    let g = ghost! { 2 };
    let _: &i32 = &*g;
}

#[allow(dead_code)]
pub fn into_inner_ghost_in_program() {
    let g = ghost! { 2 };
    let _: i32 = g.into_inner();
}

#[allow(dead_code)]
pub fn mutate_ghost_in_program() {
    let mut g = ghost! { 2 };
    *g = 3;
}

fn main() {}
