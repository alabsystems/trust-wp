// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Note: ghost! macro now works on stable Rust (no nightly features required)

//! Ghost block move validation: cases that should PASS.
//!
//! All functions in this module should verify successfully.

use trust_wp_std::{ghost, ghost::Ghost};

/// Moving a Ghost<T> value is allowed.
///
/// Ghost<T> types are specification-only and can be freely moved
/// within ghost blocks.
#[allow(dead_code)]
pub fn move_ghost_in_ghost(g: Ghost<i32>) {
    let _ = ghost! {
        {
            // Ghost<T> values can be moved - they're specification-only
            let _moved = g;  // OK: Ghost<T> can be moved
            let _again = _moved;  // OK: Ghost is Copy anyway
        }
    };
}

/// Copying a Copy value is allowed.
///
/// Copy types (primitives, shared references, etc.) can be freely used
/// in ghost blocks without restriction.
#[allow(dead_code)]
pub fn copy_in_ghost(x: i32, y: f64, z: bool) {
    let _ = ghost! {
        {
            // Copy types can be used freely
            let _a = x;  // OK: i32 is Copy
            let _b = y;  // OK: f64 is Copy
            let _c = z;  // OK: bool is Copy
            let _d = (x, y, z);  // OK: tuple of Copy types is Copy
        }
    };
}

/// Borrowing a non-Copy value is allowed.
///
/// The error message suggests using `&` to borrow. This verifies
/// that borrowing is a valid workaround.
#[allow(dead_code)]
pub fn borrow_in_ghost(v: Vec<i32>) {
    let _ = ghost! {
        {
            // Borrowing is allowed - doesn't consume the value
            let _borrowed = &v;  // OK: shared reference is Copy
            let _len = Ghost::new(v.len());  // OK: v.len() returns Copy type
        }
    };
    // v is still usable after the ghost block
    let _ = v.len();
}

/// Variables declared inside the ghost block can be moved freely.
#[allow(dead_code)]
pub fn move_local_in_ghost() {
    let _ = ghost! {
        {
            // Variables declared inside the ghost block are local
            let local_vec = Vec::<i32>::new();
            let _moved = local_vec;  // OK: local_vec is local to ghost block
        }
    };
}

/// Shared references from outside are Copy.
#[allow(dead_code)]
pub fn shared_ref_in_ghost(data: &Vec<i32>) {
    let _ = ghost! {
        {
            // Shared references are Copy, so this is fine
            let _ref1 = data;  // OK: &Vec<i32> is Copy
            let _ref2 = data;  // OK: can copy the reference multiple times
            let _len = Ghost::new(data.len());
        }
    };
}

/// Arrays of Copy types are Copy.
#[allow(dead_code)]
pub fn array_copy_in_ghost(arr: [i32; 5]) {
    let _ = ghost! {
        {
            let _a = arr;  // OK: [i32; 5] is Copy
            let _b = arr;  // OK: can copy multiple times
        }
    };
}

fn main() {}
