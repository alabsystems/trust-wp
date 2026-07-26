// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Note: ghost! macro now works on stable Rust (no nightly features required)

//! Ghost block move validation: cases that should FAIL.
//!
//! All functions in this module should produce validation errors
//! when run through trust-wp-driver.

use trust_wp_std::ghost;
#[allow(unused_imports)]
use trust_wp_std::ghost::Ghost;

/// Moving a non-Copy value into a ghost block should be rejected.
///
/// Expected validation error:
/// ```text
/// error: cannot move non-ghost value in ghost block; consider borrowing with &
/// ```
#[allow(dead_code)]
pub fn move_non_copy_in_ghost(v: Vec<i32>) {
    let _ = ghost! {
        {
            // This should be flagged as an error:
            // Moving a Vec<i32> (non-Copy, non-Ghost) into a ghost block
            // violates the "No Move of Non-Ghost" rule.
            let _moved = v;  // ERROR: v is non-Copy, non-Ghost
        }
    };
}

/// Multiple non-Copy moves should each be reported.
///
/// When multiple non-Copy values are moved, each should generate
/// a separate error message.
#[allow(dead_code)]
pub fn multiple_moves_in_ghost(v1: Vec<i32>, v2: String, s: Box<i32>) {
    let _ = ghost! {
        {
            let _a = v1;  // ERROR: Vec is non-Copy
            let _b = v2;  // ERROR: String is non-Copy
            let _c = s;   // ERROR: Box is non-Copy
        }
    };
}

/// Nested ghost blocks with moves.
///
/// Even in nested contexts, move validation should apply.
#[allow(dead_code)]
pub fn nested_ghost_moves(v: Vec<i32>) {
    let _ = ghost! {
        {
            let inner = Ghost::new(42);
            let _ = ghost! {
                {
                    let _g = inner;  // OK: Ghost<T> is Copy (no error)
                }
            };
            // This should still error because v is from outside all ghost blocks
            let _moved = v;  // ERROR: v is non-Copy, non-Ghost
        }
    };
}

/// Move in function call argument.
///
/// When a non-Copy value is passed to a function inside a ghost block,
/// it should be detected as a move.
#[allow(dead_code)]
fn consume_vec(_v: Vec<i32>) {}

#[allow(dead_code)]
pub fn move_in_call(v: Vec<i32>) {
    let _ = ghost! {
        {
            // Passing v to a function that takes ownership is a move
            consume_vec(v);  // ERROR: v is non-Copy, non-Ghost
        }
    };
}

/// Struct field initialization with move.
#[allow(dead_code)]
struct Container {
    data: Vec<i32>,
}

#[allow(dead_code)]
pub fn move_in_struct(v: Vec<i32>) {
    let _ = ghost! {
        {
            // Creating a struct that takes ownership is a move
            let _c = Container { data: v };  // ERROR: v is non-Copy
        }
    };
}

/// Tuple construction with move.
#[allow(dead_code)]
pub fn move_in_tuple(v: Vec<i32>, s: String) {
    let _ = ghost! {
        {
            // Tuple construction moves values
            let _t = (v, s);  // ERROR: both are non-Copy
        }
    };
}

/// Match scrutinee with move.
#[allow(dead_code)]
pub fn move_in_match(opt: Option<Vec<i32>>) {
    let _ = ghost! {
        {
            // Match scrutinee is consumed
            match opt {  // ERROR: Option<Vec> is non-Copy
                Some(_v) => {}
                None => {}
            }
        }
    };
}

/// String is non-Copy.
#[allow(dead_code)]
pub fn move_string(s: String) {
    let _ = ghost! {
        {
            let _moved = s;  // ERROR: String is non-Copy
        }
    };
}

/// Box is non-Copy.
#[allow(dead_code)]
pub fn move_box(b: Box<i32>) {
    let _ = ghost! {
        {
            let _moved = b;  // ERROR: Box is non-Copy
        }
    };
}

fn main() {}
