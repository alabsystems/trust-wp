// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost block write validation: cases that should FAIL.
//!
//! All functions in this module should produce validation errors
//! when run through trust-wp-driver.

use std::cell::{Cell, RefCell};

use trust_wp_std::ghost;
#[allow(unused_imports)]
use trust_wp_std::ghost::Ghost;

/// Direct assignment to an outer variable should be rejected.
///
/// Expected validation error:
/// ```text
/// error: cannot write to non-ghost variable in ghost block
/// ```
#[allow(dead_code, unused_mut, unused_assignments)]
pub fn direct_assign_outer(mut x: i32) {
    let _ = ghost! {
        {
            x = 42; // ERROR: cannot write to non-ghost variable in ghost block
        }
    };
}

/// Compound assignment (+=, -=, etc.) to an outer variable should be rejected.
///
/// Expected validation error:
/// ```text
/// error: cannot write to non-ghost variable in ghost block
/// ```
#[allow(dead_code, unused_mut, unused_assignments)]
pub fn compound_assign_outer(mut x: i32) {
    let _ = ghost! {
        {
            x += 1; // ERROR: cannot write to non-ghost variable in ghost block
        }
    };
}

/// Field write on an outer struct variable should be rejected.
///
/// Expected validation error:
/// ```text
/// error: cannot write to field/index of non-ghost variable in ghost block
/// ```
#[allow(dead_code)]
struct Point {
    x: i32,
    y: i32,
}

#[allow(dead_code, unused_mut)]
pub fn field_write_outer(mut p: Point) {
    let _ = ghost! {
        {
            p.x = 10; // ERROR: cannot write to field/index of non-ghost variable
        }
    };
}

/// Index write on an outer array/slice should be rejected.
///
/// Expected validation error:
/// ```text
/// error: cannot write to field/index of non-ghost variable in ghost block
/// ```
#[allow(dead_code, unused_mut)]
pub fn index_write_outer(mut arr: [i32; 5]) {
    let _ = ghost! {
        {
            arr[0] = 99; // ERROR: cannot write to field/index of non-ghost variable
        }
    };
}

/// Deref write through an outer pointer should be rejected.
///
/// Expected validation error:
/// ```text
/// error: cannot write to non-ghost variable in ghost block
/// ```
#[allow(dead_code, unused_mut)]
pub fn deref_write_outer(ptr: &mut i32) {
    let _ = ghost! {
        {
            *ptr = 42; // ERROR: cannot write to non-ghost variable in ghost block
        }
    };
}

/// Mutating method call on an outer variable should be rejected.
///
/// Expected validation error:
/// ```text
/// error: cannot write to non-ghost variable in ghost block
/// ```
#[allow(dead_code, unused_mut)]
pub fn method_call_mutate_outer(mut outer: Vec<i32>) {
    let _ = ghost! {
        {
            outer.push(1); // ERROR: mutating receiver outside ghost block
        }
    };
}

/// Passing mutable references to a function should be rejected.
///
/// Expected validation error:
/// ```text
/// error: cannot write to non-ghost variable in ghost block
/// ```
#[allow(dead_code, unused_mut)]
pub fn mutable_ref_argument_escape(mut a: i32, mut b: i32) {
    let _ = ghost! {
        {
            std::mem::swap(&mut a, &mut b); // ERROR: mutable reference escape
        }
    };
}

/// Writing through a local mutable-reference alias to an outer variable should be rejected.
///
/// Expected validation error:
/// ```text
/// error: cannot write to non-ghost variable in ghost block
/// ```
#[allow(dead_code, unused_mut)]
pub fn mutable_ref_alias_write_escape(mut outer: i32) {
    let _ = ghost! {
        {
            let alias = &mut outer;
            *alias = 1; // ERROR: alias points to outer non-ghost variable
        }
    };
}

/// Writing through a chained mutable-reference alias to an outer variable should be rejected.
#[allow(dead_code, unused_mut)]
pub fn mutable_ref_alias_chain_write_escape(mut outer: i32) {
    let _ = ghost! {
        {
            let alias1 = &mut outer;
            let alias2 = alias1;
            *alias2 = 2; // ERROR: chained alias still points to outer non-ghost variable
        }
    };
}

/// Interior mutability write through `Cell::set` should be rejected.
///
/// Expected validation error:
/// ```text
/// error: cannot write to non-ghost variable in ghost block
/// ```
#[allow(dead_code)]
pub fn interior_mutability_cell_set(cell: Cell<i32>) {
    let _ = ghost! {
        {
            cell.set(1); // ERROR: interior mutability write outside ghost block
        }
    };
}

/// Interior mutability capability escape through `RefCell::borrow_mut` should be rejected.
///
/// Expected validation error:
/// ```text
/// error: cannot write to non-ghost variable in ghost block
/// ```
#[allow(dead_code)]
pub fn interior_mutability_refcell_borrow_mut(ref_cell: RefCell<i32>) {
    let _ = ghost! {
        {
            let mut borrowed = ref_cell.borrow_mut(); // ERROR: mutable borrow capability escape
            *borrowed = 1;
        }
    };
}

fn main() {}
