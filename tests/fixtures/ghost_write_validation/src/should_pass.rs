// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost block write validation: cases that should PASS.
//!
//! All functions in this module should verify successfully.

use std::cell::RefCell;

use trust_wp_std::ghost;
#[allow(unused_imports)]
use trust_wp_std::ghost::Ghost;

/// Writing to a variable declared inside the ghost block is allowed.
#[allow(dead_code, unused_mut, unused_assignments)]
pub fn write_local_in_ghost() {
    let _ = ghost! {
        {
            let mut y = 0;
            y = 1; // OK: y is declared inside the ghost block
            let _ = y;
        }
    };
}

/// Compound assignment to a local variable is allowed.
#[allow(dead_code, unused_mut, unused_assignments)]
pub fn compound_assign_local() {
    let _ = ghost! {
        {
            let mut count = 0;
            count += 1; // OK: count is local to the ghost block
            count *= 2; // OK: compound ops on locals are fine
            let _ = count;
        }
    };
}

/// Writing to a Ghost<T> variable declared inside the ghost block is allowed.
#[allow(dead_code, unused_mut, unused_assignments)]
pub fn write_ghost_var_in_ghost() {
    let _ = ghost! {
        {
            let mut g = Ghost::new(0i32);
            g = Ghost::new(1); // OK: g is local Ghost<T> variable
            let _ = g;
        }
    };
}

/// Mutating a value bound inside the ghost block is allowed.
#[allow(dead_code)]
pub fn mutate_local_vec_in_ghost() {
    let _ = ghost! {
        {
            let mut local = Vec::new();
            local.push(1); // OK: local receiver is ghost-local
            let _ = local;
        }
    };
}

/// Interior mutability on ghost-local state is allowed.
#[allow(dead_code)]
pub fn mutate_local_refcell_in_ghost() {
    let _ = ghost! {
        {
            let local = RefCell::new(0i32);
            *local.borrow_mut() = 1; // OK: local receiver is ghost-local
        }
    };
}

/// Writing through a mutable-reference alias to a ghost-local binding is allowed.
#[allow(dead_code)]
pub fn mutable_ref_alias_local_ok() {
    let _ = ghost! {
        {
            let mut local = 0i32;
            let alias = &mut local;
            *alias = 1; // OK: alias ultimately points to ghost-local state
        }
    };
}

/// Chaining mutable-reference aliases to ghost-local state is allowed.
#[allow(dead_code)]
pub fn mutable_ref_alias_chain_local_ok() {
    let _ = ghost! {
        {
            let mut local = 0i32;
            let alias1 = &mut local;
            let alias2 = alias1;
            *alias2 = 2; // OK: alias chain still targets ghost-local state
        }
    };
}

fn main() {}
