// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost erasure check: cases that should PASS.
//!
//! These functions use ghost blocks correctly and should not trigger any
//! erasure check violations.

#[allow(unused_imports)]
use trust_wp_std::ghost::Ghost;
use trust_wp_std::{ghost, ghost::perm::Perm, std::cell::PermCell};

/// Ghost block result assigned to local variable, not returned.
///
/// The ghost value is bound but not returned. The function's return type
/// is `()`, so no ghost values leak into the runtime signature.
#[allow(dead_code)]
pub fn ghost_value_not_returned() {
    let _g = ghost! { 42 };
}

/// Ghost block result discarded immediately.
///
/// The ghost block is evaluated for its specification effect only.
#[allow(dead_code, unused_must_use)]
pub fn ghost_block_discarded() {
    ghost! { true };
}

/// Multiple ghost blocks in one function, none leaking.
#[allow(dead_code)]
pub fn multiple_ghost_blocks() {
    let _a = ghost! { 1 };
    let _b = ghost! { 2 };
}

/// Ghost value used inside ghost block for specification, not returned.
#[allow(dead_code)]
pub fn ghost_computation_internal() {
    let _result = ghost! {
        {
            let x = 10;
            let y = 20;
            let _ = (x, y);
            30
        }
    };
}

#[allow(dead_code)]
pub fn permission_identity_local_pair() {
    let (cell, perm) = PermCell::new(1i32);
    let _ = unsafe { cell.borrow(ghost!(&*perm)) };
}

#[allow(dead_code)]
pub fn pointer_permission_identity_local_pair() {
    let (ptr, perm) = Perm::new(1i32);
    let _ = unsafe { Perm::as_ref(ptr, ghost!(&**perm)) };
}

#[allow(dead_code)]
pub struct CellHolder {
    data: PermCell<i32>,
}

impl CellHolder {
    #[allow(dead_code)]
    pub fn permission_identity_field_receiver(&self, perm: Ghost<&Perm<PermCell<i32>>>) {
        let _ = unsafe { self.data.borrow(perm) };
    }
}

fn main() {}
