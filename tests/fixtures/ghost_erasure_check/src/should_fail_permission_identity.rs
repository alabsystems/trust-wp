// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Permission identity checks that should FAIL.
//!
//! This fixture covers provable same-scope mismatches where both resources were
//! constructed locally.

#![allow(dead_code, unexpected_cfgs, unused_variables)]

use trust_wp_std::{ghost, ghost::perm::Perm, std::cell::PermCell};

pub fn unknown_permcell_permission(
    cell: &PermCell<i32>,
    perm: trust_wp_std::ghost::Ghost<&Perm<PermCell<i32>>>,
) {
    let _ = unsafe { cell.borrow(perm) };
}

pub fn wrong_permcell_permission() {
    let (cell, _) = PermCell::new(1i32);
    let (_, wrong_owner) = PermCell::new(2i32);

    let _ = unsafe { cell.borrow(ghost!(&*wrong_owner)) };
}

pub fn local_permcell_unknown_permission(
    unknown_permission: trust_wp_std::ghost::Ghost<&Perm<PermCell<i32>>>,
) {
    let (local_cell, _) = PermCell::new(1i32);

    let _ = unsafe { local_cell.borrow(unknown_permission) };
}

pub fn wrong_permcell_permission_alias_borrow_mut() {
    let (cell, _) = PermCell::new(1i32);
    let (_, mut wrong_owner) = PermCell::new(2i32);
    let wrong_permission = ghost!(&mut *wrong_owner);

    let _ = unsafe { cell.borrow_mut(wrong_permission) };
}

pub fn wrong_permcell_permission_take() {
    let (cell, _) = PermCell::new(1i32);
    let (_, mut wrong_owner) = PermCell::new(2i32);

    let _ = unsafe { cell.take(ghost!(&mut **wrong_owner)) };
}

fn make_permcell_pair(
    value: i32,
) -> (
    PermCell<i32>,
    trust_wp_std::ghost::Ghost<Box<Perm<PermCell<i32>>>>,
) {
    PermCell::new(value)
}

pub fn helper_returned_pair_permission_mismatch() {
    let (cell, _) = make_permcell_pair(1i32);
    let (_, wrong_owner) = PermCell::new(2i32);
    let helper_wrong = ghost!(&*wrong_owner);

    let _ = unsafe { cell.borrow(helper_wrong) };
}

pub fn tuple_alias_permission_mismatch() {
    let (cell, _) = PermCell::new(1i32);
    let (_, wrong_owner) = PermCell::new(2i32);
    let (tuple_wrong,) = (ghost!(&*wrong_owner),);

    let _ = unsafe { cell.borrow(tuple_wrong) };
}

pub fn unknown_ptr_perm_permission(
    ptr: *const i32,
    perm: trust_wp_std::ghost::Ghost<&Perm<*const i32>>,
) {
    let _ = unsafe { Perm::as_ref(ptr, perm) };
}

pub fn wrong_ptr_perm_permission() {
    let (ptr, _) = Perm::new(1i32);
    let (_, wrong_owner) = Perm::new(2i32);

    let _ = unsafe { Perm::as_ref(ptr, ghost!(&**wrong_owner)) };
}

pub fn wrong_ptr_perm_permission_alias_as_mut() {
    let (ptr, _) = Perm::new(1i32);
    let (_, mut wrong_owner) = Perm::new(2i32);
    let wrong_permission = ghost!(&mut **wrong_owner);

    let _ = unsafe { Perm::as_mut(ptr as *mut i32, wrong_permission) };
}

fn main() {}
