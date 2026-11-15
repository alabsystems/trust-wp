// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{super::*, helpers::*};

#[test]
fn test_lookup_mutex_new() {
    let spec = lookup_std_spec("std::sync::Mutex::new").unwrap();
    assert_requires_contains(&spec, "inv.inv(value)", "Mutex::new");
    assert_ensures_contains(&spec, "result.inv() == inv", "Mutex::new");
}

#[test]
fn test_lookup_mutex_lock() {
    let spec = lookup_std_spec("std::sync::Mutex::lock").unwrap();
    assert_requires_contains(
        &spec,
        "__trust_wp_std_site_unmodelled_panic()",
        "Mutex::lock",
    );
    assert_ensures_contains(&spec, "self.inv().inv(*result)", "Mutex::lock");
}

#[test]
fn test_lookup_mutex_into_inner() {
    let spec = lookup_std_spec("std::sync::Mutex::into_inner").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self.inv().inv(result)", "Mutex::into_inner");
}

#[test]
fn test_lookup_mutex_get_mut() {
    let spec = lookup_std_spec("std::sync::Mutex::get_mut").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "(*self).inv().inv(*result)", "Mutex::get_mut");
}

#[test]
fn test_lookup_mutex_guard_deref() {
    let spec = lookup_std_spec("std::sync::MutexGuard::deref").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self.inv().inv(*result)", "MutexGuard::deref");
}

#[test]
fn test_lookup_mutex_guard_set() {
    let spec = lookup_std_spec("std::sync::MutexGuard::set").unwrap();
    assert_requires_contains(&spec, "self.inv().inv(value)", "MutexGuard::set");
    assert_eq!(spec.ensures.len(), 1);
    assert_ensures_contains(&spec, "(^self).inv().inv(value)", "MutexGuard::set");
}

#[test]
fn test_lookup_arc_new() {
    let spec = lookup_std_spec("std::sync::Arc::new").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "*result == value", "Arc::new");
}

#[test]
fn test_lookup_arc_clone() {
    let spec = lookup_std_spec("alloc::sync::Arc::clone").unwrap();
    assert!(spec.requires.is_empty());
    // Inner-value equality: *result == *self
    assert_ensures_contains(&spec, "*result == *self", "Arc::clone");
}

#[test]
fn test_lookup_arc_clone_trait_qualified() {
    let spec = lookup_std_spec("<alloc::sync::Arc as core::clone::Clone>::clone").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "*result == *self", "Arc::clone trait");
}

#[test]
fn test_lookup_arc_as_ref() {
    let spec = lookup_std_spec("std::sync::Arc::as_ref").unwrap();
    assert!(spec.requires.is_empty());
    assert!(spec
        .ensures
        .iter()
        .any(|e| e.contains("result@") && e.contains("*self")));
}

#[test]
fn test_lookup_arc_try_unwrap() {
    let spec = lookup_std_spec("std::sync::Arc::try_unwrap").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Ok(v) => v == *self", "Arc::try_unwrap");
    assert_ensures_contains(&spec, "Err(arc) => *arc == *self", "Arc::try_unwrap");
}

#[test]
fn test_lookup_rc_new() {
    let spec = lookup_std_spec("std::rc::Rc::new").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "*result == value", "Rc::new");
}

#[test]
fn test_lookup_rc_clone() {
    let spec = lookup_std_spec("alloc::rc::Rc::clone").unwrap();
    assert!(spec.requires.is_empty());
    // Inner-value equality: *result == *self
    assert_ensures_contains(&spec, "*result == *self", "Rc::clone");
}

#[test]
fn test_lookup_rc_clone_trait_qualified() {
    let spec = lookup_std_spec("<alloc::rc::Rc as core::clone::Clone>::clone").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "*result == *self", "Rc::clone trait");
}

#[test]
fn test_lookup_rc_as_ref() {
    let spec = lookup_std_spec("std::rc::Rc::as_ref").unwrap();
    assert!(spec.requires.is_empty());
    assert!(spec
        .ensures
        .iter()
        .any(|e| e.contains("result@") && e.contains("*self")));
}

#[test]
fn test_lookup_arc_ptr_eq() {
    let spec =
        lookup_std_spec("std::sync::Arc::ptr_eq").expect("Arc::ptr_eq spec must be registered");
    assert!(spec.requires.is_empty());
    // One direction only: no allocation identity (D-190).
    assert_ensures_contains(&spec, "result ==> self == rhs", "Arc::ptr_eq");
}

#[test]
fn test_lookup_rc_ptr_eq() {
    let spec = lookup_std_spec("std::rc::Rc::ptr_eq").expect("Rc::ptr_eq spec must be registered");
    assert!(spec.requires.is_empty());
    // One direction only: no allocation identity (D-190).
    assert_ensures_contains(&spec, "result ==> self == rhs", "Rc::ptr_eq");
}

#[test]
fn test_lookup_cell_new() {
    let spec = lookup_std_spec("core::cell::Cell::new").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result.get() == value", "Cell::new");
}

#[test]
fn test_lookup_cell_get() {
    let spec = lookup_std_spec("std::cell::Cell::get").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "result == self.inner()", "Cell::get");
}

#[test]
fn test_lookup_cell_set() {
    let spec = lookup_std_spec("core::cell::Cell::set").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "(^self).inner() == value", "Cell::set");
}

#[test]
fn test_lookup_refcell_new() {
    let spec = lookup_std_spec("std::cell::RefCell::new").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "*result.borrow() == value", "RefCell::new");
}

#[test]
fn test_lookup_refcell_borrow() {
    let spec = lookup_std_spec("core::cell::RefCell::borrow").unwrap();
    assert_requires_contains(
        &spec,
        "__trust_wp_std_site_unmodelled_panic()",
        "RefCell::borrow",
    );
    assert_ensures_contains(&spec, "*result == self.inner()", "RefCell::borrow");
}

#[test]
fn test_lookup_refcell_borrow_mut() {
    let spec = lookup_std_spec("std::cell::RefCell::borrow_mut").unwrap();
    assert_requires_contains(
        &spec,
        "__trust_wp_std_site_unmodelled_panic()",
        "RefCell::borrow_mut",
    );
    assert_eq!(spec.ensures.len(), 2); // two postconditions
    assert_ensures_contains(&spec, "*result == self.inner()", "RefCell::borrow_mut");
    assert_ensures_contains(&spec, "(^self).inner() == ^result", "RefCell::borrow_mut");
}

#[test]
fn test_lookup_thread_spawn() {
    let spec = lookup_std_spec("std::thread::spawn").unwrap();
    assert_requires_contains(&spec, "f.precondition()", "thread::spawn");
    assert_ensures_contains(&spec, "result.postcond() == f.postcond()", "thread::spawn");
}

#[test]
fn test_lookup_join_handle_join() {
    let spec = lookup_std_spec("std::thread::JoinHandle::join").unwrap();
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "Ok(v) => self.postcond().inv(v)", "JoinHandle::join");
    assert_ensures_contains(&spec, "Err(_) => true", "JoinHandle::join");
}
