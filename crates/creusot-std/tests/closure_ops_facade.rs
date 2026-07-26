// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-surface test for stable FnOnceExt/FnMutExt/FnExt facade traits.
//!
//! Part of #2443: verifies that the closure-ops extension traits are
//! importable through `creusot_std::std::ops` and that blanket impls
//! satisfy trait bounds for closures and function pointers over arities 0..=3.

use creusot_std::std::ops::{FnExt, FnMutExt, FnOnceExt};

fn require_fn_once_ext<F: FnOnceExt<Args>, Args>(_f: F) {}
fn require_fn_mut_ext<F: FnMutExt<Args>, Args>(_f: F) {}
fn require_fn_ext<F: FnExt<Args>, Args>(_f: F) {}

fn require_fn_once_ext_with_output<F: FnOnceExt<Args, Output = O>, Args, O>(_f: F) {}

#[test]
fn stable_closure_ops_zero_arg() {
    let f: fn() -> bool = || true;
    require_fn_once_ext::<_, ()>(f);
    require_fn_mut_ext::<_, ()>(f);
    require_fn_ext::<_, ()>(f);
    require_fn_once_ext_with_output::<_, (), bool>(f);
}

#[test]
fn stable_closure_ops_one_arg() {
    let f: fn(u32) -> bool = |_x| true;
    require_fn_once_ext::<_, (u32,)>(f);
    require_fn_mut_ext::<_, (u32,)>(f);
    require_fn_ext::<_, (u32,)>(f);
    require_fn_once_ext_with_output::<_, (u32,), bool>(f);
}

#[test]
fn stable_closure_ops_two_arg() {
    let f: fn(u32, i64) -> bool = |_x, _y| true;
    require_fn_once_ext::<_, (u32, i64)>(f);
    require_fn_mut_ext::<_, (u32, i64)>(f);
    require_fn_ext::<_, (u32, i64)>(f);
}

#[test]
fn stable_closure_ops_three_arg() {
    let f: fn(u8, u16, u32) -> String = |_a, _b, _c| String::new();
    require_fn_once_ext::<_, (u8, u16, u32)>(f);
    require_fn_mut_ext::<_, (u8, u16, u32)>(f);
    require_fn_ext::<_, (u8, u16, u32)>(f);
    require_fn_once_ext_with_output::<_, (u8, u16, u32), String>(f);
}

#[test]
fn stable_closure_ops_with_closure_not_fn_pointer() {
    let captured = 42u32;
    let closure = |x: u32| -> bool { x > captured };
    require_fn_ext::<_, (u32,)>(&closure);
    require_fn_mut_ext::<_, (u32,)>(&closure);
}
