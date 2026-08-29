// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;

use super::rustc_callback_harness::run_test_compiler;
use crate::callbacks::struct_field_map::build_struct_field_map;

struct StructFieldMapCallbacks {
    fn_name: String,
    field_map: Option<HashMap<String, usize>>,
    ran: bool,
}

impl Callbacks for StructFieldMapCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            let def_path = tcx.def_path_str(def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            self.field_map = Some(build_struct_field_map(tcx, def_id));
            self.ran = true;
            break;
        }

        Compilation::Stop
    }
}

fn collect_struct_field_map(source: &str, fn_name: &str) -> HashMap<String, usize> {
    let mut callbacks = StructFieldMapCallbacks {
        fn_name: fn_name.to_string(),
        field_map: None,
        ran: false,
    };
    run_test_compiler(source, "trust_wp_struct_field_map", &mut callbacks);

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );
    callbacks
        .field_map
        .expect("field map should be collected for requested function")
}

#[test]
fn build_struct_field_map_includes_return_type_fields() {
    let source = r#"
pub struct Ret {
    pub value: i32,
    pub other: i32,
}

pub fn make_ret() -> Ret {
    Ret { value: 1, other: 2 }
}
"#;

    let field_map = collect_struct_field_map(source, "make_ret");
    assert_eq!(field_map.get("value"), Some(&0));
    assert_eq!(field_map.get("other"), Some(&1));
}

#[test]
fn build_struct_field_map_collects_nested_struct_fields() {
    let source = r#"
pub struct Inner {
    pub value: i32,
}

pub struct Outer {
    pub inner: Inner,
}

pub fn read_inner(input: Outer) -> i32 {
    input.inner.value
}
"#;

    let field_map = collect_struct_field_map(source, "read_inner");
    assert_eq!(field_map.get("inner"), Some(&0));
    assert_eq!(field_map.get("value"), Some(&0));
}

#[test]
fn build_struct_field_map_drops_ambiguous_field_names() {
    let source = r#"
pub struct Left {
    pub x: i32,
}

pub struct Right {
    pub y: i32,
    pub x: i32,
}

pub fn combine(left: Left, right: Right) -> i32 {
    left.x + right.x + right.y
}
"#;

    let field_map = collect_struct_field_map(source, "combine");
    assert!(!field_map.contains_key("x"));
    assert_eq!(field_map.get("y"), Some(&0));
}

#[test]
fn build_struct_field_map_ignores_nonlocal_nested_struct_fields() {
    let source = r#"
pub struct Wrapper {
    pub len: i32,
    pub data: Vec<i32>,
}

pub fn wrapper_len(w: Wrapper) -> i32 {
    w.len
}
"#;

    let field_map = collect_struct_field_map(source, "wrapper_len");
    assert_eq!(field_map.get("len"), Some(&0));
    assert_eq!(field_map.get("data"), Some(&1));
}

/// Nested struct with multiple fields: verify distinct indices propagate correctly.
/// Without this test, the existing nested-struct test passes trivially because
/// both fields map to index 0 (each is the first field in its struct).
#[test]
fn build_struct_field_map_nested_struct_distinct_indices() {
    let source = r#"
pub struct Inner {
    pub first: i32,
    pub second: i32,
    pub third: i32,
}

pub struct Outer {
    pub inner: Inner,
    pub extra: i32,
}

pub fn read_parts(input: Outer) -> i32 {
    input.inner.first + input.inner.second + input.inner.third + input.extra
}
"#;

    let field_map = collect_struct_field_map(source, "read_parts");
    assert_eq!(
        field_map.get("inner"),
        Some(&0),
        "Outer.inner should be at index 0"
    );
    assert_eq!(
        field_map.get("extra"),
        Some(&1),
        "Outer.extra should be at index 1"
    );
    assert_eq!(
        field_map.get("first"),
        Some(&0),
        "Inner.first should be at index 0"
    );
    assert_eq!(
        field_map.get("second"),
        Some(&1),
        "Inner.second should be at index 1"
    );
    assert_eq!(
        field_map.get("third"),
        Some(&2),
        "Inner.third should be at index 2"
    );
}

/// Same field name at the same index in two different structs should be preserved
/// (not dropped as ambiguous). This tests the `Some(_) => {}` branch of
/// `record_struct_field_index` at verification.rs:370.
#[test]
fn build_struct_field_map_same_name_same_index_preserved() {
    let source = r#"
pub struct Alpha {
    pub id: i32,
    pub name: i32,
}

pub struct Beta {
    pub id: i32,
    pub label: i32,
}

pub fn combine(a: Alpha, b: Beta) -> i32 {
    a.id + b.id + a.name + b.label
}
"#;

    let field_map = collect_struct_field_map(source, "combine");
    // "id" appears at index 0 in both Alpha and Beta — should be preserved
    assert_eq!(
        field_map.get("id"),
        Some(&0),
        "same-name same-index fields should be preserved, not dropped as ambiguous"
    );
    assert_eq!(field_map.get("name"), Some(&1));
    assert_eq!(field_map.get("label"), Some(&1));
}
