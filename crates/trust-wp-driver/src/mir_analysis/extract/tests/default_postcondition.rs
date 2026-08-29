// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::HashMap,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::{TyCtxt, TyKind};
use trust_wp_driver::StdSpec;

use super::*;

static COUNTER: AtomicU64 = AtomicU64::new(0);

#[derive(Default)]
struct TakeDefaultCallbacks {
    ensures_by_fn: HashMap<String, Vec<String>>,
}

impl Callbacks for TakeDefaultCallbacks {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            if tcx.def_kind(def_id) != DefKind::Fn {
                continue;
            }

            let path = tcx.def_path_str(def_id);
            let Some(name) = path.rsplit("::").next() else {
                continue;
            };
            if !matches!(
                name,
                "take_bool" | "take_option" | "take_slice" | "take_shared_slice"
            ) {
                continue;
            }

            let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
            let arg_ty = sig.inputs()[0];
            let TyKind::Ref(_, dest_ty, _) = arg_ty.kind() else {
                panic!("{name} first arg should be &mut T, got {arg_ty:?}");
            };

            let mut spec = generic_take_spec();
            specialize_take_default_postcondition_for_ty(tcx, &mut spec, "dest", *dest_ty);
            self.ensures_by_fn.insert(name.to_string(), spec.ensures);
        }

        Compilation::Stop
    }
}

fn generic_take_spec() -> StdSpec {
    StdSpec {
        requires: vec![],
        ensures: vec![
            "result == old(*dest)".to_string(),
            "(^dest) == Default::default()".to_string(),
        ],
        param_names: Some(vec!["dest".to_string()]),
    }
}

fn collect_specialized_take_ensures() -> HashMap<String, Vec<String>> {
    let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_take_default_specialization_{}_{}",
        std::process::id(),
        unique
    ));
    std::fs::create_dir_all(&temp_dir).expect("create temp dir");

    let source_path = temp_dir.join("test.rs");
    std::fs::write(
        &source_path,
        "pub fn take_bool(dest: &mut bool) -> bool { std::mem::take(dest) }\n\
         pub fn take_option(dest: &mut Option<i32>) -> Option<i32> { std::mem::take(dest) }\n\
         pub fn take_slice<'a>(dest: &mut &'a mut [i32]) -> &'a mut [i32] { std::mem::take(dest) }\n\
         pub fn take_shared_slice<'a>(dest: &mut &'a [i32]) -> &'a [i32] { std::mem::take(dest) }\n",
    )
    .expect("write temp source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_take_default_spec_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = TakeDefaultCallbacks::default();
    run_compiler(&args, &mut callbacks);

    let _ = std::fs::remove_file(&source_path);
    let _ = std::fs::remove_dir_all(&temp_dir);

    callbacks.ensures_by_fn
}

#[test]
fn take_default_bool_specializes_to_false() {
    let ensures = collect_specialized_take_ensures();
    let take_bool = ensures
        .get("take_bool")
        .expect("should collect specialized spec for take_bool");

    assert!(
        take_bool.iter().any(|clause| clause == "(^dest) == false"),
        "bool mem::take should specialize Default::default() to false, got {take_bool:?}"
    );
    assert!(
        !take_bool
            .iter()
            .any(|clause| clause.contains("Default::default()")),
        "bool mem::take should not leave the generic default placeholder: {take_bool:?}"
    );
}

#[test]
fn take_default_option_specializes_to_none_constructor() {
    let ensures = collect_specialized_take_ensures();
    let take_option = ensures
        .get("take_option")
        .expect("should collect specialized spec for take_option");

    assert!(
        take_option
            .iter()
            .any(|clause| clause == "(^dest) == None()"),
        "Option mem::take should specialize Default::default() to None(), got {take_option:?}"
    );
}

#[test]
fn take_default_mut_slice_reference_specializes_to_empty_seq_view() {
    let ensures = collect_specialized_take_ensures();
    let take_slice = ensures
        .get("take_slice")
        .expect("should collect specialized spec for take_slice");

    assert!(
        take_slice
            .iter()
            .any(|clause| clause == "(^dest)@ == Seq::empty()"),
        "&mut [T] mem::take should specialize Default::default() to an empty sequence view, got {take_slice:?}"
    );
}

/// Creusot-parity F2: for `&mut [T]` destinations, `Default for &'a mut [T]`
/// has a second ensures conjunct `(^result)@ == Seq::empty()`
/// (creusot-std/src/std/slice.rs:432). With `result := ^dest` this is the
/// final view of the inner borrow, `(^(^dest))@ == Seq::empty()`, emitted as
/// a separate clause. The pre-existing clauses must be byte-identical.
#[test]
fn take_default_mut_slice_reference_emits_final_view_conjunct() {
    let ensures = collect_specialized_take_ensures();
    let take_slice = ensures
        .get("take_slice")
        .expect("should collect specialized spec for take_slice");

    assert!(
        take_slice
            .iter()
            .any(|clause| clause == "(^(^dest))@ == Seq::empty()"),
        "&mut [T] mem::take should also pin the FINAL view of the inner borrow \
         (Creusot's `(^result)@ == Seq::empty()` Default conjunct), got {take_slice:?}"
    );
    // Existing conjuncts unchanged and no duplicates: exactly the original
    // two clauses plus the one appended final-view clause.
    assert_eq!(
        take_slice.as_slice(),
        [
            "result == old(*dest)".to_string(),
            "(^dest)@ == Seq::empty()".to_string(),
            "(^(^dest))@ == Seq::empty()".to_string(),
        ],
        "&mut [T] mem::take ensures should be exactly the two original clauses \
         plus the appended final-view conjunct"
    );
}

/// Shared `&[T]` destinations must NOT get the final-view conjunct: Creusot's
/// `Default for &'a [T]` (creusot-std/src/std/slice.rs:436-440) has only the
/// single current-view conjunct, and a shared reference has no prophecy.
#[test]
fn take_default_shared_slice_reference_gets_no_final_view_conjunct() {
    let ensures = collect_specialized_take_ensures();
    let take_shared = ensures
        .get("take_shared_slice")
        .expect("should collect specialized spec for take_shared_slice");

    assert!(
        take_shared
            .iter()
            .any(|clause| clause == "(^dest)@ == Seq::empty()"),
        "&[T] mem::take should specialize Default::default() to an empty sequence view, got {take_shared:?}"
    );
    assert!(
        !take_shared
            .iter()
            .any(|clause| clause.contains("(^(^dest))")),
        "shared &[T] mem::take must NOT get a final-view conjunct (no prophecy \
         on shared refs), got {take_shared:?}"
    );
    assert_eq!(
        take_shared.len(),
        2,
        "shared &[T] mem::take should keep exactly the two original clauses, got {take_shared:?}"
    );
}

/// Non-borrow destinations (e.g. `bool`) must not grow an extra clause.
#[test]
fn take_default_bool_gets_no_final_view_conjunct() {
    let ensures = collect_specialized_take_ensures();
    let take_bool = ensures
        .get("take_bool")
        .expect("should collect specialized spec for take_bool");

    assert!(
        !take_bool.iter().any(|clause| clause.contains("(^(^dest))")),
        "bool mem::take must not get a final-view conjunct, got {take_bool:?}"
    );
    assert_eq!(
        take_bool.len(),
        2,
        "bool mem::take should keep exactly the two original clauses, got {take_bool:?}"
    );
}

// ── Generalized specialization tests (#2256) ────────────────────────

/// Test that `specialize_take_default_postcondition_for_ty` works for i32
/// (the most common primitive Default case).
#[test]
fn specialize_default_i32_gives_zero() {
    #[derive(Default)]
    struct I32DefaultCallbacks {
        result: Option<Vec<String>>,
    }

    impl Callbacks for I32DefaultCallbacks {
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for local_def_id in tcx.hir_body_owners() {
                let def_id = local_def_id.to_def_id();
                if tcx.def_kind(def_id) != DefKind::Fn {
                    continue;
                }
                let path = tcx.def_path_str(def_id);
                if !path.ends_with("custom_take_i32") {
                    continue;
                }
                let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                let arg_ty = sig.inputs()[0];
                let TyKind::Ref(_, dest_ty, _) = arg_ty.kind() else {
                    panic!("first arg should be &mut i32, got {arg_ty:?}");
                };

                // Use a non-mem::take spec with Default::default() placeholder
                let mut spec = StdSpec {
                    requires: vec![],
                    ensures: vec![
                        "result == old(*x)".to_string(),
                        "(^x) == Default::default()".to_string(),
                    ],
                    param_names: Some(vec!["x".to_string()]),
                };
                specialize_take_default_postcondition_for_ty(tcx, &mut spec, "x", *dest_ty);
                self.result = Some(spec.ensures);
            }
            Compilation::Stop
        }
    }

    let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_default_i32_{}_{}",
        std::process::id(),
        unique
    ));
    std::fs::create_dir_all(&temp_dir).expect("create temp dir");
    let source_path = temp_dir.join("test.rs");
    std::fs::write(
        &source_path,
        "pub fn custom_take_i32(x: &mut i32) -> i32 { std::mem::take(x) }\n",
    )
    .expect("write temp source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_default_i32_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = I32DefaultCallbacks::default();
    run_compiler(&args, &mut callbacks);
    let _ = std::fs::remove_dir_all(&temp_dir);

    let ensures = callbacks
        .result
        .expect("should collect ensures for custom_take_i32");
    assert!(
        ensures.iter().any(|clause| clause == "(^x) == 0"),
        "i32 default should specialize to (^x) == 0, got {ensures:?}"
    );
    assert!(
        !ensures
            .iter()
            .any(|clause| clause.contains("Default::default()")),
        "should not leave the generic default placeholder: {ensures:?}"
    );
}

/// Test that specialization works for u64 (unsigned integer).
#[test]
fn specialize_default_u64_gives_zero() {
    #[derive(Default)]
    struct U64DefaultCallbacks {
        result: Option<Vec<String>>,
    }

    impl Callbacks for U64DefaultCallbacks {
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for local_def_id in tcx.hir_body_owners() {
                let def_id = local_def_id.to_def_id();
                if tcx.def_kind(def_id) != DefKind::Fn {
                    continue;
                }
                let path = tcx.def_path_str(def_id);
                if !path.ends_with("custom_take_u64") {
                    continue;
                }
                let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                let arg_ty = sig.inputs()[0];
                let TyKind::Ref(_, dest_ty, _) = arg_ty.kind() else {
                    panic!("first arg should be &mut u64, got {arg_ty:?}");
                };

                let mut spec = StdSpec {
                    requires: vec![],
                    ensures: vec!["(^dest) == Default::default()".to_string()],
                    param_names: Some(vec!["dest".to_string()]),
                };
                specialize_take_default_postcondition_for_ty(tcx, &mut spec, "dest", *dest_ty);
                self.result = Some(spec.ensures);
            }
            Compilation::Stop
        }
    }

    let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_default_u64_{}_{}",
        std::process::id(),
        unique
    ));
    std::fs::create_dir_all(&temp_dir).expect("create temp dir");
    let source_path = temp_dir.join("test.rs");
    std::fs::write(
        &source_path,
        "pub fn custom_take_u64(dest: &mut u64) -> u64 { std::mem::take(dest) }\n",
    )
    .expect("write temp source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_default_u64_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = U64DefaultCallbacks::default();
    run_compiler(&args, &mut callbacks);
    let _ = std::fs::remove_dir_all(&temp_dir);

    let ensures = callbacks
        .result
        .expect("should collect ensures for custom_take_u64");
    assert!(
        ensures.iter().any(|clause| clause == "(^dest) == 0"),
        "u64 default should specialize to (^dest) == 0, got {ensures:?}"
    );
}

/// Test that specialization works for String (Vec-like default).
#[test]
fn specialize_default_string_gives_empty_seq() {
    #[derive(Default)]
    struct StringDefaultCallbacks {
        result: Option<Vec<String>>,
    }

    impl Callbacks for StringDefaultCallbacks {
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for local_def_id in tcx.hir_body_owners() {
                let def_id = local_def_id.to_def_id();
                if tcx.def_kind(def_id) != DefKind::Fn {
                    continue;
                }
                let path = tcx.def_path_str(def_id);
                if !path.ends_with("custom_take_string") {
                    continue;
                }
                let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                let arg_ty = sig.inputs()[0];
                let TyKind::Ref(_, dest_ty, _) = arg_ty.kind() else {
                    panic!("first arg should be &mut String, got {arg_ty:?}");
                };

                let mut spec = StdSpec {
                    requires: vec![],
                    ensures: vec!["(^dest) == Default::default()".to_string()],
                    param_names: Some(vec!["dest".to_string()]),
                };
                specialize_take_default_postcondition_for_ty(tcx, &mut spec, "dest", *dest_ty);
                self.result = Some(spec.ensures);
            }
            Compilation::Stop
        }
    }

    let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_default_string_{}_{}",
        std::process::id(),
        unique
    ));
    std::fs::create_dir_all(&temp_dir).expect("create temp dir");
    let source_path = temp_dir.join("test.rs");
    std::fs::write(
        &source_path,
        "pub fn custom_take_string(dest: &mut String) -> String { std::mem::take(dest) }\n",
    )
    .expect("write temp source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_default_string_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = StringDefaultCallbacks::default();
    run_compiler(&args, &mut callbacks);
    let _ = std::fs::remove_dir_all(&temp_dir);

    let ensures = callbacks
        .result
        .expect("should collect ensures for custom_take_string");
    assert!(
        ensures
            .iter()
            .any(|clause| clause == "(^dest)@ == Seq::empty()"),
        "String default should specialize to (^dest)@ == Seq::empty(), got {ensures:?}"
    );
}
