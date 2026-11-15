// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `vec![c0, ..]` element-value synthesis and the `Vec<T>`-gated
//! `Vec::extend` concat contract (bug/874). Each case runs `resolve_call` on
//! both the borrowck-shaped MIR (`mir_promoted`, what the driver consumes) and
//! the elaborated `optimized_mir`, so both payload-write shapes are pinned.

use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;

use super::*;
use crate::mir_analysis::extract::call_resolve_shared::{resolve_call, ResolvedCallKind};

static COUNTER: AtomicU64 = AtomicU64::new(0);

/// Resolve every call whose def path ends with `callee_suffix` inside
/// `fn_name`, returning the ensures of each ExternSpec resolution (or `None`
/// for non-ExternSpec kinds) for (promoted MIR, optimized MIR).
struct ResolveCallbacks {
    fn_name: String,
    callee_suffix: String,
    promoted: Vec<Option<Vec<String>>>,
    optimized: Vec<Option<Vec<String>>>,
}

fn resolve_matching<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    callee_suffix: &str,
) -> Vec<Option<Vec<String>>> {
    let mut out = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &data.terminator().kind
        else {
            continue;
        };
        let Operand::Constant(deref!(constant)) = func else {
            continue;
        };
        let rustc_middle::ty::TyKind::FnDef(def_id, _) = constant.ty().kind() else {
            continue;
        };
        if !tcx.def_path_str(*def_id).ends_with(callee_suffix) {
            continue;
        }
        let resolved = resolve_call(
            tcx,
            body,
            bb,
            func,
            args,
            destination.local,
            &HashMap::new(),
            &HashMap::new(),
            &HashMap::new(),
            None,
            &HashMap::<Local, PureExpr>::new(),
        );
        out.push(match resolved.kind {
            ResolvedCallKind::ExternSpec(spec) => Some(spec.ensures),
            _ => None,
        });
    }
    out
}

impl Callbacks for ResolveCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }
            // Borrowck-shaped MIR: read before borrowck steals it.
            let promoted = tcx.mir_promoted(local_def_id).0.borrow().clone();
            self.promoted = resolve_matching(tcx, &promoted, &self.callee_suffix);
            let optimized = tcx.optimized_mir(local_def_id.to_def_id());
            self.optimized = resolve_matching(tcx, optimized, &self.callee_suffix);
            return Compilation::Stop;
        }
        Compilation::Stop
    }
}

type Resolutions = (Vec<Option<Vec<String>>>, Vec<Option<Vec<String>>>);

fn resolve_in_source(source: &str, fn_name: &str, callee_suffix: &str) -> Resolutions {
    let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_vec_extend_literal_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");
    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");
    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_vec_extend_literal_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = ResolveCallbacks {
        fn_name: fn_name.to_string(),
        callee_suffix: callee_suffix.to_string(),
        promoted: Vec::new(),
        optimized: Vec::new(),
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);
    (callbacks.promoted, callbacks.optimized)
}

fn both_shapes(res: &Resolutions) -> Vec<&Option<Vec<String>>> {
    assert!(!res.0.is_empty(), "no matching call in promoted MIR");
    assert_eq!(
        res.0.len(),
        res.1.len(),
        "promoted/optimized call counts differ: {res:?}"
    );
    res.0.iter().chain(res.1.iter()).collect()
}

#[test]
fn vec_literal_of_constants_carries_element_values() {
    let res = resolve_in_source(
        "pub fn f() -> Vec<i32> { vec![1, -2, 3] }",
        "f",
        "box_assume_init_into_vec_unsafe",
    );
    for ensures in both_shapes(&res) {
        let ensures = ensures.as_ref().expect("vec literal resolves to a spec");
        assert_eq!(
            ensures,
            &vec![
                "result@.len() == 3".to_string(),
                "result@.index_logic(0) == 1".to_string(),
                "result@.index_logic(1) == -2".to_string(),
                "result@.index_logic(2) == 3".to_string(),
            ]
        );
    }
}

#[test]
fn vec_literal_with_non_constant_operand_keeps_length_only() {
    let res = resolve_in_source(
        "pub fn f(x: i32) -> Vec<i32> { vec![x, 2] }",
        "f",
        "box_assume_init_into_vec_unsafe",
    );
    for ensures in both_shapes(&res) {
        assert_eq!(
            ensures.as_ref().expect("vec literal resolves to a spec"),
            &vec!["result@.len() == 2".to_string()],
            "a non-constant element must not produce ANY element fact"
        );
    }
}

#[test]
fn two_vec_literals_each_get_their_own_values() {
    let res = resolve_in_source(
        "pub fn f() -> (Vec<i32>, Vec<i32>) { (vec![1, 2], vec![7, 8]) }",
        "f",
        "box_assume_init_into_vec_unsafe",
    );
    let shapes = both_shapes(&res);
    let all: Vec<_> = shapes.iter().map(|e| (*e).clone().expect("spec")).collect();
    let half = all.len() / 2;
    for pair in [&all[..half], &all[half..]] {
        assert_eq!(pair.len(), 2);
        let joined: Vec<String> = pair.iter().flatten().cloned().collect();
        assert!(joined.contains(&"result@.index_logic(0) == 1".to_string()));
        assert!(joined.contains(&"result@.index_logic(0) == 7".to_string()));
        // No literal may receive the other literal's values.
        for spec in pair {
            let has_first = spec.iter().any(|e| e.ends_with("== 1"));
            let has_second = spec.iter().any(|e| e.ends_with("== 7"));
            assert!(has_first ^ has_second, "values crossed literals: {spec:?}");
        }
    }
}

#[test]
fn vec_extend_with_vec_argument_gets_concat_contract() {
    let res = resolve_in_source(
        "pub fn f(mut v: Vec<i32>, w: Vec<i32>) -> Vec<i32> { v.extend(w); v }",
        "f",
        "::extend",
    );
    for ensures in both_shapes(&res) {
        let ensures = ensures.as_ref().expect("extend resolves to a spec");
        assert!(
            ensures.contains(&"(^self)@ == self@.concat(iter@)".to_string()),
            "{ensures:?}"
        );
    }
}

fn assert_no_concat(res: &Resolutions) {
    for ensures in both_shapes(res) {
        if let Some(ensures) = ensures {
            assert!(
                !ensures.iter().any(|e| e.contains("concat")),
                "concat contract must be gated to Vec<T> arguments, got {ensures:?}"
            );
        }
    }
}

#[test]
fn vec_extend_with_array_argument_does_not_get_concat_contract() {
    assert_no_concat(&resolve_in_source(
        "pub fn f(mut v: Vec<i32>) -> Vec<i32> { v.extend([1, 2]); v }",
        "f",
        "::extend",
    ));
}

#[test]
fn vec_extend_with_iterator_argument_does_not_get_concat_contract() {
    // A filtering iterator produces a SUBSET of its source's view: a
    // concat over `iter@` would be unsound here.
    assert_no_concat(&resolve_in_source(
        "pub fn f(mut v: Vec<i32>, w: Vec<i32>) -> Vec<i32> { \
             v.extend(w.into_iter().filter(|x| *x > 0)); v }",
        "f",
        "::extend",
    ));
}

#[test]
fn vec_extend_with_ref_element_vec_does_not_get_concat_contract() {
    // `Extend<&T>` with a `Vec<&T>` argument: element types differ.
    assert_no_concat(&resolve_in_source(
        "pub fn f(mut v: Vec<i32>, w: Vec<&i32>) -> Vec<i32> { v.extend(w); v }",
        "f",
        "::extend",
    ));
}

#[test]
fn user_extend_trait_on_vec_does_not_get_concat_contract() {
    assert_no_concat(&resolve_in_source(
        "pub trait Extend<A> { fn extend(&mut self, other: A); }
         impl Extend<Vec<i32>> for Vec<i32> { fn extend(&mut self, _other: Vec<i32>) {} }
         pub fn f(mut v: Vec<i32>, w: Vec<i32>) -> Vec<i32> { Extend::extend(&mut v, w); v }",
        "f",
        "::extend",
    ));
}
