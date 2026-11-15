// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A write through a MOVED `&mut` borrow must reach the borrowed place — and
//! must not be attributed to a place the borrow may no longer govern.

use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::mir::{Rvalue, StatementKind};

use super::*;

static MOVED_BORROW_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Substitutions at the first closure aggregate in `fn_name` (the marker
/// `let _m = || marker;` placed where a `proof_assert!` would be).
struct SubstitutionsAtMarker {
    fn_name: String,
    substitutions: Option<NameSubstitutions>,
    ran: bool,
}

impl Callbacks for SubstitutionsAtMarker {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }
            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let arg_names = resolve_arg_names_or_warn(tcx, local_def_id.to_def_id(), None);
            let location =
                body.basic_blocks
                    .iter_enumerated()
                    .find_map(|(bb_idx, bb_data)| {
                        bb_data.statements.iter().enumerate().find_map(
                            |(stmt_idx, stmt)| match stmt.kind {
                                StatementKind::Assign((
                                    _,
                                    Rvalue::Aggregate(
                                        rustc_middle::mir::AggregateKind::Closure(_, _),
                                        _,
                                    ),
                                )) => Some(Location {
                                    block: bb_idx,
                                    statement_index: stmt_idx,
                                }),
                                _ => None,
                            },
                        )
                    })
                    .expect("closure marker should be present");
            self.substitutions = extract_name_substitutions_until_location(
                tcx,
                body,
                &arg_names,
                &HashMap::new(),
                &HashMap::new(),
                &HashMap::new(),
                location,
            );
            self.ran = true;
            return Compilation::Stop;
        }
        Compilation::Stop
    }
}

/// Obligations of the primary (return-expression) lane for `fn_name`.
struct ObligationsOfBody {
    fn_name: String,
    obligations: Option<Vec<PureExpr>>,
    ran: bool,
}

impl Callbacks for ObligationsOfBody {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }
            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let arg_names = resolve_arg_names_or_warn(tcx, local_def_id.to_def_id(), None);
            let (_expr, effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &HashMap::new(),
                &HashMap::new(),
                &HashMap::new(),
            );
            self.obligations = Some(effects.obligations);
            self.ran = true;
            return Compilation::Stop;
        }
        Compilation::Stop
    }
}

fn compile_with<C: Callbacks + Send>(source: &str, callbacks: &mut C) {
    let unique = MOVED_BORROW_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_moved_borrow_{}_{}",
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
        "trust_wp_moved_borrow_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    run_compiler(&args, callbacks);
    let _ = fs::remove_dir_all(&temp_dir);
}

fn substitutions_at_marker(source: &str, fn_name: &str) -> NameSubstitutions {
    let mut callbacks = SubstitutionsAtMarker {
        fn_name: fn_name.to_string(),
        substitutions: None,
        ran: false,
    };
    compile_with(source, &mut callbacks);
    assert!(
        callbacks.ran,
        "failed to extract substitutions for `{fn_name}`"
    );
    callbacks.substitutions.unwrap_or_default()
}

fn obligations_of(source: &str, fn_name: &str) -> Vec<PureExpr> {
    let mut callbacks = ObligationsOfBody {
        fn_name: fn_name.to_string(),
        obligations: None,
        ran: false,
    };
    compile_with(source, &mut callbacks);
    assert!(
        callbacks.ran,
        "failed to extract obligations for `{fn_name}`"
    );
    callbacks.obligations.unwrap_or_default()
}

fn binds_to_seven(substitutions: &NameSubstitutions, name: &str) -> bool {
    matches!(substitutions.get(name), Some(PureExpr::Int(7)))
}

/// A write through a moved borrow reaches the borrowed local: `x` is 7 at the
/// marker, exactly as it is when the write goes through the original borrow.
#[test]
fn write_through_moved_borrow_reaches_the_borrowed_local() {
    let source = r#"
pub fn moved() {
    let marker = 0u8;
    let mut x = 5i32;
    let r = &mut x;
    let r2 = r;
    *r2 = 7;
    let _m = || marker;
}
pub fn moved_twice() {
    let marker = 0u8;
    let mut x = 5i32;
    let r = &mut x;
    let r2 = r;
    let r3 = r2;
    *r3 = 7;
    let _m = || marker;
}
pub fn direct() {
    let marker = 0u8;
    let mut x = 5i32;
    let r = &mut x;
    *r = 7;
    let _m = || marker;
}
"#;
    for fn_name in ["direct", "moved", "moved_twice"] {
        let substitutions = substitutions_at_marker(source, fn_name);
        assert!(
            binds_to_seven(&substitutions, "x"),
            "{fn_name}: the write through the borrow must rebind `x` to the written value, got {substitutions:?}"
        );
    }
}

/// A borrow local the body assigns more than once may govern a different
/// place on each path: no chain edge is recorded for it, so the write is not
/// attributed to the place it was first created on.
#[test]
fn reassigned_moved_borrow_gets_no_chain_edge() {
    let source = r#"
pub fn redirected(c: bool) {
    let marker = 0u8;
    let mut x = 5i32;
    let mut y = 5i32;
    let r = &mut x;
    let mut r2 = r;
    if c {
        r2 = &mut y;
    }
    *r2 = 7;
    let _m = || marker;
}
"#;
    let substitutions = substitutions_at_marker(source, "redirected");
    assert!(
        !binds_to_seven(&substitutions, "x"),
        "a reassigned borrow local must not attribute its write to the first place it \
         borrowed: {substitutions:?}"
    );
}

/// A moved-from borrow whose own address is taken can be redirected through
/// that pointer before the move; the chain edge must refuse it.
#[test]
fn escaped_moved_borrow_gets_no_chain_edge() {
    let source = r#"
pub fn escaped() {
    let marker = 0u8;
    let mut x = 5i32;
    let mut y = 5i32;
    let mut r: &mut i32 = &mut x;
    let rr: &mut &mut i32 = &mut r;
    *rr = &mut y;
    let r2 = r;
    *r2 = 7;
    let _m = || marker;
}
"#;
    let substitutions = substitutions_at_marker(source, "escaped");
    assert!(
        !binds_to_seven(&substitutions, "x"),
        "a borrow whose address escapes may point elsewhere; its write must not reach \
         the place it was created on: {substitutions:?}"
    );
}

fn has_false_obligation(obligations: &[PureExpr]) -> bool {
    obligations
        .iter()
        .any(|o| matches!(o, PureExpr::Bool(false)))
}

/// The return lane reads a stored-through pointee (or the borrowed local
/// itself) as its entry value; such a return must fail closed.
#[test]
fn returning_a_stored_through_value_fails_closed() {
    let source = r#"
pub fn root_read() -> i32 {
    let mut x = 5i32;
    let r = &mut x;
    *r = 7;
    x
}
pub fn deref_read() -> i32 {
    let mut x = 5i32;
    let r = &mut x;
    *r = 7;
    *r
}
pub fn moved_root_read() -> i32 {
    let mut x = 5i32;
    let r = &mut x;
    let r2 = r;
    *r2 = 7;
    x
}
"#;
    for fn_name in ["root_read", "deref_read", "moved_root_read"] {
        let obligations = obligations_of(source, fn_name);
        assert!(
            has_false_obligation(&obligations),
            "{fn_name}: a return value read after a store through a borrow of it must owe \
             `false`, got {obligations:?}"
        );
    }
}

/// The gate must not fire where nothing stale is read: a plain reassignment,
/// a store followed by a fresh literal, or a returned BORROW (the handback
/// lane owns that shape and its `^result == ^p` control must keep verifying).
#[test]
fn return_gate_leaves_clean_and_handback_returns_alone() {
    let source = r#"
pub fn plain() -> i32 {
    let mut x = 5i32;
    x = 7;
    x
}
pub fn literal_after_store() -> i32 {
    let mut x = 5i32;
    let r = &mut x;
    *r = 7;
    9
}
pub fn hand_back(p: &mut u32) -> &mut u32 {
    *p = 9;
    p
}
pub fn param_root(p: &mut i32) -> &mut i32 {
    *p = 7;
    &mut *p
}
"#;
    for fn_name in ["plain", "literal_after_store", "hand_back", "param_root"] {
        let obligations = obligations_of(source, fn_name);
        assert!(
            !has_false_obligation(&obligations),
            "{fn_name}: nothing stale is read into a reference-free return value, so no \
             `false` may be owed, got {obligations:?}"
        );
    }
}
