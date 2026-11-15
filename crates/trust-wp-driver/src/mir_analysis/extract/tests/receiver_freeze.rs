// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Value copies are frozen around mutating-receiver state propagation, while
//! the MIR-located mutated place (and borrow carriers, captured variables)
//! still advances. (#mutrecv-copies)

use std::{
    collections::{HashMap, HashSet},
    fs,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc,
    },
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::{
    mir::{Body, Local, Operand, TerminatorKind},
    ty::TyCtxt,
};

use super::*;

static RECEIVER_FREEZE_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

type Check = Box<dyn for<'a, 'tcx> Fn(TyCtxt<'tcx>, &'a Body<'tcx>, &'a [String]) + Send>;

struct FreezeCallbacks {
    check: Check,
    ran: bool,
}

impl Callbacks for FreezeCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != "caller" && !def_path.ends_with("::caller") {
                continue;
            }
            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let arg_names = resolve_arg_names_or_warn(tcx, local_def_id.to_def_id(), None);
            (self.check)(tcx, body, &arg_names);
            self.ran = true;
            return Compilation::Stop;
        }
        Compilation::Stop
    }
}

fn run_on_caller(source: &str, check: Check) {
    let unique = RECEIVER_FREEZE_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_receiver_freeze_{}_{}",
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
        "trust_wp_receiver_freeze_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "-Zmir-opt-level=0".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = FreezeCallbacks { check, ran: false };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);
    assert!(callbacks.ran, "caller body was not analysed");
}

fn named_local(body: &Body<'_>, arg_names: &[String], name: &str) -> Local {
    body.local_decls
        .indices()
        .filter(|local| source_name_for_local(body, *local, arg_names).as_deref() == Some(name))
        .max_by_key(|local| local.as_u32())
        .unwrap_or_else(|| panic!("source local `{name}` not found"))
}

/// First argument operand of the first call whose callee path contains `needle`.
fn first_arg_of_call<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    needle: &str,
) -> &'a Operand<'tcx> {
    body.basic_blocks
        .iter()
        .filter_map(|block| block.terminator.as_ref())
        .find_map(|terminator| match &terminator.kind {
            TerminatorKind::Call { func, args, .. } => {
                let (def_id, _) = func.const_fn_def()?;
                tcx.def_path_str(def_id)
                    .contains(needle)
                    .then(|| args.first().map(|arg| &arg.node))
                    .flatten()
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("no call to `{needle}`"))
}

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn final_of(expr: PureExpr) -> PureExpr {
    PureExpr::Final(Arc::new(expr))
}

#[test]
fn copy_source_and_copy_freeze_while_the_mutated_copy_advances() {
    // `resolve_ref_to_named_local` translates `&mut y` to `Var(x)` after
    // `let mut y = x`: the receiver EXPRESSION names x, the mutated PLACE is y.
    run_on_caller(
        r#"
pub fn inc(x: &mut i32) { *x += 1; }
pub fn caller() -> i32 {
    let x: i32 = 0;
    let mut y = x;
    let n = y;
    inc(&mut y);
    x + y + n
}
"#,
        Box::new(|tcx, body, arg_names| {
            let x = named_local(body, arg_names, "x");
            let y = named_local(body, arg_names, "y");
            let n = named_local(body, arg_names, "n");
            let operand = first_arg_of_call(tcx, body, "inc");
            let places = mutated_place_locals(body, operand).expect("place located");
            assert!(places.contains(&y), "y is the mutated place: {places:?}");
            assert!(!places.contains(&x) && !places.contains(&n), "{places:?}");

            let mut local_exprs = HashMap::from([(x, var("x")), (y, var("x")), (n, var("x"))]);
            propagate_mutating_receiver_state_with_captures(
                &mut local_exprs,
                body,
                arg_names,
                &var("x"),
                Some(operand),
                None,
            );
            assert_eq!(local_exprs[&y], final_of(var("x")), "mutated y advances");
            assert_eq!(local_exprs[&x], var("x"), "copy source x is frozen");
            assert_eq!(local_exprs[&n], var("x"), "copy n is frozen");
        }),
    );
}

#[test]
fn scalar_read_of_the_receiver_is_frozen_but_borrow_alias_and_place_advance() {
    run_on_caller(
        r#"
pub fn caller() -> usize {
    let mut v: Vec<i32> = Vec::new();
    let n = v.len();
    let r = &mut v;
    r.push(1);
    n
}
"#,
        Box::new(|tcx, body, arg_names| {
            let v = named_local(body, arg_names, "v");
            let n = named_local(body, arg_names, "n");
            let r = named_local(body, arg_names, "r");
            let operand = first_arg_of_call(tcx, body, "push");
            let places = mutated_place_locals(body, operand).expect("place located");
            assert!(
                places.contains(&v) && places.contains(&r),
                "reborrow through r reaches v: {places:?}"
            );

            let len_of_v = PureExpr::View(Arc::new(var("v")));
            let mut local_exprs =
                HashMap::from([(v, var("v")), (n, len_of_v.clone()), (r, var("v"))]);
            let frozen =
                receiver_mutation_frozen_locals(&local_exprs, body, arg_names, Some(operand));
            assert_eq!(frozen, HashSet::from([n]));
            propagate_mutating_receiver_state_with_captures(
                &mut local_exprs,
                body,
                arg_names,
                &var("v"),
                Some(operand),
                None,
            );
            assert_eq!(local_exprs[&n], len_of_v, "scalar read n is frozen");
            assert_eq!(local_exprs[&v], final_of(var("v")));
            assert_eq!(local_exprs[&r], final_of(var("v")));
        }),
    );
}

#[test]
fn captured_variable_is_a_place_of_the_closure_receiver() {
    run_on_caller(
        r#"
pub fn caller() -> i32 {
    let mut x: i32 = 0;
    let y = x;
    let mut c = || { x = 5; };
    c();
    y
}
"#,
        Box::new(|tcx, body, arg_names| {
            let x = named_local(body, arg_names, "x");
            let y = named_local(body, arg_names, "y");
            let c = named_local(body, arg_names, "c");
            let operand = first_arg_of_call(tcx, body, "call_mut");
            let places = mutated_place_locals(body, operand).expect("place located");
            assert!(places.contains(&c) && places.contains(&x), "{places:?}");

            let env = PureExpr::LogicFnCall {
                name: "__trust_wp_tuple1".to_string(),
                args: vec![var("x")],
            };
            let mut local_exprs = HashMap::from([(x, var("x")), (y, var("x")), (c, env.clone())]);
            let frozen =
                receiver_mutation_frozen_locals(&local_exprs, body, arg_names, Some(operand));
            assert_eq!(frozen, HashSet::from([y]));
            propagate_mutating_receiver_state_with_captures(
                &mut local_exprs,
                body,
                arg_names,
                &env,
                Some(operand),
                None,
            );
            assert_ne!(
                local_exprs[&x],
                var("x"),
                "captured x receives the post-call state"
            );
            assert_eq!(local_exprs[&y], var("x"), "copy y keeps the pre-call value");
        }),
    );
}

#[test]
fn unknown_receiver_place_freezes_nothing() {
    run_on_caller(
        r#"
pub fn caller() -> usize {
    let mut v: Vec<i32> = Vec::new();
    let n = v.len();
    v.push(1);
    n
}
"#,
        Box::new(|_tcx, body, arg_names| {
            let n = named_local(body, arg_names, "n");
            let local_exprs = HashMap::from([(n, PureExpr::View(Arc::new(var("v"))))]);
            assert!(
                receiver_mutation_frozen_locals(&local_exprs, body, arg_names, None).is_empty()
            );
        }),
    );
}
