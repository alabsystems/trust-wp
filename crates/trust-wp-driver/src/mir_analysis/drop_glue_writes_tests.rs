// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIR-level pins for D-140's hand-off classification: which `Drop` and which
//! call may run drop glue that writes through what the value holds, and which
//! locals it then changes. Each test drives a real rustc over a plain crate
//! (no contracts), so the MIR is the one the lanes read.

use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Config};
use rustc_middle::{
    mir::{Local, TerminatorKind},
    ty::TyCtxt,
};

use super::extract::drop_glue_writes::{locals_changed_by_handoff, locals_reached_by_handoff};
use crate::callbacks::{copy_mir_bodies, thread_locals::clear_caches, try_get_body_with_context};

static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Per hand-off terminator of the probed function, in block order: whether a
/// local named `c` is among the locals it changes, whether the call's own
/// destination is, and whether a local named `v` is. `None` in the list is a
/// `Drop` or call that is NOT a hand-off.
type Observed = Vec<Option<(bool, bool, bool)>>;

/// Per terminator of the probed function that either reach calls a hand-off,
/// in block order: whether the parameter named `g` is among the locals the
/// extraction walks re-bind (`locals_changed_by_handoff`), and whether it is
/// among the locals the parameter-final lane havocs the parameters of
/// (`locals_reached_by_handoff`).
type ParamReach = Vec<(bool, bool)>;

struct HandoffCallbacks {
    fn_name: String,
    observed: Option<Observed>,
    param_reach: ParamReach,
    /// The first argument of the probed function's first recursive call, as
    /// the termination lane's recursive-call walk reads it (the function's
    /// one parameter named `n`).
    recursive_arg: Option<trust_wp_core::formula::PureExpr>,
}

impl Callbacks for HandoffCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_sess, providers| {
            crate::callbacks::spec_typecheck::install_spec_tc_mir_built_erasure(providers);
            providers.queries.mir_borrowck = |tcx, local_id| {
                if tcx.hir_node_by_def_id(local_id).body_id().is_none() {
                    let guar = tcx.dcx().span_delayed_bug(
                        tcx.def_span(local_id),
                        "mir_borrowck called for item without HIR body",
                    );
                    return Err(guar);
                }
                copy_mir_bodies(tcx, local_id);
                (rustc_interface::DEFAULT_QUERY_PROVIDERS
                    .queries
                    .mir_borrowck)(tcx, local_id)
            };
        });
    }

    #[allow(clippy::elidable_lifetime_names)]
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        crate::callbacks::thread_locals::with_mir_session(tcx, || {
            let _ = tcx.analysis(());
            let suffix = format!("::{}", self.fn_name);
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                let path = tcx.def_path_str(def_id);
                if path != self.fn_name && !path.ends_with(&suffix) {
                    continue;
                }
                let root = tcx.typeck_root_def_id(def_id).expect_local();
                let _ = tcx.mir_borrowck(root);
                let Some(body_with_facts) = try_get_body_with_context(tcx, owner) else {
                    continue;
                };
                let body = super::get_mir_body(&body_with_facts);
                let named = |name: &str| -> Option<Local> {
                    body.var_debug_info
                        .iter()
                        .find_map(|info| match &info.value {
                            rustc_middle::mir::VarDebugInfoContents::Place(place)
                                if info.name.as_str() == name && place.projection.is_empty() =>
                            {
                                Some(place.local)
                            }
                            _ => None,
                        })
                };
                let (c, v, g) = (named("c"), named("v"), named("g"));
                let mut observed = Vec::new();
                for (bb, data) in body.basic_blocks.iter_enumerated() {
                    if data.is_cleanup {
                        continue;
                    }
                    let terminator = data.terminator();
                    let destination = match &terminator.kind {
                        TerminatorKind::Drop { .. } => None,
                        TerminatorKind::Call { destination, .. } => Some(destination.local),
                        _ => continue,
                    };
                    let changed = locals_changed_by_handoff(tcx, body, bb, terminator);
                    let reached = locals_reached_by_handoff(tcx, body, bb, terminator);
                    if changed.is_some() || reached.is_some() {
                        let holds_g = |locals: &Option<std::collections::HashSet<Local>>| {
                            locals
                                .as_ref()
                                .is_some_and(|locals| g.is_some_and(|g| locals.contains(&g)))
                        };
                        self.param_reach
                            .push((holds_g(&changed), holds_g(&reached)));
                    }
                    observed.push(changed.map(|changed| {
                        (
                            c.is_some_and(|c| changed.contains(&c)),
                            destination.is_some_and(|dest| changed.contains(&dest)),
                            v.is_some_and(|v| changed.contains(&v)),
                        )
                    }));
                }
                self.observed = Some(observed);
                self.recursive_arg = crate::mir_analysis::extract_recursive_call_args(
                    body,
                    &["n".to_string()],
                    def_id,
                    Some(tcx),
                )
                .first()
                .and_then(|site| site.call_args.first())
                .cloned();
                break;
            }
            Compilation::Stop
        })
    }
}

fn observe(source: &str, fn_name: &str) -> Observed {
    let callbacks = run(source, fn_name);
    callbacks
        .observed
        .unwrap_or_else(|| panic!("failed to locate function `{fn_name}` in rustc callback"))
}

fn observe_param_reach(source: &str, fn_name: &str) -> ParamReach {
    let callbacks = run(source, fn_name);
    assert!(
        callbacks.observed.is_some(),
        "failed to locate function `{fn_name}` in rustc callback"
    );
    callbacks.param_reach
}

fn run(source: &str, fn_name: &str) -> HandoffCallbacks {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_drop_glue_writes_{}_{}",
        std::process::id(),
        unique
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");
    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");
    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_drop_glue_writes_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = HandoffCallbacks {
        fn_name: fn_name.to_string(),
        observed: None,
        param_reach: Vec::new(),
        recursive_arg: None,
    };
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();
    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);
    callbacks
}

/// The guard type every source below shares, with `$body` as its `Drop`.
fn guard(drop_body: &str, host: &str) -> String {
    format!(
        "pub struct G<'a>(pub &'a mut u32, pub u32);\n\
         impl Drop for G<'_> {{ fn drop(&mut self) {{ {drop_body} }} }}\n\
         pub fn consume<T>(t: T) {{ let _ = t; }}\n\
         {host}\n"
    )
}

const SCOPE_END: &str = "pub fn host() -> u32 { let mut c = 0u32; { let _g = G(&mut c, 1); } c }";

#[test]
fn a_drop_impl_that_writes_through_its_borrow_changes_the_borrowed_local() {
    let observed = observe(&guard("*self.0 = 5;", SCOPE_END), "host");
    assert_eq!(observed, vec![Some((true, false, false))], "{observed:?}");
}

#[test]
fn a_drop_impl_that_only_reads_through_its_borrow_is_no_hand_off() {
    let observed = observe(&guard("let _ = *self.0;", SCOPE_END), "host");
    assert_eq!(observed, vec![None], "{observed:?}");
}

#[test]
fn a_store_into_the_dying_values_own_plain_field_is_no_hand_off() {
    let observed = observe(&guard("self.1 = 0;", SCOPE_END), "host");
    assert_eq!(observed, vec![None], "{observed:?}");
}

#[test]
fn a_drop_impl_that_hands_its_borrow_to_a_call_may_write() {
    let source = guard(
        "bump(self.0);",
        &format!("pub fn bump(r: &mut u32) {{ *r += 0; }}\n{SCOPE_END}"),
    );
    let observed = observe(&source, "host");
    // The `+= 0` in `bump` is `bump`'s business; `host` sees the drop only.
    assert_eq!(
        observed.last(),
        Some(&Some((true, false, false))),
        "{observed:?}"
    );
}

#[test]
fn a_callee_handed_a_writing_guard_by_move_changes_the_borrowed_local_not_its_destination() {
    let host = "pub fn host() -> u32 { let mut c = 0u32; consume(G(&mut c, 1)); c }";
    let observed = observe(&guard("*self.0 = 5;", host), "host");
    assert_eq!(observed, vec![Some((true, false, false))], "{observed:?}");
}

#[test]
fn mem_forget_keeps_its_argument_and_runs_no_glue() {
    let host =
        "pub fn host() -> u32 { let mut c = 0u32; let g = G(&mut c, 1); std::mem::forget(g); c }";
    let observed = observe(&guard("*self.0 = 5;", host), "host");
    // The call to `forget` is no hand-off. The scope-end `Drop` of the
    // moved-out `g` is still in the MIR the lanes read (drop elaboration has
    // not run), and it is read as one: D-140's named completeness price.
    assert_eq!(
        observed,
        vec![None, Some((true, false, false))],
        "{observed:?}"
    );
}

#[test]
fn a_boxed_writing_guard_is_a_hand_off_through_the_box() {
    let host = "pub fn host() -> u32 { let mut c = 0u32; { let _b = Box::new(G(&mut c, 1)); } c }";
    let observed = observe(&guard("*self.0 = 5;", host), "host");
    // `Box::new` keeps its argument; the box's own drop runs `G::drop`.
    assert_eq!(observed.first(), Some(&None), "{observed:?}");
    assert_eq!(
        observed.last(),
        Some(&Some((true, false, false))),
        "{observed:?}"
    );
}

#[test]
fn a_std_container_of_plain_values_is_no_hand_off() {
    let source = "pub fn host() -> u32 { let mut c = 0u32; let r = &mut c; *r = 1; \
                  { let _v: Vec<u32> = Vec::new(); } c }";
    let observed = observe(source, "host");
    assert!(observed.iter().all(Option::is_none), "{observed:?}");
}

#[test]
fn a_container_a_call_stored_the_guard_in_reaches_the_borrowed_local_at_its_drop() {
    // `push` stores the guard in `v` and nothing flows into its `()` result:
    // only a flow that joins the call's arguments puts `c` in `v`'s reach.
    let host = "pub fn host() -> u32 { let mut c = 0u32; \
                { let mut v = Vec::new(); v.push(G(&mut c, 1)); } c }";
    let observed = observe(&guard("*self.0 = 5;", host), "host");
    // `v` itself is left out: it is uninitialized after its own drop.
    assert_eq!(
        observed,
        vec![None, None, Some((true, false, false))],
        "{observed:?}"
    );
}

#[test]
fn a_callee_lent_a_container_of_writing_guards_changes_the_borrowed_local_not_the_container() {
    let host = "pub fn host() -> u32 { let mut c = 0u32; let mut v = Vec::new(); \
                v.push(G(&mut c, 1)); v.clear(); std::mem::forget(v); c }";
    let observed = observe(&guard("*self.0 = 5;", host), "host");
    // `Vec::new`, `push` and `forget` never drop an element; `clear` drops
    // them in place. `v` itself is the call lane's to bind from `^self`.
    assert_eq!(
        observed,
        vec![
            None,
            None,
            Some((true, false, false)),
            None,
            Some((true, false, false))
        ],
        "{observed:?}"
    );
}

#[test]
fn a_generic_container_lent_to_a_callee_is_no_hand_off() {
    let source = "pub fn host<T>(v: &mut Vec<T>) { v.clear(); v.truncate(0); }";
    let observed = observe(source, "host");
    assert!(observed.iter().all(Option::is_none), "{observed:?}");
}

#[test]
fn a_container_of_plain_values_lent_to_a_callee_is_no_hand_off() {
    let source = "pub fn host() -> u32 { let mut c = 0u32; let mut v: Vec<&mut u32> = Vec::new(); \
                  v.push(&mut c); v.clear(); c }";
    let observed = observe(source, "host");
    assert!(observed.iter().all(Option::is_none), "{observed:?}");
}

#[test]
fn a_generic_value_dropped_at_its_scope_end_is_no_hand_off() {
    // `T`'s glue is the caller's: it may write, but nothing of this body's
    // but the dying local, and interior mutability, which `host` has none of.
    let source = "pub fn host<T>(t: T) -> u32 { let c = 0u32; { let _t = t; } c }";
    let observed = observe(source, "host");
    assert!(observed.iter().all(Option::is_none), "{observed:?}");
}

#[test]
fn a_standard_destructor_that_uses_a_borrowing_argument_is_a_hand_off() {
    // `BufWriter<W>`'s `Drop` flushes through `W::write`: `W` is not
    // `#[may_dangle]` there, and `W` holds a `&mut`.
    let source = "pub struct W<'a>(pub &'a mut u32);\n\
                  impl std::io::Write for W<'_> {\n\
                  fn write(&mut self, b: &[u8]) -> std::io::Result<usize> { *self.0 = 5; Ok(b.len()) }\n\
                  fn flush(&mut self) -> std::io::Result<()> { Ok(()) } }\n\
                  pub fn host() -> u32 { let mut c = 0u32; \
                  { let _b = std::io::BufWriter::new(W(&mut c)); } c }";
    let observed = observe(source, "host");
    assert_eq!(
        observed.last(),
        Some(&Some((true, false, false))),
        "{observed:?}"
    );
}

#[test]
fn a_standard_destructor_that_only_drops_a_borrowing_argument_is_no_hand_off() {
    // `Vec<T>`'s `Drop` takes `T` `#[may_dangle]`, and `W` has no glue.
    let source = "pub struct W<'a>(pub &'a mut u32);\n\
                  pub fn host() -> u32 { let mut c = 0u32; \
                  { let mut v = Vec::new(); v.push(W(&mut c)); } c }";
    let observed = observe(source, "host");
    assert!(observed.iter().all(Option::is_none), "{observed:?}");
}

#[test]
fn a_callee_lent_a_manually_dropped_writing_guard_is_a_hand_off() {
    // `ManuallyDrop<G>` has no glue of its own, but a holder of `&mut` to it
    // drops the `G` in place.
    let host = "pub fn host() -> u32 { let mut c = 0u32; \
                let mut m = std::mem::ManuallyDrop::new(G(&mut c, 1)); \
                unsafe { std::mem::ManuallyDrop::drop(&mut m) }; c }";
    let observed = observe(&guard("*self.0 = 5;", host), "host");
    assert_eq!(
        observed.last(),
        Some(&Some((true, false, false))),
        "{observed:?}"
    );
}

#[test]
fn a_generic_value_dropped_behind_a_reference_is_no_hand_off() {
    // `**x = value` drops the `T` in `*b`. Its glue writes only through
    // borrows the caller put in it, which no borrow of this body reaches, so
    // `r` keeps its binding (the h_final_control_write_inner_borrow shape).
    let source = "pub fn host<'a, T>(x: &mut &'a mut T, b: &'a mut T, value: T) { \
                  let r = &mut **x; *x = b; **x = value; let _ = r; }";
    let observed = observe(source, "host");
    assert!(observed.iter().all(Option::is_none), "{observed:?}");
}

#[test]
fn a_generic_value_beside_a_writing_guard_keeps_the_guards_reach() {
    let host = "pub fn host<T>(t: T) -> u32 { let mut c = 0u32; \
                { let _p = (t, G(&mut c, 1)); } c }";
    let observed = observe(&guard("*self.0 = 5;", host), "host");
    // The first is the tuple's scope-end `Drop`; the parameter's own, moved
    // out, is last and reaches nothing.
    assert_eq!(
        observed.first(),
        Some(&Some((true, false, false))),
        "{observed:?}"
    );
}

#[test]
fn an_async_future_whose_coroutine_has_no_glue_is_no_hand_off() {
    // The future is revealed to the coroutine `g` builds, which holds only a
    // `&mut u32`: dropping it unpolled runs no glue.
    let source = "pub async fn g(x: &mut u32) { *x = 5; }\n\
                  pub fn host() -> u32 { let mut c = 0u32; drop(g(&mut c)); c }";
    let observed = observe(source, "host");
    assert!(observed.iter().all(Option::is_none), "{observed:?}");
}

#[test]
fn an_async_future_that_owns_a_writing_guard_is_a_hand_off() {
    let host = "pub async fn g(_g: G<'_>) {}\n\
                pub fn host() -> u32 { let mut c = 0u32; drop(g(G(&mut c, 1))); c }";
    let observed = observe(&guard("*self.0 = 5;", host), "host");
    assert_eq!(
        observed.last(),
        Some(&Some((true, false, false))),
        "{observed:?}"
    );
}

#[test]
fn a_closure_lent_as_a_trait_object_is_read_as_the_closure() {
    // The unsizing coercion erased the closure's type, not what it holds: a
    // shared capture lends nothing a callee can drop.
    let source = "pub fn apply_dyn(f: &mut dyn FnMut() -> bool) -> bool { f() }\n\
                  pub fn host() -> u32 { let c = 0u32; let _ = apply_dyn(&mut || c == 0); c }";
    let observed = observe(source, "host");
    assert!(observed.iter().all(Option::is_none), "{observed:?}");
}

#[test]
fn a_closure_owning_a_writing_guard_lent_as_a_trait_object_is_a_hand_off() {
    // Calling the closure overwrites the guard it owns, which runs `G::drop`.
    let host = "pub fn apply_dyn(f: &mut dyn FnMut() -> bool) -> bool { f() }\n\
                pub fn host() -> u32 { let mut c = 0u32; let mut o = Some(G(&mut c, 1)); \
                let _ = apply_dyn(&mut move || { o = None; true }); c }";
    let observed = observe(&guard("*self.0 = 5;", host), "host");
    assert_eq!(
        observed.first(),
        Some(&Some((true, false, false))),
        "{observed:?}"
    );
}

#[test]
fn a_future_handed_to_a_callee_that_may_resume_it_is_a_hand_off() {
    // `mem::drop` above only runs the future's glue. A callee that owns it
    // may resume it instead, which runs its body and drops what it saved.
    let source = "pub async fn g(x: &mut u32) { *x = 5; }\n\
                  pub fn consume<T>(t: T) { let _ = t; }\n\
                  pub fn host() -> u32 { let mut c = 0u32; consume(g(&mut c)); c }";
    let observed = observe(source, "host");
    assert_eq!(
        observed.last(),
        Some(&Some((true, false, false))),
        "{observed:?}"
    );
}

#[test]
fn a_by_value_parameter_dropped_at_its_scope_end_is_reached_though_no_walk_reads_it_again() {
    // `g` is uninitialized after its own drop, so the walks re-bind nothing
    // of it; the final value of the borrow it holds is read after the glue
    // stored 5 through it, so the parameter-final lane must see it.
    let host = "pub fn host(g: G<'_>) { *g.0 = 0; }";
    let reach = observe_param_reach(&guard("*self.0 = 5;", host), "host");
    assert_eq!(reach, vec![(false, true)], "{reach:?}");
}

#[test]
fn a_by_value_parameter_moved_into_a_local_is_reached_at_that_locals_drop() {
    let host = "pub fn host(g: G<'_>) { *g.0 = 0; let _k = g; }";
    let reach = observe_param_reach(&guard("*self.0 = 5;", host), "host");
    assert!(reach.contains(&(true, true)), "{reach:?}");
}

#[test]
fn a_by_value_parameter_handed_to_a_callee_by_move_is_reached_at_the_call() {
    let host = "pub fn host(g: G<'_>) { *g.0 = 0; consume(g); }";
    let reach = observe_param_reach(&guard("*self.0 = 5;", host), "host");
    assert_eq!(
        reach.first().map(|(_, reached)| *reached),
        Some(true),
        "{reach:?}"
    );
}

#[test]
fn a_by_value_parameter_whose_drop_impl_only_reads_is_no_hand_off() {
    let host = "pub fn host(g: G<'_>) { *g.0 = 0; consume(g); }";
    let reach = observe_param_reach(&guard("let _ = *self.0;", host), "host");
    assert!(reach.is_empty(), "{reach:?}");
}

#[test]
fn a_user_impl_of_a_kept_trait_method_is_asked_as_the_impl_it_resolves_to() {
    // The keep-list names `IntoIterator::into_iter`; this impl is the host
    // crate's, and dropping `self` runs the writing glue.
    let host = "impl<'a> IntoIterator for G<'a> { type Item = u32; \
                type IntoIter = std::iter::Empty<u32>; \
                fn into_iter(self) -> Self::IntoIter { std::iter::empty() } }\n\
                pub fn host() -> u32 { let mut c = 0u32; let _it = G(&mut c, 1).into_iter(); c }";
    let observed = observe(&guard("*self.0 = 5;", host), "host");
    assert!(
        observed
            .iter()
            .any(|seen| matches!(seen, Some((true, _, _)))),
        "{observed:?}"
    );
}

fn recursive_arg(source: &str) -> trust_wp_core::formula::PureExpr {
    run(source, "f")
        .recursive_arg
        .unwrap_or_else(|| panic!("no recursive call of `f` extracted"))
}

fn is_fresh(arg: &trust_wp_core::formula::PureExpr) -> bool {
    matches!(arg, trust_wp_core::formula::PureExpr::Var(name, _)
        if crate::mir_analysis::is_fallback_arg_placeholder(name))
}

const RECURSIVE_HOST: &str = "pub fn f(n: u32) { if n == 0 { return; } let mut m = 0u32; \
                              { let _g = G(&mut m, 1); } f(m); }";

#[test]
fn a_recursive_call_reads_a_local_writing_glue_changed_as_a_fresh_value() {
    let arg = recursive_arg(&guard("*self.0 = 5;", RECURSIVE_HOST));
    assert!(is_fresh(&arg), "{arg:?}");
}

#[test]
fn a_recursive_call_reads_a_local_reading_glue_left_alone_as_its_value() {
    let arg = recursive_arg(&guard("let _ = *self.0;", RECURSIVE_HOST));
    assert!(!is_fresh(&arg), "{arg:?}");
}

#[test]
fn a_recursive_call_reads_a_local_stored_through_a_borrow_as_a_fresh_value() {
    let source = "pub fn f(n: u32) { if n == 0 { return; } let mut m = 0u32; \
                  let r = &mut m; *r = 5; f(m); }";
    let arg = recursive_arg(source);
    assert!(is_fresh(&arg), "{arg:?}");
}

#[test]
fn a_recursive_call_reads_a_local_written_through_a_field_as_a_fresh_value() {
    let source = "pub fn f(n: u32) { if n == 0 { return; } let mut p = (0u32, 0u32); \
                  p.0 = 5; f(p.0); }";
    let arg = recursive_arg(source);
    assert!(is_fresh(&arg), "{arg:?}");
}
