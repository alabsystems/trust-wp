// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::atomic::{AtomicU64, Ordering};

use super::*;
use crate::callbacks::copy_mir_bodies;

static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Custom callbacks that install the bodyless-item `mir_borrowck` guard
/// (same as `TrustWpCallbacks::config`) and run analysis to verify bodyless
/// trait methods don't crash the compilation pipeline.
#[derive(Default)]
struct MirBorrowckGuardProbe {
    has_bodyless_trait_method: bool,
    ran: bool,
}

impl Callbacks for MirBorrowckGuardProbe {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_sess, providers| {
            crate::callbacks::spec_typecheck::install_spec_tc_mir_built_erasure(providers);
            providers.queries.mir_borrowck = |tcx, local_id| {
                // Same guard as TrustWpCallbacks::config (#2229)
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

    #[allow(
        clippy::elidable_lifetime_names,
        clippy::let_unit_value,
        clippy::ignored_unit_patterns
    )]
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        crate::callbacks::thread_locals::with_mir_session(tcx, || {
            // Run full analysis (type checking + borrow checking) with our
            // custom mir_borrowck provider installed via config(). Before the
            // body_id() guard (#2229), this could panic for crates with
            // bodyless trait methods via nested_bodies_within → body_owned_by.
            let _ = tcx.analysis(());

            // Verify the fixture has a bodyless trait method (test sanity check).
            for local_id in tcx.iter_local_def_id() {
                if tcx.def_kind(local_id) == DefKind::AssocFn
                    && !is_bodyful_trait_method(tcx, local_id)
                {
                    let parent = tcx.parent(local_id.to_def_id());
                    if tcx.def_kind(parent) == DefKind::Trait {
                        self.has_bodyless_trait_method = true;
                    }
                }
            }

            self.ran = true;
            Compilation::Stop
        })
    }
}

/// Regression test for #2229: bodyless trait methods must not crash the custom
/// `mir_borrowck` provider installed by `TrustWpCallbacks::config`.
///
/// Before the fix, `copy_mir_bodies` called `get_bodies_with_borrowck_facts`
/// for bodyless trait methods, which triggered `nested_bodies_within` →
/// `body_owned_by` → panic ("has no associated body"). The `body_id()` guard
/// in the `mir_borrowck` provider returns `Err` early for such items.
///
/// This test verifies end-to-end that `tcx.analysis(())` completes without
/// crashing when the guarded `mir_borrowck` provider is installed and the
/// crate contains bodyless trait methods with implementations.
#[test]
fn mir_borrowck_provider_does_not_crash_on_bodyless_trait_method() {
    let source = r#"
pub trait HasBodyless {
    fn bodyless(&self) -> bool;
    fn with_body(&self) -> bool { true }
}

pub struct MyStruct;
impl HasBodyless for MyStruct {
    fn bodyless(&self) -> bool { false }
}

pub fn use_trait<T: HasBodyless>(t: &T) -> bool {
    t.bodyless() && t.with_body()
}
"#;

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_mir_borrowck_guard_{}_{}",
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
        "trust_wp_mir_borrowck_guard_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = MirBorrowckGuardProbe::default();
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "mir_borrowck guard probe must complete without crashing (#2229)"
    );
    assert!(
        callbacks.has_bodyless_trait_method,
        "fixture must contain a bodyless trait method (test sanity check)"
    );
}
