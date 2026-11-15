// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::{
    fs,
    panic::{catch_unwind, AssertUnwindSafe},
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Config};
use rustc_middle::ty::TyCtxt;

use super::*;

static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);

#[derive(Default)]
struct RetentionProbe {
    parent: Option<ContextKey>,
    nest: bool,
    checked: usize,
    cross_worker: bool,
}

impl Callbacks for RetentionProbe {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_, providers| {
            providers.queries.mir_borrowck = |tcx, def_id| {
                copy_mir_bodies(tcx, def_id);
                (rustc_interface::DEFAULT_QUERY_PROVIDERS
                    .queries
                    .mir_borrowck)(tcx, def_id)
            };
        });
    }

    fn after_expansion<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let owners: Vec<_> = tcx.hir_body_owners().collect();
        let first = owners[0];
        let key = ContextKey::of(tcx);
        assert!(try_get_body_with_context(tcx, first).is_none());
        // No active session means no call to the consumer or unowned storage.
        copy_mir_bodies(tcx, first);
        assert!(!registry().sessions.contains_key(&key));
        let mut first_generation = 0;
        let retained = with_mir_session(tcx, || {
            first_generation = registry().sessions[&key].generation;
            assert!(try_get_body_with_context(tcx, first).is_none());
            let _ = tcx.mir_borrowck(first);
            let retained = try_get_body_with_context(tcx, first).expect("first query retained");
            let pointer = Arc::as_ptr(&retained);
            // Analysis can schedule every remaining provider on other workers,
            // growing the registry while the first owned handle stays borrowed.
            let _ = tcx.analysis(());
            for owner in &owners {
                let body = try_get_body_with_context(tcx, *owner).expect("worker MIR retained");
                assert_eq!(body.body.source.def_id().expect_local(), *owner);
                self.cross_worker |= body.captured_on != std::thread::current().id();
                self.checked += 1;
            }
            assert_eq!(pointer, Arc::as_ptr(&retained));
            assert!(Arc::ptr_eq(
                &retained,
                &try_get_body_with_context(tcx, first).unwrap()
            ));
            // Refused same-context nesting must not destroy the outer entries,
            // including when recovering the mutex after the refusal unwinds.
            assert!(catch_unwind(AssertUnwindSafe(|| with_mir_session(tcx, || ()))).is_err());
            assert!(Arc::ptr_eq(
                &retained,
                &try_get_body_with_context(tcx, first).unwrap()
            ));
            if let Some(parent) = self.parent {
                let registry = registry();
                assert_ne!(key, parent);
                assert!(registry.sessions.contains_key(&parent));
                let outer = registry.sessions[&parent].bodies.get(&first).unwrap();
                let inner = registry.sessions[&key].bodies.get(&first).unwrap();
                assert!(
                    !Arc::ptr_eq(outer, inner),
                    "same LocalDefId is session scoped"
                );
            }
            if self.nest {
                // rustc requires distinct SessionGlobals on a fresh thread;
                // only the plain context identity crosses this boundary.
                let inner = std::thread::spawn(move || run_probe(Some(key), false))
                    .join()
                    .expect("nested compiler completed");
                assert!(inner.checked > 1);
                assert!(registry().sessions.contains_key(&key));
                assert!(try_get_body_with_context(tcx, first).is_some());
            }
            retained
        });
        assert!(try_get_body_with_context(tcx, first).is_none());
        // The returned Arc owns the MIR independently of registry cleanup,
        // while its type still carries this live compiler context's lifetime.
        assert_eq!(retained.body.source.def_id().expect_local(), first);
        assert!(!retained.body.local_decls.is_empty());
        assert!(!insert_retained(
            tcx,
            first_generation,
            first,
            Arc::clone(&retained)
        ));
        with_mir_session(tcx, || {
            assert!(try_get_body_with_context(tcx, first).is_none());
            let current_generation = registry().sessions[&key].generation;
            assert_ne!(current_generation, first_generation);
            // A capture started by the previous registration cannot publish
            // after teardown/reentry, even though this actual tcx stays live.
            assert!(!insert_retained(
                tcx,
                first_generation,
                first,
                Arc::clone(&retained)
            ));
            assert!(try_get_body_with_context(tcx, first).is_none());
            assert!(!insert_retained(
                tcx,
                current_generation,
                owners[1],
                Arc::clone(&retained)
            ));
            assert!(try_get_body_with_context(tcx, owners[1]).is_none());
            assert!(insert_retained(
                tcx,
                current_generation,
                first,
                Arc::clone(&retained)
            ));
            assert!(Arc::ptr_eq(
                &retained,
                &try_get_body_with_context(tcx, first).unwrap()
            ));
            // A stale cleanup token cannot erase a newer registration.
            drop(MirSessionGuard {
                key,
                generation: first_generation,
                context: PhantomData,
            });
            assert!(registry().sessions.contains_key(&key));
        });
        assert!(catch_unwind(AssertUnwindSafe(|| {
            with_mir_session(tcx, || panic!("retention unwind control"));
        }))
        .is_err());
        assert!(!registry().sessions.contains_key(&key));
        if let Some(parent) = self.parent {
            assert!(registry().sessions.contains_key(&parent));
        }
        Compilation::Stop
    }
}

fn run_probe(parent: Option<ContextKey>, nest: bool) -> RetentionProbe {
    let sequence = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
    let directory = std::env::temp_dir().join(format!(
        "trust-wp-retention-{}-{sequence}",
        std::process::id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let source_path = directory.join("source.rs");
    let mut source = String::from("#![allow(dead_code)]\n");
    // Distinct roots make the compiler's parallel body-owner traversal do real
    // work. No fabricated TyCtxt, body, or thread identity licenses the reads.
    for index in 0..96 {
        source.push_str(&format!(
            "pub fn body_{index}(x: i32) -> i32 {{ if x < {index} {{ x }} else {{ {index} }} }}\n"
        ));
    }
    fs::write(&source_path, source).unwrap();
    let args = vec![
        "trustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name=retention_probe".to_string(),
        "--crate-type=lib".to_string(),
        "--edition=2021".to_string(),
        "-Zthreads=6".to_string(),
        "--out-dir".to_string(),
        directory.to_string_lossy().into_owned(),
    ];
    let mut callbacks = RetentionProbe {
        parent,
        nest,
        ..RetentionProbe::default()
    };
    run_compiler(&args, &mut callbacks);
    fs::remove_dir_all(&directory).unwrap();
    callbacks
}

#[test]
fn mir_retention_cross_worker_lookup_is_owned_and_session_bound() {
    crate::compiler_test_process::run_isolated(
        concat!(
            module_path!(),
            "::mir_retention_cross_worker_lookup_is_owned_and_session_bound"
        ),
        || {
            let observed = run_probe(None, false);
            assert_eq!(observed.checked, 96);
            assert!(
                observed.cross_worker,
                "fixture must actually capture on a different worker"
            );
        },
    );
}

#[test]
fn mir_retention_nested_compilers_do_not_share_local_definition_keys() {
    crate::compiler_test_process::run_isolated(
        concat!(
            module_path!(),
            "::mir_retention_nested_compilers_do_not_share_local_definition_keys"
        ),
        || {
            let observed = run_probe(None, true);
            assert_eq!(observed.checked, 96);
        },
    );
}
