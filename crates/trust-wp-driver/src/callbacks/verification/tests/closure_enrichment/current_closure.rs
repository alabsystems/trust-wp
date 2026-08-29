// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::ty::TyCtxt;
use trust_wp_core::closure::ClosureCaptureInfo;
use trust_wp_driver::StdSpec;

use super::super::rustc_callback_harness::{run_test_compiler_with_args, trust_wp_probe_args};
use crate::callbacks::{
    closure_enrichment::collect_closure_capture_infos, copy_mir_bodies,
    discovery::find_contract_functions, parsing::build_user_spec_table,
};

fn install_mir_borrowck_cache(config: &mut Config) {
    config.override_queries = Some(|_sess, providers| {
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

#[derive(Default)]
struct CurrentClosureCaptureSnapshot {
    contract_paths: Vec<String>,
    current_closure_path: Option<String>,
    infos: Vec<ClosureCaptureInfo>,
    ran: bool,
}

#[derive(Default)]
struct CurrentClosureCaptureCallbacks {
    snapshot: CurrentClosureCaptureSnapshot,
}

impl Callbacks for CurrentClosureCaptureCallbacks {
    fn config(&mut self, config: &mut Config) {
        install_mir_borrowck_cache(config);
    }

    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let contracts = find_contract_functions(tcx);
        self.snapshot.contract_paths = contracts
            .iter()
            .map(|contract| tcx.def_path_str(contract.def_id))
            .collect();

        let closure_contract = contracts
            .iter()
            .find(|contract| tcx.def_kind(contract.def_id) == DefKind::Closure)
            .expect("fixture should discover a contracted closure");
        self.snapshot.current_closure_path = Some(tcx.def_path_str(closure_contract.def_id));

        let root = tcx
            .typeck_root_def_id(closure_contract.def_id)
            .expect_local();
        let _ = tcx.mir_borrowck(root);

        let user_specs = build_user_spec_table(&contracts);
        let trait_specs: HashMap<DefId, StdSpec> = HashMap::new();
        let extern_specs: HashMap<String, StdSpec> = HashMap::new();
        self.snapshot.infos = collect_closure_capture_infos(
            tcx,
            closure_contract.local_def_id,
            &user_specs,
            &trait_specs,
            &extern_specs,
        );
        self.snapshot.ran = true;
        Compilation::Stop
    }
}

fn current_closure_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp::*;

pub fn host(x: i32) {
    let clos = #[ensures(result == x)] || x;
    let _ = clos();
}
"#
}

fn collect_current_closure_capture_snapshot(source: &str) -> CurrentClosureCaptureSnapshot {
    let mut callbacks = CurrentClosureCaptureCallbacks::default();
    run_test_compiler_with_args(
        source,
        "trust_wp_current_closure_capture",
        &trust_wp_probe_args(),
        &mut callbacks,
    );
    assert!(
        callbacks.snapshot.ran,
        "current-closure capture callback should run"
    );
    callbacks.snapshot
}

#[test]
fn collect_closure_capture_infos_seeds_current_closure_with_self_param_name() {
    let snapshot = collect_current_closure_capture_snapshot(current_closure_fixture_source());
    let current_closure_path = snapshot
        .current_closure_path
        .as_deref()
        .expect("fixture should record the closure path");
    let current_info = snapshot
        .infos
        .iter()
        .find(|info| info.def_id() == current_closure_path)
        .unwrap_or_else(|| {
            panic!(
                "current closure should seed its own capture info; closure={}, infos={:?}, contracts={:?}",
                current_closure_path,
                snapshot.infos,
                snapshot.contract_paths,
            )
        });

    assert_eq!(
        current_info.param_name(),
        Some("self"),
        "current closure verification should attach captures to the `self` environment",
    );
    let capture_names: Vec<_> = current_info
        .captures()
        .iter()
        .map(|field| field.name().to_string())
        .collect();
    assert_eq!(
        capture_names,
        vec!["x".to_string()],
        "current closure should report its own captures",
    );
    assert_eq!(
        snapshot.infos.len(),
        1,
        "fixture has no nested closures, so collection should only return the current closure",
    );
}
