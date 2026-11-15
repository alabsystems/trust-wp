// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use super::*;

const TEST_CRATE_NAME: &str = "trust_wp_discovery_trait_default_test";
static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

#[derive(Default)]
struct TraitDefaultProbeCallbacks {
    with_body_is_bodyful: Option<bool>,
    without_body_is_bodyful: Option<bool>,
    discovered_assoc_methods: HashSet<String>,
    trusted_assoc_methods: HashSet<String>,
    assoc_method_attr_values: HashMap<String, Vec<String>>,
    ran: bool,
}

#[derive(Default)]
struct ContractDiscoveryProbeCallbacks {
    discovered_paths: Vec<String>,
    ran: bool,
}

impl Callbacks for TraitDefaultProbeCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let contracts = find_contract_functions(tcx);
        self.discovered_assoc_methods = contracts
            .iter()
            .filter(|contract| tcx.def_kind(contract.def_id) == rustc_hir::def::DefKind::AssocFn)
            .map(|contract| tcx.item_name(contract.def_id).to_string())
            .collect();
        self.trusted_assoc_methods = contracts
            .iter()
            .filter(|contract| {
                contract.trusted
                    && tcx.def_kind(contract.def_id) == rustc_hir::def::DefKind::AssocFn
            })
            .map(|contract| tcx.item_name(contract.def_id).to_string())
            .collect();

        for local_def_id in tcx.iter_local_def_id() {
            let def_id = local_def_id.to_def_id();
            if tcx.def_kind(def_id) != rustc_hir::def::DefKind::AssocFn {
                continue;
            }

            let method_name = tcx.item_name(def_id).to_string();
            let attr_values: Vec<String> = tcx
                .get_all_attrs(def_id)
                .iter()
                // Trust 1.99 represents `#[doc = "..."]` as a parsed doc
                // attribute. `value_str()` only sees the legacy unparsed
                // representation, so use the same representation-independent
                // accessor as production marker discovery.
                .filter_map(|attr| {
                    crate::attr_utils::doc_marker_str(attr).map(|value| value.to_string())
                })
                .collect();
            if !attr_values.is_empty() {
                self.assoc_method_attr_values
                    .insert(method_name.clone(), attr_values);
            }

            match method_name.as_str() {
                "with_body" => {
                    self.with_body_is_bodyful = Some(is_bodyful_trait_method(tcx, local_def_id));
                }
                "without_body" => {
                    self.without_body_is_bodyful = Some(is_bodyful_trait_method(tcx, local_def_id));
                }
                _ => {}
            }
        }

        self.ran = true;
        Compilation::Stop
    }
}

impl Callbacks for ContractDiscoveryProbeCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.discovered_paths = find_contract_functions(tcx)
            .iter()
            .map(|contract| tcx.def_path_str(contract.def_id))
            .collect();
        self.ran = true;
        Compilation::Stop
    }
}

fn probe_trait_default_detection(source: &str) -> TraitDefaultProbeCallbacks {
    probe_trait_default_detection_with_args(source, &[])
}

fn probe_trait_default_detection_with_args(
    source: &str,
    extra_args: &[String],
) -> TraitDefaultProbeCallbacks {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_discovery_trait_default_{}_{}",
        std::process::id(),
        unique
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let mut args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        TEST_CRATE_NAME.to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    args.extend(extra_args.iter().cloned());

    let mut callbacks = TraitDefaultProbeCallbacks::default();
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to run discovery callback against test fixture"
    );
    callbacks
}

fn probe_contract_discovery_with_args(
    source: &str,
    extra_args: &[String],
) -> ContractDiscoveryProbeCallbacks {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_discovery_contracts_{}_{}",
        std::process::id(),
        unique
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let mut args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        TEST_CRATE_NAME.to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    args.extend(extra_args.iter().cloned());

    let mut callbacks = ContractDiscoveryProbeCallbacks::default();
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to run discovery callback against test fixture"
    );
    callbacks
}

fn dependency_artifact(crate_name: &str, extensions: &[&str]) -> PathBuf {
    trust_wp_test_utils::unit_dirs::UnitDirs::of_current_exe().artifact(crate_name, extensions)
}

fn trust_wp_macros_proc_macro_artifact() -> PathBuf {
    dependency_artifact("trust_wp_macros", &["dylib", "so", "dll"])
}

fn trust_wp_lib_artifact() -> PathBuf {
    // Crate-name form (underscore) — rustc emits `libtrust_wp-*.rmeta`.
    dependency_artifact("trust_wp", &["rmeta", "rlib"])
}

fn proc_macro_probe_args() -> Vec<String> {
    let macro_artifact = trust_wp_macros_proc_macro_artifact();
    let mut args = vec![
        "--extern".to_string(),
        format!("trust_wp_macros={}", macro_artifact.display()),
    ];
    args.extend(trust_wp_test_utils::unit_dirs::UnitDirs::of_current_exe().search_args());
    args
}

fn trust_wp_probe_args() -> Vec<String> {
    let trust_wp_artifact = trust_wp_lib_artifact();
    let macro_artifact = trust_wp_macros_proc_macro_artifact();
    let mut args = vec![
        "--extern".to_string(),
        // Crate-name form (underscore) — `--extern` consumes the rust crate
        // name, not the hyphenated package name.
        format!("trust_wp={}", trust_wp_artifact.display()),
        "--extern".to_string(),
        format!("trust_wp_macros={}", macro_artifact.display()),
    ];
    args.extend(trust_wp_test_utils::unit_dirs::UnitDirs::of_current_exe().search_args());
    args
}

fn trait_default_fixture_source() -> &'static str {
    r#"
pub trait Defaultable {
    fn with_body(&self) -> i32 {
        1
    }
    fn without_body(&self) -> i32;
}
"#
}

fn trait_default_with_doc_trusted_fixture_source() -> &'static str {
    r#"
pub trait TrustedByDoc {
    #[doc(hidden)]
    #[doc = "trust-wp:trusted:"]
    fn trusted_default(&self) -> i32 {
        42
    }
}
"#
}

fn trait_default_with_macro_trusted_fixture_source() -> &'static str {
    r#"
use trust_wp_macros::trusted;

pub trait TrustedByMacro {
    #[trusted]
    fn trusted_default(&self) -> i32 {
        42
    }
}
"#
}

fn trusted_proof_assert_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp::*;

#[ensures(b)]
pub fn assume(b: bool) {
    #[trusted]
    proof_assert! { b };
    let _ = b;
}
"#
}

fn trait_default_with_inactive_cfg_attr_fixture_source() -> &'static str {
    r#"
pub trait CfgTrusted {
    #[cfg_attr(any(), doc = "trust-wp:trusted:")]
    fn maybe_trusted(&self) -> i32 {
        42
    }
}
"#
}

fn trait_default_with_inner_doc_marker_fixture_source() -> &'static str {
    r#"
pub trait InnerTrusted {
    fn maybe_trusted(&self) -> i32 {
        #![doc = "trust-wp:trusted:"]
        42
    }
}
"#
}

fn trait_default_with_doc_text_mention_fixture_source() -> &'static str {
    r##"
pub trait MentionOnly {
    #[doc = "#[trusted]"]
    fn maybe_trusted(&self) -> i32 {
        42
    }
}
"##
}

#[path = "trait_default_bodyful_detection.rs"]
mod trait_default_bodyful_detection;
#[path = "trait_default_contract_behavior.rs"]
mod trait_default_contract_behavior;
#[path = "trait_default_trusted_behavior.rs"]
mod trait_default_trusted_behavior;
#[path = "trusted_marker_source.rs"]
mod trusted_marker_source;
