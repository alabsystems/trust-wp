// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Real typed trait contracts must retain their bodies under parallel analysis.

use std::{collections::HashSet, time::Duration};

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::ty::TyCtxt;
use trust_wp_driver::builtin_trust_wp_std_specs;

use super::rustc_callback_harness::{run_test_compiler_with_args, trust_wp_probe_args};
use crate::callbacks::{
    apply_trait_contract_inheritance, build_trait_spec_table, find_contract_functions,
    find_trait_contracts, reporting::VerificationSummary, thread_locals::with_mir_session,
    try_get_body_with_context, verification::verify_contracts,
    verification_context::VerificationRunConfig, TrustWpCallbacks, TrustWpOptions,
};

#[derive(Default)]
struct TraitContractProbe {
    summary: Option<VerificationSummary>,
}

impl Callbacks for TraitContractProbe {
    fn config(&mut self, config: &mut Config) {
        // Exercise the production provider, including macro-vehicle erasure and
        // binding identities, instead of a test-only alternate MIR producer.
        TrustWpCallbacks::new(TrustWpOptions::default()).config(config);
    }

    fn after_expansion<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        with_mir_session(tcx, || {
            let _ = tcx.analysis(());
            let mut contracts = find_contract_functions(tcx);
            let traits = find_trait_contracts(tcx);
            apply_trait_contract_inheritance(&mut contracts, &traits);
            let trait_specs = build_trait_spec_table(tcx, &traits, &[]);
            let target = contracts
                .iter()
                .find(|contract| tcx.item_name(contract.def_id).as_str() == "omg")
                .expect("real macro contract discovered");
            assert_eq!(target.ensures.len(), 1);
            let retained = try_get_body_with_context(tcx, target.local_def_id)
                .expect("parallel analysis retained target MIR");
            assert!(retained.body.basic_blocks.iter().any(|block| {
                matches!(
                    block.terminator().kind,
                    rustc_middle::mir::TerminatorKind::Call { .. }
                )
            }));
            let extern_specs = builtin_trust_wp_std_specs();
            let recursive = HashSet::new();
            let run_config = VerificationRunConfig {
                all_contracts: &contracts,
                ghost_blocks: &[],
                logic_fns: &[],
                type_invariant_defs: &[],
                trait_specs: &trait_specs,
                trait_contracts: &traits,
                recursive_fns: &recursive,
                extern_specs: &extern_specs,
                verbose: false,
                track_level: Default::default(),
                timeout: Some(Duration::from_secs(10)),
                strict_axioms: false,
                strict_trust: true,
            };
            self.summary = Some(verify_contracts(tcx, &contracts, &run_config));
            Compilation::Stop
        })
    }
}

fn check(negated: bool) -> VerificationSummary {
    let source = format!(
        "#![feature(stmt_expr_attributes, proc_macro_hygiene)]\n\
         use trust_wp::*;\n\
         pub trait A {{\n\
             #[ensures(result == true)]\n\
             fn is_true(&self) -> bool;\n\
         }}\n\
         #[ensures(result == true)]\n\
         pub fn omg<T: A>(a: T) -> bool {{ {}a.is_true() }}\n",
        if negated { "!" } else { "" }
    );
    let mut args = trust_wp_probe_args();
    args.push("-Zthreads=6".to_string());
    let mut callbacks = TraitContractProbe::default();
    run_test_compiler_with_args(
        &source,
        "trust_wp_retained_trait_contract",
        &args,
        &mut callbacks,
    );
    callbacks.summary.expect("verification actually ran")
}

#[test]
fn mir_retention_parallel_trait_contract_verifies() {
    crate::compiler_test_process::run_isolated(
        concat!(
            module_path!(),
            "::mir_retention_parallel_trait_contract_verifies"
        ),
        || {
            let result = check(false);
            assert_eq!(result.verified, 1);
            assert_eq!(result.failed, 0);
            assert_eq!(result.errors, 0);
            assert_eq!(result.rustc_process_exit_code(), 0);
        },
    );
}

#[test]
fn mir_retention_parallel_reversed_trait_contract_is_refuted() {
    crate::compiler_test_process::run_isolated(
        concat!(
            module_path!(),
            "::mir_retention_parallel_reversed_trait_contract_is_refuted"
        ),
        || {
            let result = check(true);
            assert_eq!(result.verified, 0);
            assert_eq!(result.failed, 1);
            assert_eq!(result.errors, 0);
            assert_eq!(result.rustc_process_exit_code(), 1);
        },
    );
}
