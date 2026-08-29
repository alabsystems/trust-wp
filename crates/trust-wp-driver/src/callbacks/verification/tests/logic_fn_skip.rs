// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    time::Duration,
};

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use trust_wp_core::{logic::TypeInvariantDef, TrackLevel};
use trust_wp_driver::StdSpec;

use super::rustc_callback_harness::{run_test_compiler, TEST_CRATE_NAME};
use crate::callbacks::{
    discovery::find_contract_functions,
    reporting::VerificationCounters,
    verification::{
        prepare_verification,
        skip_decision::{check_contract_skip, SkipDecision},
    },
    verification_context::VerificationRunConfig,
};

#[derive(Debug, Default)]
struct LogicFnSkipSnapshot {
    logic_fn_paths: HashSet<String>,
    logic_fn_has_ensures: HashSet<String>,
    skip_decisions: HashMap<String, &'static str>,
    ran: bool,
}

struct LogicFnSkipCallbacks {
    snapshot: LogicFnSkipSnapshot,
}

impl Callbacks for LogicFnSkipCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let contracts = find_contract_functions(tcx);
        let logic_fns = crate::logic::extract_logic_fn_defs(tcx);
        let trait_specs: HashMap<rustc_hir::def_id::DefId, StdSpec> = HashMap::new();
        let trait_contracts: &[crate::contracts::TraitMethodContract] = &[];
        let trait_refinement_overrides = HashSet::new();
        let recursive_fns = HashSet::new();
        let extern_specs: HashMap<String, StdSpec> = HashMap::new();
        let run_config = VerificationRunConfig {
            all_contracts: &contracts,
            ghost_blocks: &[] as &[crate::ghost::GhostBlock],
            logic_fns: &logic_fns,
            type_invariant_defs: &[] as &[TypeInvariantDef],
            trait_specs: &trait_specs,
            trait_contracts,
            trait_refinement_overrides: &trait_refinement_overrides,
            recursive_fns: &recursive_fns,
            extern_specs: &extern_specs,
            verbose: false,
            track_level: TrackLevel::Auto,
            timeout: Some(Duration::from_secs(5)),
            strict_axioms: false,
            strict_trust: false,
        };
        let mut counters = VerificationCounters::default();
        let mut unverified_axioms = HashSet::new();
        let prep = prepare_verification(
            tcx,
            &contracts,
            &run_config,
            &mut counters,
            &mut unverified_axioms,
        );

        self.snapshot.logic_fn_paths = prep.logic_fn_paths.clone();
        self.snapshot.logic_fn_has_ensures = prep.logic_fn_has_ensures.clone();
        self.snapshot.skip_decisions = contracts
            .iter()
            .map(|contract| {
                let def_path = tcx.def_path_str(contract.def_id);
                let decision = match check_contract_skip(
                    tcx,
                    contract,
                    &prep.logic_fn_paths,
                    &prep.logic_fn_has_ensures,
                ) {
                    SkipDecision::Verify => "Verify",
                    SkipDecision::Trusted => "Trusted",
                    SkipDecision::LogicFnAxiom => "LogicFnAxiom",
                    SkipDecision::LogicFnEnsures => "LogicFnEnsures",
                    SkipDecision::BodylessTraitMethod => "BodylessTraitMethod",
                };
                (def_path, decision)
            })
            .collect();
        self.snapshot.ran = true;
        Compilation::Stop
    }
}

fn collect_logic_fn_skip_snapshot(source: &str) -> LogicFnSkipSnapshot {
    let mut callbacks = LogicFnSkipCallbacks {
        snapshot: LogicFnSkipSnapshot::default(),
    };
    run_test_compiler(source, "trust_wp_logic_fn_skip", &mut callbacks);

    assert!(callbacks.snapshot.ran, "logic-fn skip callback should run");
    callbacks.snapshot
}

#[test]
fn logic_fn_path_aliases_prepare_verification_aligns_skip_decisions() {
    let source = r#"
mod specs {
    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:requires:x >= 0"]
    pub fn axiom(x: i32) -> i32 {
        x
    }

    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:ensures:result == x"]
    pub fn checked(x: i32) -> i32 {
        x
    }
}
"#;

    let snapshot = collect_logic_fn_skip_snapshot(source);
    let axiom_full = format!("{TEST_CRATE_NAME}::specs::axiom");
    let checked_full = format!("{TEST_CRATE_NAME}::specs::checked");

    assert!(snapshot.logic_fn_paths.contains(&axiom_full));
    assert!(snapshot.logic_fn_paths.contains("specs::axiom"));
    assert!(snapshot.logic_fn_paths.contains(&checked_full));
    assert!(snapshot.logic_fn_paths.contains("specs::checked"));

    assert!(!snapshot.logic_fn_has_ensures.contains(&axiom_full));
    assert!(!snapshot.logic_fn_has_ensures.contains("specs::axiom"));
    assert!(snapshot.logic_fn_has_ensures.contains(&checked_full));
    assert!(snapshot.logic_fn_has_ensures.contains("specs::checked"));

    assert_eq!(
        snapshot.skip_decisions.get("specs::axiom"),
        Some(&"LogicFnAxiom")
    );
    assert_eq!(
        snapshot.skip_decisions.get("specs::checked"),
        Some(&"LogicFnEnsures")
    );
}

#[test]
fn concrete_law_postconditions_are_axiomatized_while_trait_laws_still_verify() {
    let source = r#"
mod specs {
    #[doc = "trust-wp:logic:open:"]
    #[doc = "trust-wp:logic_law:"]
    #[doc = "trust-wp:logic_body:0"]
    #[doc = "trust-wp:ensures:result > 0"]
    pub fn assumed_law() -> i32 {
        0
    }

    #[doc = "trust-wp:logic:open:"]
    #[doc = "trust-wp:logic_body:0"]
    #[doc = "trust-wp:ensures:result > 0"]
    pub fn checked() -> i32 {
        0
    }
}

pub trait Laws {
    #[doc = "trust-wp:logic:open:"]
    #[doc = "trust-wp:logic_law:"]
    #[doc = "trust-wp:logic_body:()"]
    #[doc = "trust-wp:ensures:true"]
    fn trait_law() {}
}
"#;

    let snapshot = collect_logic_fn_skip_snapshot(source);
    let assumed_full = format!("{TEST_CRATE_NAME}::specs::assumed_law");
    let checked_full = format!("{TEST_CRATE_NAME}::specs::checked");
    let trait_full = format!("{TEST_CRATE_NAME}::Laws::trait_law");

    assert!(snapshot.logic_fn_paths.contains(&assumed_full));
    assert!(snapshot.logic_fn_paths.contains(&checked_full));
    assert!(snapshot.logic_fn_paths.contains(&trait_full));

    assert!(!snapshot.logic_fn_has_ensures.contains(&assumed_full));
    assert!(!snapshot.logic_fn_has_ensures.contains("specs::assumed_law"));
    assert!(snapshot.logic_fn_has_ensures.contains(&checked_full));
    assert!(snapshot.logic_fn_has_ensures.contains("specs::checked"));
    assert!(snapshot.logic_fn_has_ensures.contains(&trait_full));
    assert!(snapshot.logic_fn_has_ensures.contains("Laws::trait_law"));

    assert_eq!(
        snapshot.skip_decisions.get("specs::assumed_law"),
        Some(&"LogicFnAxiom")
    );
    assert_eq!(
        snapshot.skip_decisions.get("specs::checked"),
        Some(&"LogicFnEnsures")
    );
    assert_eq!(
        snapshot.skip_decisions.get("Laws::trait_law"),
        Some(&"LogicFnEnsures")
    );
}
