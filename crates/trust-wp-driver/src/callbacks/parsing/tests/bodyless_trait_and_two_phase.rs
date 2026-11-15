// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[derive(Default)]
pub(super) struct TwoPhaseParsingProbe {
    pub(super) ran: bool,
    pub(super) call_assumptions: Vec<PureExpr>,
    pub(super) writebacks: Vec<ReborrowWriteback>,
}

#[derive(Default)]
#[allow(clippy::struct_excessive_bools)] // test probe struct, not a configuration
pub(super) struct BodylessTraitParsingProbe {
    pub(super) ran: bool,
    pub(super) missing_hir_body: bool,
    pub(super) parsed_contract: bool,
    pub(super) missing_result_expr: bool,
}

impl Callbacks for TwoPhaseParsingProbe {
    fn config(&mut self, config: &mut Config) {
        install_mir_borrowck_cache(config);
    }

    #[allow(clippy::elidable_lifetime_names)]
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        crate::callbacks::thread_locals::with_mir_session(tcx, || {
            let _ = tcx.analysis(());
            let contracts = find_contract_functions(tcx);
            let trait_contracts = find_trait_contracts(tcx);
            let trait_specs = build_trait_spec_table(tcx, &trait_contracts, &[]);
            let Some(contract) = contracts.iter().find(|contract| {
                tcx.def_path_str(contract.def_id)
                    .ends_with("push_len_contract")
            }) else {
                return Compilation::Stop;
            };
            let user_specs = HashMap::new();
            let extern_specs = HashMap::new();
            let extraction_ctx =
                ExtractionContext::new(&user_specs, &trait_specs, &extern_specs, &[], false, false);

            let parsed =
                parse_and_extract_contract(tcx, contract, &HashSet::new(), &extraction_ctx)
                    .expect("push_len_contract should parse and extract");

            self.call_assumptions = parsed.call_assumptions.clone();
            self.writebacks = parsed
                .mut_borrow
                .mut_borrow_body
                .as_ref()
                .and_then(|body| body.resolve_results.as_ref())
                .map(|results| results.writebacks.clone())
                .unwrap_or_default();
            self.ran = true;
            Compilation::Stop
        })
    }
}

impl Callbacks for BodylessTraitParsingProbe {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        crate::callbacks::thread_locals::with_mir_session(tcx, || {
            let _ = tcx.analysis(());
            let trait_contracts = find_trait_contracts(tcx);
            let Some(trait_contract) = trait_contracts
                .iter()
                .find(|contract| contract.method_name == "required_spec")
            else {
                return Compilation::Stop;
            };

            let local_def_id = trait_contract
                .method_def_id
                .as_local()
                .expect("trait method contract should be local");
            self.missing_hir_body = tcx.hir_node_by_def_id(local_def_id).body_id().is_none();

            let contract = FunctionContract {
                local_def_id,
                def_id: trait_contract.method_def_id,
                requires: trait_contract.requires.clone(),
                ensures: trait_contract.ensures.clone(),
                invariants: Vec::new(),
                per_loop_invariants: Vec::new(),
                per_loop_variants: Vec::new(),
                all_loop_spans: Vec::new(),
                variants: Vec::new(),
                terminates: false,
                ghost: false,
                trusted: false,
                trait_origin: None,
                capture_owner_only: false,
            };
            let trait_specs = build_trait_spec_table(tcx, &trait_contracts, &[]);
            let user_specs = HashMap::new();
            let extern_specs = HashMap::new();
            let extraction_ctx =
                ExtractionContext::new(&user_specs, &trait_specs, &extern_specs, &[], false, false);
            let parsed =
                parse_and_extract_contract(tcx, &contract, &HashSet::new(), &extraction_ctx);
            self.parsed_contract = parsed.is_some();
            self.missing_result_expr = parsed
                .as_ref()
                .is_some_and(|parsed_contract| parsed_contract.result_expr.is_none());
            self.ran = true;
            Compilation::Stop
        })
    }
}

pub(super) fn expr_is_delayed_writeback(
    expr: &PureExpr,
    parent_name: &str,
    child_name: &str,
) -> bool {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Eq, rhs) => {
            matches!(
                lhs.as_ref(),
                PureExpr::Deref(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == parent_name)
            ) && matches!(
                rhs.as_ref(),
                PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == child_name)
            )
        }
        _ => false,
    }
}

#[test]
fn parse_and_extract_contract_skips_mir_borrowck_for_bodyless_trait_method() {
    let source = r#"
pub trait SpecTrait {
    #[doc = "trust-wp:requires:true"]
    #[doc = "trust-wp:ensures:true"]
    fn required_spec(&self);
}

pub struct Impl;

impl SpecTrait for Impl {
    fn required_spec(&self) {}
}
"#;

    let unique = PARSING_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_parsing_bodyless_trait_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create parsing test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write parsing test source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_parsing_bodyless_trait_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = BodylessTraitParsingProbe::default();
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "bodyless trait parsing probe should complete without crashing"
    );
    assert!(
        callbacks.missing_hir_body,
        "required trait method should have no HIR body"
    );
    assert!(
        callbacks.parsed_contract,
        "parse_and_extract_contract should still return a parsed contract"
    );
    assert!(
        callbacks.missing_result_expr,
        "bodyless trait method should not synthesize a MIR result expression"
    );
}

#[test]
fn parse_and_extract_contract_suppresses_unsafe_two_phase_reservation_writeback() {
    let source = r#"
#[doc = "trust-wp:ensures:true"]
pub fn push_len_contract(v: &mut Vec<usize>) {
    v.push(v.len());
}
"#;

    let unique = PARSING_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_parsing_two_phase_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create parsing test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write parsing test source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_parsing_two_phase_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = TwoPhaseParsingProbe::default();
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "two-phase parsing probe should find and parse the fixture contract"
    );
    let writeback = callbacks
        .writebacks
        .iter()
        .find(|writeback| writeback.parent_name == "v" && writeback.activation.is_some())
        .expect("push(len()) should classify the receiver writeback as delayed");
    assert!(
        !callbacks
            .call_assumptions
            .iter()
            .any(|expr| expr_is_delayed_writeback(expr, "v", &writeback.child_name)),
        "the reservation-time writeback for spec-advanced `v.push(..)` must be suppressed; \
         otherwise it equates the entry value of `v` with the post-mutation child final"
    );
}
