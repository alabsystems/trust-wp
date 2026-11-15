// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[derive(Default)]
struct GenericAssocConstDefinitionProbe {
    ran: bool,
    definitions: HashMap<String, PureExpr>,
}

#[derive(Default)]
struct QualifiedAssocConstContractProbe {
    ran: bool,
    ensures: Vec<PureExpr>,
}

impl Callbacks for GenericAssocConstDefinitionProbe {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        crate::callbacks::thread_locals::with_mir_session(tcx, || {
            let _ = tcx.analysis(());
            self.definitions =
                crate::mir_analysis::extract::collect_generic_assoc_const_definitions(tcx);
            self.ran = true;
            Compilation::Stop
        })
    }
}

impl Callbacks for QualifiedAssocConstContractProbe {
    fn config(&mut self, config: &mut Config) {
        install_mir_borrowck_cache(config);
    }

    #[allow(clippy::elidable_lifetime_names)]
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        crate::callbacks::thread_locals::with_mir_session(tcx, || {
            let _ = tcx.analysis(());
            let contracts = find_contract_functions(tcx);
            let Some(contract) = contracts
                .iter()
                .find(|contract| tcx.def_path_str(contract.def_id).ends_with("nat_i3_logic"))
            else {
                return Compilation::Stop;
            };
            let user_specs = HashMap::new();
            let trait_specs = HashMap::new();
            let extern_specs = HashMap::new();
            let extraction_ctx =
                ExtractionContext::new(&user_specs, &trait_specs, &extern_specs, &[], false, false);

            let parsed =
                parse_and_extract_contract(tcx, contract, &HashSet::new(), &extraction_ctx)
                    .expect("nat_i3_logic contract should parse and extract");

            self.ensures = parsed.ensures.clone();
            self.ran = true;
            Compilation::Stop
        })
    }
}

#[test]
fn collect_generic_assoc_const_definitions_tracks_qualified_paths() {
    let source = r#"
pub trait Nat {
    const VALUE: usize;
}

pub struct I3<T: Nat>(T);

impl<T: Nat> Nat for I3<T> {
    const VALUE: usize = const { T::VALUE + T::VALUE };
}

pub fn nat_i3_logic<T: Nat>() {}
"#;

    let unique = PARSING_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_assoc_const_contract_parse_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create assoc const parsing temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write assoc const parsing source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_assoc_const_contract_parse_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = GenericAssocConstDefinitionProbe::default();
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(callbacks.ran, "assoc const definition probe should run");
    let body_text = callbacks
        .definitions
        .get("<I3<T> as Nat>::VALUE")
        .map(ToString::to_string)
        .expect("generic assoc const collector should record the qualified I3 value path");
    assert!(
        body_text.contains("T::VALUE"),
        "collected definition should preserve the symbolic inner assoc const: {body_text}"
    );
    assert!(
        body_text.contains('+'),
        "collected definition should preserve the additive body shape: {body_text}"
    );
}

#[test]
fn parse_and_extract_contract_rewrites_module_qualified_assoc_const_ensures() {
    let source = r#"
mod traits {
    pub trait Nat {
        const VALUE: usize;
    }
}

use traits::Nat;

pub struct I3<T: Nat>(T);

impl<T: Nat> traits::Nat for I3<T> {
    const VALUE: usize = const { T::VALUE + T::VALUE };
}

#[doc = "trust-wp:ensures:<I3<T> as traits::Nat>::VALUE@ == T::VALUE@ + T::VALUE@"]
pub fn nat_i3_logic<T: traits::Nat>() -> usize {
    <I3<T> as traits::Nat>::VALUE
}
"#;

    let unique = PARSING_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_assoc_const_contract_rewrite_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create assoc const rewrite temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write assoc const rewrite source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_assoc_const_contract_rewrite_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = QualifiedAssocConstContractProbe::default();
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "qualified assoc const contract probe should run"
    );
    let ensures_text: Vec<String> = callbacks.ensures.iter().map(ToString::to_string).collect();
    assert!(
        ensures_text
            .iter()
            .all(|text| !text.contains("<I3<T> as traits::Nat>::VALUE")),
        "parsed ensures should not retain the module-qualified assoc const path: {ensures_text:?}"
    );
    assert!(
        ensures_text
            .iter()
            .any(|text| text.contains("T::VALUE") && text.contains('+')),
        "parsed ensures should include the symbolic associated-const body: {ensures_text:?}"
    );
}

#[test]
fn parse_and_extract_contract_rewrites_super_qualified_assoc_const_ensures() {
    let source = r#"
#![allow(dead_code)]

mod outer {
    pub mod traits {
        pub trait Nat {
            const VALUE: usize;
        }
    }

    use traits::Nat;

    pub struct I3<T: Nat>(T);

    impl<T: Nat> traits::Nat for I3<T> {
        const VALUE: usize = const { T::VALUE + T::VALUE };
    }

    pub mod nested {
        use super::I3;

        #[doc = "trust-wp:ensures:<I3<T> as super::traits::Nat>::VALUE@ == T::VALUE@ + T::VALUE@"]
        pub fn nat_i3_logic<T: super::traits::Nat>() -> usize {
            <I3<T> as super::traits::Nat>::VALUE
        }
    }
}
"#;

    let unique = PARSING_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_assoc_const_contract_super_rewrite_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create assoc const super rewrite temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write assoc const super rewrite source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_assoc_const_contract_super_rewrite_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = QualifiedAssocConstContractProbe::default();
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "super-qualified assoc const contract probe should run"
    );
    let ensures_text: Vec<String> = callbacks.ensures.iter().map(ToString::to_string).collect();
    assert!(
        ensures_text
            .iter()
            .all(|text| !text.contains("<I3<T> as super::traits::Nat>::VALUE")),
        "parsed ensures should not retain the super-qualified assoc const path: {ensures_text:?}"
    );
    assert!(
        ensures_text
            .iter()
            .any(|text| text.contains("T::VALUE") && text.contains('+')),
        "parsed ensures should include the symbolic associated-const body for super-qualified trait paths: {ensures_text:?}"
    );
}
