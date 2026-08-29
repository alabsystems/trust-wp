// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

struct RecursiveSelfSpecCallbacks {
    fn_name: String,
    non_recursive_param_names: Option<Vec<String>>,
    recursive_param_names: Option<Vec<String>>,
    ran: bool,
}

impl Callbacks for RecursiveSelfSpecCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let contracts = find_contract_functions(tcx);
        let suffix = format!("::{}", self.fn_name);
        let contract = contracts.iter().find(|contract| {
            let def_path = tcx.def_path_str(contract.def_id);
            def_path == self.fn_name || def_path.ends_with(&suffix)
        });
        let Some(contract) = contract else {
            return Compilation::Stop;
        };

        let user_specs = crate::callbacks::parsing::build_user_spec_table(&contracts);
        let arg_names = vec!["n".to_string()];
        let recursive_fns = HashSet::from([contract.def_id]);

        let non_recursive_specs =
            effective_user_specs_for_extraction(contract, &HashSet::new(), &arg_names, &user_specs);
        self.non_recursive_param_names = non_recursive_specs
            .get(&contract.def_id)
            .and_then(|spec| spec.param_names.clone());

        let recursive_specs =
            effective_user_specs_for_extraction(contract, &recursive_fns, &arg_names, &user_specs);
        self.recursive_param_names = recursive_specs
            .get(&contract.def_id)
            .and_then(|spec| spec.param_names.clone());
        self.ran = true;
        Compilation::Stop
    }
}

fn collect_recursive_self_spec_param_names(
    source: &str,
    fn_name: &str,
) -> (Option<Vec<String>>, Option<Vec<String>>) {
    let unique = PARSING_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_parsing_recursive_{}_{}",
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
        "trust_wp_parsing_recursive_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = RecursiveSelfSpecCallbacks {
        fn_name: fn_name.to_string(),
        non_recursive_param_names: None,
        recursive_param_names: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to inspect recursive self-spec injection for `{fn_name}`"
    );
    (
        callbacks.non_recursive_param_names,
        callbacks.recursive_param_names,
    )
}

#[test]
fn recursive_self_spec_injection_requires_recursive_membership() {
    let source = r#"
#[doc(hidden)]
#[doc = "trust-wp:ensures:result == 42"]
pub fn recursive_answer(n: i32) -> i32 {
    if n == 0 {
        42
    } else {
        recursive_answer(n - 1)
    }
}
"#;

    let (without_recursive_fns, with_recursive_fns) =
        collect_recursive_self_spec_param_names(source, "recursive_answer");
    assert!(
        without_recursive_fns.is_none(),
        "non-recursive extraction should preserve the original user spec without param_names, got {without_recursive_fns:?}"
    );
    assert!(
        with_recursive_fns == Some(vec!["n".to_string()]),
        "recursive_fns should inject explicit param_names for the self-spec, got {with_recursive_fns:?}"
    );
}
