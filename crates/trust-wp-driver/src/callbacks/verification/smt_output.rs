// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT-LIB2 output generation for function contracts.
//!
//! Generates SMT-LIB2 queries from function contracts for debugging and
//! inspection. Supports two emission sinks (#1691):
//!
//! - `--emit-smt`: raw query body to stdout (existing behavior)
//! - `--emit-smt-dir <path>`: per-function `.smt2` files with source-mapping
//!   comments under a crate/module/function directory tree

use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use tracing::warn;
use trust_wp_core::{
    formula::PureExpr,
    logic::{LogicFnDef, TypeInvariantDef},
    smt::SmtGenerator,
};
use trust_wp_driver::StdSpec;

use super::{
    super::{
        super::contracts::FunctionContract,
        closure_enrichment::{
            collect_closure_capture_infos, synthesized_ensures_from_capture_infos,
        },
        contract_rewrite::{build_user_shadowed_builtins, rewrite_parsed_contract_structure},
        ghost_context::collect_trusted_proof_assert_assumptions,
        integer_range::build_unsigned_range_preconditions,
        iterator_spec_rewrite::rewrite_iterator_spec_methods,
        parsing::{build_user_spec_table, parse_and_extract_contract, ExtractionContext},
    },
    clause_enrichment::{enrich_effective_clauses, EnrichmentData},
    contract_transform::transform_contract,
    PreparedVerification,
};

/// A generated SMT artifact for a single function contract.
pub(in crate::callbacks) struct GeneratedSmtArtifact {
    /// Rust def-path of the function (e.g., `my_crate::module::function`).
    pub(in crate::callbacks) def_path: String,
    /// Relative path for on-disk emission (e.g., `my_crate/module/function.smt2`)
    pub(in crate::callbacks) rel_path: PathBuf,
    /// The raw SMT-LIB2 query body (what `--emit-smt` prints)
    pub(in crate::callbacks) query_body: String,
    /// Header comments for the file sink (source location, contract text, etc.)
    pub(in crate::callbacks) file_comments: Vec<String>,
}

/// Build per-function SMT artifacts from contracts.
///
/// Applies the same pre-solver enrichment pipeline as `verify_contracts` so
/// that the emitted SMT-LIB2 reflects enriched clauses (const substitutions,
/// trusted assumptions, forall grounding, closure enrichment, type invariants).
///
/// **Remaining divergence**: the VC body is generated via `SmtGenerator` (simple
/// weakest-precondition), not the full ay separation-logic encoder used by
/// `dispatch_smt_verification`. Loop path VCs, recursive variant checks, and
/// solver-context captures (ghost blocks, indexed writes, ADT field ranges) are
/// not included. (#2123)
#[tracing::instrument(name = "trust_wp::build_smt_artifacts", level = "info", skip_all, fields(contracts = contracts.len()))]
pub(in crate::callbacks) fn build_smt_artifacts(
    tcx: TyCtxt<'_>,
    contracts: &[FunctionContract],
    recursive_fns: &HashSet<DefId>,
    type_invariant_defs: &[TypeInvariantDef],
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    logic_fns: &[LogicFnDef],
) -> Vec<GeneratedSmtArtifact> {
    let user_specs = build_user_spec_table(contracts);

    // Build logic method name set for structural rewriting (mirrors
    // prepare_verification in verification.rs).
    let logic_method_names: HashSet<String> = logic_fns
        .iter()
        .filter(|lf| lf.params().first().is_some_and(|p| p == "self"))
        .map(|lf| lf.name().to_string())
        .collect();
    let user_shadowed_builtins = build_user_shadowed_builtins(tcx);

    // Build const item substitutions (mirrors prepare_verification). (#2123)
    let const_item_substitutions: HashMap<String, PureExpr> = {
        use rustc_hir::def::DefKind;
        let mut map = HashMap::new();
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            if !matches!(
                tcx.def_kind(def_id),
                DefKind::Const { .. } | DefKind::AssocConst { .. }
            ) {
                continue;
            }
            if let Some(expr) =
                crate::mir_analysis::translate::resolve_const_item_value(tcx, def_id)
            {
                let full_path = tcx.def_path_str(def_id);
                if let Some(short_name) = full_path.rsplit("::").next() {
                    map.insert(short_name.to_string(), expr);
                }
            }
        }
        let generic_assoc_consts =
            crate::mir_analysis::extract::collect_generic_assoc_const_definitions(tcx);
        map.extend(generic_assoc_consts);
        map
    };

    // Collect trusted proof_assert assumptions. (#2123)
    // SMT emission does not run logic-function verification, so the raw
    // user_specs (no #1878 downgrade) is correct here — this is debug output.
    let (trusted_proof_assert_assumptions, _warnings) =
        collect_trusted_proof_assert_assumptions(tcx, contracts, &user_specs, logic_fns);

    // Build minimal PreparedVerification for enrichment. (#2123)
    let prep = PreparedVerification::for_smt_emission(
        user_specs.clone(),
        trusted_proof_assert_assumptions,
        const_item_substitutions,
    );

    let mut artifacts = Vec::with_capacity(contracts.len());

    for contract in contracts {
        let extraction_ctx = ExtractionContext::new(
            &user_specs,
            trait_specs,
            extern_specs,
            false,
            !type_invariant_defs.is_empty(),
        );
        let Some(mut parsed) =
            parse_and_extract_contract(tcx, contract, recursive_fns, &extraction_ctx)
        else {
            continue;
        };

        // Structural rewrites: type invariant methods, logic method calls,
        // newtype simplification, named struct field rewriting.
        rewrite_parsed_contract_structure(
            tcx,
            contract.def_id,
            &mut parsed,
            type_invariant_defs,
            &logic_method_names,
            &user_shadowed_builtins,
        );

        // Rewrite iterator spec methods for supported types (#2172)
        rewrite_iterator_spec_methods(&mut parsed);

        // Inject integer range preconditions BEFORE transform (matches
        // verify_contracts ordering — ranges feed into the transform).
        parsed.requires.extend(build_unsigned_range_preconditions(
            tcx,
            contract.def_id,
            &parsed.arg_names,
        ));

        let tc = transform_contract(&parsed);
        let mut effective_requires = tc.effective_requires;
        let mut effective_ensures = tc.effective_ensures;

        // Collect closure capture infos + synthesized ensures for enrichment. (#2123)
        let closure_capture_infos = collect_closure_capture_infos(
            tcx,
            contract.local_def_id,
            &user_specs,
            trait_specs,
            extern_specs,
        );
        let synth_ensures = synthesized_ensures_from_capture_infos(&closure_capture_infos);

        // Apply all clause enrichment passes — const substitution, trusted
        // PA assumptions, forall grounding, trivial closure rewriting, type
        // invariants, closure ensures enrichment. (#2123)
        let enrichment_data = EnrichmentData {
            type_invariant_defs,
            synthesized_closure_ensures: &synth_ensures,
            closure_capture_infos: &closure_capture_infos,
        };
        enrich_effective_clauses(
            tcx,
            contract,
            &mut parsed,
            &mut effective_requires,
            &mut effective_ensures,
            &prep,
            &enrichment_data,
        );

        // Generate SMT query body
        let mut vc_generator = SmtGenerator::new();

        let def_path = tcx.def_path_str(contract.def_id);
        let func_name = def_path.split("::").last().unwrap_or("unknown");

        vc_generator.generate_vc(
            func_name,
            &effective_requires,
            &effective_ensures,
            parsed.result_expr.as_ref(),
        );

        let query_body = vc_generator.output().to_string();
        let rel_path = def_path_to_rel_path(&def_path);

        // Build file-only header comments with source metadata.
        // Use the original contract text (Vec<String>) for human-readable comments,
        // not the parsed PureExpr vectors.
        let file_comments = build_file_comments(
            tcx,
            contract,
            &def_path,
            &contract.requires,
            &contract.ensures,
        );

        artifacts.push(GeneratedSmtArtifact {
            def_path,
            rel_path,
            query_body,
            file_comments,
        });
    }

    artifacts
}

/// Emit SMT artifacts to stdout (preserves existing `--emit-smt` behavior).
pub(in crate::callbacks) fn emit_smt_artifacts_to_stdout(artifacts: &[GeneratedSmtArtifact]) {
    for artifact in artifacts {
        tracing::debug!(def_path = %artifact.def_path, "emitting SMT to stdout");
        println!("{}", artifact.query_body);
    }
}

/// Write SMT artifacts to a directory tree under `root`.
///
/// Creates `root` and parent directories as needed. Each artifact is written to
/// `root/<rel_path>` with file-only header comments prepended before the query body.
pub(in crate::callbacks) fn write_smt_artifacts_to_dir(
    root: &Path,
    artifacts: &[GeneratedSmtArtifact],
) {
    if let Err(e) = std::fs::create_dir_all(root) {
        warn!(
            "trust-wp: failed to create SMT output directory {}: {e}",
            root.display()
        );
        return;
    }

    for artifact in artifacts {
        let target = root.join(&artifact.rel_path);
        if let Some(parent) = target.parent() {
            if let Err(e) = std::fs::create_dir_all(parent) {
                warn!(
                    "trust-wp: failed to create directory {}: {e}",
                    parent.display()
                );
                continue;
            }
        }

        let mut content = String::new();
        for comment in &artifact.file_comments {
            content.push_str("; ");
            content.push_str(comment);
            content.push('\n');
        }
        if !artifact.file_comments.is_empty() {
            content.push('\n');
        }
        content.push_str(&artifact.query_body);

        if let Err(e) = std::fs::write(&target, &content) {
            warn!(
                "trust-wp: failed to write SMT file {}: {e}",
                target.display()
            );
        }
    }
}

/// Convert a Rust def-path (e.g., `my_crate::module::func`) to a relative
/// filesystem path (e.g., `my_crate/module/func.smt2`).
///
/// Sanitizes each segment for filesystem safety (replaces non-alphanumeric
/// characters except `_` and `-` with `_`).
fn def_path_to_rel_path(def_path: &str) -> PathBuf {
    let segments: Vec<&str> = def_path.split("::").collect();
    let mut path = PathBuf::new();
    for (i, seg) in segments.iter().enumerate() {
        let sanitized = sanitize_path_segment(seg);
        if i == segments.len() - 1 {
            path.push(format!("{sanitized}.smt2"));
        } else {
            path.push(sanitized);
        }
    }
    path
}

/// Sanitize a path segment: replace non-alphanumeric characters (except `_`, `-`)
/// with `_`. Empty segments become `_`.
fn sanitize_path_segment(seg: &str) -> String {
    if seg.is_empty() {
        return "_".to_string();
    }
    seg.chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' || c == '-' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

/// Build file-level header comments for an SMT artifact.
fn build_file_comments(
    tcx: TyCtxt<'_>,
    contract: &FunctionContract,
    def_path: &str,
    requires: &[String],
    ensures: &[String],
) -> Vec<String> {
    let mut comments = Vec::new();

    // Function identity
    comments.push(format!("Function: {def_path}"));

    // Source location
    let span = tcx.def_span(contract.def_id);
    let source_map = tcx.sess.source_map();
    let loc = source_map.span_to_diagnostic_string(span);
    comments.push(format!("Source: {loc}"));

    // Contract summary
    if !requires.is_empty() {
        for (i, req) in requires.iter().enumerate() {
            comments.push(format!("requires[{i}]: {req}"));
        }
    }
    if !ensures.is_empty() {
        for (i, ens) in ensures.iter().enumerate() {
            comments.push(format!("ensures[{i}]: {ens}"));
        }
    }

    comments
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_def_path_to_rel_path_simple() {
        let path = def_path_to_rel_path("my_crate::module::func");
        assert_eq!(path, PathBuf::from("my_crate/module/func.smt2"));
    }

    #[test]
    fn test_def_path_to_rel_path_nested() {
        let path = def_path_to_rel_path("trust_wp_std::std::ops::add");
        assert_eq!(path, PathBuf::from("trust_wp_std/std/ops/add.smt2"));
    }

    #[test]
    fn test_def_path_to_rel_path_single_segment() {
        let path = def_path_to_rel_path("main");
        assert_eq!(path, PathBuf::from("main.smt2"));
    }

    #[test]
    fn test_def_path_to_rel_path_impl_method() {
        // Impl methods have angle brackets and spaces — both get sanitized
        let path = def_path_to_rel_path("my_crate::<impl MyStruct>::method");
        assert_eq!(path, PathBuf::from("my_crate/_impl_MyStruct_/method.smt2"));
    }

    #[test]
    fn test_sanitize_path_segment_basic() {
        assert_eq!(sanitize_path_segment("hello_world"), "hello_world");
        assert_eq!(sanitize_path_segment("my-crate"), "my-crate");
    }

    #[test]
    fn test_sanitize_path_segment_special_chars() {
        // Spaces and angle brackets are sanitized to _
        assert_eq!(sanitize_path_segment("<impl Foo>"), "_impl_Foo_");
        assert_eq!(sanitize_path_segment("a::b"), "a__b");
    }

    #[test]
    fn test_sanitize_path_segment_empty() {
        assert_eq!(sanitize_path_segment(""), "_");
    }

    #[test]
    fn test_write_artifacts_to_dir_creates_files() {
        let temp_dir =
            std::env::temp_dir().join(format!("trust-wp-smt-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&temp_dir);

        let artifacts = vec![GeneratedSmtArtifact {
            def_path: "test::func".to_string(),
            rel_path: PathBuf::from("test/func.smt2"),
            query_body: "(check-sat)\n".to_string(),
            file_comments: vec![
                "Function: test::func".to_string(),
                "Source: src/lib.rs:5:1".to_string(),
            ],
        }];

        write_smt_artifacts_to_dir(&temp_dir, &artifacts);

        let written = std::fs::read_to_string(temp_dir.join("test/func.smt2"))
            .expect("artifact file should exist");
        assert!(
            written.contains("; Function: test::func"),
            "missing header comment"
        );
        assert!(
            written.contains("; Source: src/lib.rs:5:1"),
            "missing source comment"
        );
        assert!(written.contains("(check-sat)"), "missing query body");

        let _ = std::fs::remove_dir_all(&temp_dir);
    }
}
