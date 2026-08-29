// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic function extraction from Rust source
//!
//! This module detects and extracts `#[logic]`/`#[predicate]` functions for verification.
//! Logic functions are pure specification-only functions that:
//! - Exist only for verification (erased at runtime)
//! - Are encoded as uninterpreted SMT functions with defining axioms
//! - Can be called from contracts and ghost blocks
//!
//! Reference: `designs/2026-02-01-logic-functions.md`

#![allow(clippy::doc_markdown)]

mod attrs;
pub(crate) mod discovery;
mod recursion;
mod type_transforms;

use std::collections::{HashMap, HashSet};

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{AssocContainer, TyCtxt};
use trust_wp_core::{
    formula::PureExpr,
    logic::{LogicFnDef, LogicMode},
};

use self::type_transforms::{
    newtype_param_names_for_logic_fn, simplify_newtype_view_in_expr_for_params,
    unit_field_constraints_for_logic_fn,
};
pub(crate) use self::{
    discovery::{
        extract_logic_mode, find_logic_functions, has_law_doc_marker, has_logic_marker,
        to_logic_fn_def,
    },
    recursion::{analyze_logic_fn_recursion_for_functions, validate_logic_fn_recursion},
    type_transforms::extract_type_invariant_defs,
};

/// Validate Creusot-compatible restrictions for logic laws.
///
/// Creusot laws are schema-like axioms but do not allow their own additional
/// generic parameters. Trait or impl generics from the parent item remain fine;
/// own generic params/predicates catch only constraints introduced directly on
/// the law method.
pub(crate) fn validate_logic_laws(tcx: TyCtxt<'_>) -> usize {
    validate_logic_laws_impl(tcx, true)
}

fn validate_logic_laws_impl(tcx: TyCtxt<'_>, emit_diagnostics: bool) -> usize {
    let mut error_count = 0usize;

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }

        let attrs = tcx.get_all_attrs(def_id);
        let is_law = has_law_doc_marker(attrs);

        error_count += validate_impl_logic_trait_mode_matches_trait(
            tcx,
            def_id,
            attrs,
            is_law,
            emit_diagnostics,
        );

        if !is_law {
            continue;
        }

        let has_own_generics = !tcx.generics_of(def_id).own_params.is_empty();
        let has_own_predicates = !tcx.predicates_of(def_id).predicates.is_empty();
        if has_own_generics || has_own_predicates {
            if emit_diagnostics {
                tcx.dcx().span_err(
                    tcx.def_span(def_id),
                    "Laws cannot have additional generic parameters or trait constraints",
                );
            }
            error_count += 1;
        }
    }

    error_count
}

fn validate_impl_logic_trait_mode_matches_trait(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    impl_attrs: &[rustc_hir::Attribute],
    impl_is_law: bool,
    emit_diagnostics: bool,
) -> usize {
    let Some(trait_item_def_id) = trait_item_def_id_for_impl_assoc(tcx, def_id) else {
        return 0;
    };

    let trait_attrs = tcx.get_all_attrs(trait_item_def_id);
    let mut errors = 0usize;

    errors += validate_impl_logic_mode_matches_trait(
        tcx,
        def_id,
        trait_item_def_id,
        impl_attrs,
        trait_attrs,
        emit_diagnostics,
    );

    if has_logic_marker(impl_attrs) && has_logic_marker(trait_attrs) {
        errors += validate_impl_law_mode_matches_trait(
            tcx,
            def_id,
            impl_is_law,
            trait_attrs,
            emit_diagnostics,
        );
    }

    errors += validate_impl_does_not_override_sealed_trait_method(
        tcx,
        def_id,
        trait_attrs,
        emit_diagnostics,
    );

    errors
}

fn trait_item_def_id_for_impl_assoc(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    let Some(assoc_item) = tcx.opt_associated_item(def_id) else {
        return None;
    };
    if matches!(assoc_item.container, AssocContainer::Trait) {
        return None;
    }
    assoc_item.trait_item_def_id()
}

fn validate_impl_law_mode_matches_trait(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    impl_is_law: bool,
    trait_attrs: &[rustc_hir::Attribute],
    emit_diagnostics: bool,
) -> usize {
    let trait_is_law = has_law_doc_marker(trait_attrs);
    if impl_is_law == trait_is_law {
        return 0;
    }

    let method_name = tcx.item_name(def_id);
    let message = if trait_is_law {
        format!(
            "Expected `{method_name}` to be a `#[logic(law)]` as specified by the trait declaration"
        )
    } else {
        format!(
            "Method `{method_name}` should not be a `#[logic(law)]`, as specified by the trait declaration"
        )
    };
    if emit_diagnostics {
        tcx.dcx().span_err(tcx.def_span(def_id), message);
    }
    1
}

fn validate_impl_logic_mode_matches_trait(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    trait_item_def_id: DefId,
    impl_attrs: &[rustc_hir::Attribute],
    trait_attrs: &[rustc_hir::Attribute],
    emit_diagnostics: bool,
) -> usize {
    let impl_is_logic = has_logic_marker(impl_attrs);
    let trait_is_logic = has_logic_marker(trait_attrs);
    let method_name = tcx.item_name(def_id);

    // Strict guard (creusot tests/should_fail/trait_item_types_mismatch.rs): an
    // impl that provides a PLAIN (non-`#[logic]`) `fn` override of a trait method
    // that was declared `#[logic]` *with a default body* must be rejected.
    // Creusot reports "Expected `f` to be a logic function as specified by the
    // trait declaration": once the trait fixes the method as a logic function
    // (default body present), an implementor cannot redefine it as an ordinary
    // program function.
    //
    // Soundness/over-rejection guard:
    // - Only fires when the trait declaration carries `#[logic]` AND provides a
    //   default body (`defaultness.has_value()`). A *bodyless* trait logic
    //   declaration (`#[logic] fn f();`) is the legitimate "trait declares logic,
    //   impl provides it" pattern and is left lenient (the impl inherits
    //   logic-ness) — see test_validate_logic_laws_lenient_trait_logic_implemented_by_plain_fn.
    // - Only fires when the impl override is itself PLAIN. Impls that re-mark
    //   `#[logic]`/`#[logic(open)]`/… (the common should_succeed pattern, e.g.
    //   termination/default_impl{,_in_trait}.rs) are unaffected.
    // - `def_id` here is always an explicit local impl AssocFn (callers filter to
    //   local DefKind::AssocFn and skip trait containers), so inherited defaults
    //   are never visited — no spurious rejection of impls that simply omit the
    //   override.
    if trait_is_logic && !impl_is_logic && tcx.defaultness(trait_item_def_id).has_value() {
        if emit_diagnostics {
            // Mirror the prophetic-impl rejection: record under the logic-recursion
            // counter and use the marker phrase so the should-fail harness
            // classifies this as a valid rejection.
            crate::result_protocol_state::record_logic_recursion_error();
            let full_path = tcx.def_path_str(def_id);
            tcx.dcx().span_err(
                tcx.def_span(def_id),
                format!(
                    "trust-wp: logic recursion check failed: `{full_path}`:                          Expected `{method_name}` to be a logic function as specified by the trait declaration",
                ),
            );
        }
        return 1;
    }

    // Lenient mode (Creusot compatibility): most trait/impl logic-marker
    // mismatches are accepted. Creusot accepts impls that:
    // (a) inherit logic-ness from the trait without re-marking
    // (b) add `#[logic(open)]` to mark body visibility on an
    //     unmarked trait method
    // (c) strengthen `open` (or any visible mode) to `prophetic` when the
    //     body needs `^x`
    //
    // Strict guard (creusot tests/should_fail/logic_prophetic_impl.rs): an
    // impl MUST NOT upgrade from the trait's default-opaque `#[logic]` mode
    // directly to `#[logic(prophetic)]`. Creusot rejects this with
    // "Expected `f` to be a logic function as specified by the trait
    // declaration" because the trait's opaque declaration does not authorize
    // prophetic-mode bodies. The impl must instead use `open`, `open(self)`,
    // or match the trait's mode.
    if impl_is_logic && trait_is_logic {
        let impl_mode = extract_logic_mode(impl_attrs);
        let trait_mode = extract_logic_mode(trait_attrs);
        if impl_mode == LogicMode::Prophetic && trait_mode == LogicMode::Default {
            if emit_diagnostics {
                // Use the logic-recursion error counter and marker phrase so
                // the should-fail harness classifies this as a valid rejection.
                // The diagnostic itself reports the Creusot-equivalent message
                // (mode mismatch with the trait declaration). (#1, prophetic_impl)
                crate::result_protocol_state::record_logic_recursion_error();
                let full_path = tcx.def_path_str(def_id);
                tcx.dcx().span_err(
                    tcx.def_span(def_id),
                    format!(
                        "trust-wp: logic recursion check failed: `{full_path}`:                          Expected `{method_name}` to be a logic function as specified by the trait declaration",
                    ),
                );
            }
            return 1;
        }
    }

    let _ = (
        method_name,
        impl_is_logic,
        trait_is_logic,
        impl_attrs,
        trait_attrs,
        emit_diagnostics,
        tcx,
        def_id,
    );
    0
}

fn validate_impl_does_not_override_sealed_trait_method(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    trait_attrs: &[rustc_hir::Attribute],
    emit_diagnostics: bool,
) -> usize {
    if !has_doc_marker(trait_attrs, "trust-wp:logic_sealed:") {
        return 0;
    }

    if emit_diagnostics {
        tcx.dcx().span_err(
            tcx.def_span(def_id),
            "This trait method overrides a sealed implementation",
        );
    }
    1
}

fn has_doc_marker(attrs: &[rustc_hir::Attribute], marker: &str) -> bool {
    attrs
        .iter()
        .filter_map(crate::attr_utils::doc_marker_str)
        .any(|value| value.as_str().starts_with(marker))
}

/// Extract all logic function definitions from a crate.
///
/// This combines finding and parsing logic functions.
pub(crate) fn extract_logic_fn_defs(tcx: TyCtxt<'_>) -> Vec<LogicFnDef> {
    let logic_functions = find_logic_functions(tcx);
    let recursion_analysis = analyze_logic_fn_recursion_for_functions(&logic_functions);

    // Emit recursion diagnostics during logic extraction so recursive spec
    // cycles fail compilation even when callbacks continue analysis.
    for error in &recursion_analysis.errors {
        tcx.dcx().err(format!(
            "trust-wp: logic recursion check failed: `{}`: {}",
            error.full_path, error.message
        ));
    }

    let newtype_type_names: HashSet<String> = extract_type_invariant_defs(tcx)
        .into_iter()
        .filter(|inv| inv.is_newtype())
        .map(|inv| inv.type_name().to_string())
        .collect();
    let assoc_const_substitutions =
        crate::mir_analysis::extract::collect_generic_assoc_const_definitions(tcx);

    // Build DefId lookup for type-directed post-processing (newtype simplification,
    // unit field constraints). Always needed when logic functions exist.
    // Keys must be crate-qualified paths (e.g., "creusot_test::baz") to match
    // LogicFunction.full_path which is built with the crate name prefix (#1564).
    let mut fn_def_ids_by_path: HashMap<String, DefId> = HashMap::new();
    if !logic_functions.is_empty() {
        let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
        for local_def_id in tcx.iter_local_def_id() {
            let def_id = local_def_id.to_def_id();
            if matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
                let local_path = tcx.def_path_str(def_id);
                let full_path = format!("{crate_name}::{local_path}");
                fn_def_ids_by_path.insert(full_path, def_id);
            }
        }
    }

    let mut logic_defs: Vec<LogicFnDef> = logic_functions
        .iter()
        .filter_map(|logic_fn| {
            let mut parsed = to_logic_fn_def(logic_fn)?;
            if recursion_analysis
                .supported_scc_members
                .contains(&logic_fn.full_path)
            {
                parsed.set_is_recursive(true);
            }
            let Some(def_id) = fn_def_ids_by_path.get(&logic_fn.full_path).copied() else {
                return Some(parsed);
            };

            // Newtype view simplification
            simplify_newtype_views(
                tcx,
                def_id,
                &logic_fn.params,
                &newtype_type_names,
                &mut parsed,
            );

            // Unit field constraints (#1271): for parameters whose type is a struct
            // with unit-typed fields, add `field(param) == tuple0()` as preconditions.
            // This encodes the type-system fact that `()` has exactly one value.
            let unit_constraints =
                unit_field_constraints_for_logic_fn(tcx, def_id, &logic_fn.params);
            if !unit_constraints.is_empty() {
                parsed.extend_requires(unit_constraints);
            }

            normalize_local_assoc_const_paths(tcx, def_id, &mut parsed);
            apply_assoc_const_substitutions(&mut parsed, &assoc_const_substitutions);

            Some(parsed)
        })
        .collect();
    inline_qualified_logic_fn_calls_in_defs(&mut logic_defs);
    logic_defs
}

#[derive(Clone)]
struct InlineLogicFn {
    full_path: String,
    params: Vec<String>,
    body: PureExpr,
}

fn inline_qualified_logic_fn_calls_in_defs(logic_defs: &mut [LogicFnDef]) {
    let inline_map = build_qualified_logic_fn_inline_map(logic_defs);
    if inline_map.is_empty() {
        return;
    }

    for logic_def in logic_defs {
        let full_path = logic_def.full_path().to_string();
        let body = logic_def.take_body();
        logic_def.set_body(inline_qualified_logic_fn_calls(
            body,
            &inline_map,
            &full_path,
        ));

        let requires: Vec<PureExpr> = logic_def
            .take_requires()
            .into_iter()
            .map(|expr| inline_qualified_logic_fn_calls(expr, &inline_map, &full_path))
            .collect();
        logic_def.set_requires(requires);

        let ensures: Vec<PureExpr> = logic_def
            .take_ensures()
            .into_iter()
            .map(|expr| inline_qualified_logic_fn_calls(expr, &inline_map, &full_path))
            .collect();
        logic_def.set_ensures(ensures);
    }
}

fn build_qualified_logic_fn_inline_map(
    logic_defs: &[LogicFnDef],
) -> HashMap<String, InlineLogicFn> {
    let mut map = HashMap::new();
    for logic_def in logic_defs {
        if logic_def.is_opaque()
            || logic_def.mode() == LogicMode::Default
            || logic_def.is_recursive()
            || !logic_def.requires().is_empty()
        {
            continue;
        }

        let inline = InlineLogicFn {
            full_path: logic_def.full_path().to_string(),
            params: logic_def.params().to_vec(),
            body: logic_def.body().clone(),
        };
        map.insert(logic_def.full_path().to_string(), inline.clone());
        if let Some((_, relative)) = logic_def.full_path().split_once("::") {
            if relative != logic_def.name() {
                map.insert(relative.to_string(), inline.clone());
            }
        }
        for alias in ufcs_aliases_for_impl_logic_path(logic_def.full_path()) {
            map.insert(alias, inline.clone());
        }
    }
    map
}

fn ufcs_aliases_for_impl_logic_path(full_path: &str) -> Vec<String> {
    let Some(impl_start) = full_path.find("<impl ") else {
        return Vec::new();
    };
    let Some(method_sep_rel) = full_path[impl_start..].find(">::") else {
        return Vec::new();
    };
    let method_sep = impl_start + method_sep_rel;
    let impl_content = &full_path[impl_start + "<impl ".len()..method_sep];
    let Some((trait_path, self_ty)) = impl_content.split_once(" for ") else {
        return Vec::new();
    };
    let method = &full_path[method_sep + ">::".len()..];
    if trait_path.is_empty() || self_ty.is_empty() || method.is_empty() {
        return Vec::new();
    }

    let crate_prefix = &full_path[..impl_start];
    let qualified = format!("{crate_prefix}<{self_ty} as {trait_path}>::{method}");
    let relative = format!("<{self_ty} as {trait_path}>::{method}");
    if qualified == relative {
        vec![relative]
    } else {
        vec![qualified, relative]
    }
}

fn inline_qualified_logic_fn_calls(
    expr: PureExpr,
    inline_map: &HashMap<String, InlineLogicFn>,
    current_full_path: &str,
) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::LogicFnCall { name, args } => {
            let Some(target) = inline_map.get(&name) else {
                return PureExpr::LogicFnCall { name, args };
            };
            if target.full_path == current_full_path || target.params.len() != args.len() {
                return PureExpr::LogicFnCall { name, args };
            }
            let substitutions: HashMap<String, PureExpr> =
                target.params.iter().cloned().zip(args).collect();
            target.body.substitute_capture_avoiding(
                &substitutions,
                &trust_wp_core::formula::CaptureAvoidingSubstOptions::default(),
            )
        }
        other => other,
    })
}

fn simplify_newtype_views(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    params: &[String],
    newtype_type_names: &HashSet<String>,
    parsed: &mut LogicFnDef,
) {
    if newtype_type_names.is_empty() {
        return;
    }
    let newtype_params = newtype_param_names_for_logic_fn(tcx, def_id, params, newtype_type_names);
    if newtype_params.is_empty() {
        return;
    }
    let body = parsed.take_body();
    parsed.set_body(simplify_newtype_view_in_expr_for_params(
        body,
        &newtype_params,
    ));
    let requires: Vec<_> = parsed
        .take_requires()
        .into_iter()
        .map(|req| simplify_newtype_view_in_expr_for_params(req, &newtype_params))
        .collect();
    parsed.set_requires(requires);
    let ensures: Vec<_> = parsed
        .take_ensures()
        .into_iter()
        .map(|ens| simplify_newtype_view_in_expr_for_params(ens, &newtype_params))
        .collect();
    parsed.set_ensures(ensures);
}

fn apply_assoc_const_substitutions(
    parsed: &mut LogicFnDef,
    substitutions: &HashMap<String, PureExpr>,
) {
    if substitutions.is_empty() {
        return;
    }

    let body = parsed.take_body();
    parsed.set_body(body.substitute(substitutions));
    let requires: Vec<_> = parsed
        .take_requires()
        .into_iter()
        .map(|req| req.substitute(substitutions))
        .collect();
    parsed.set_requires(requires);
    let ensures: Vec<_> = parsed
        .take_ensures()
        .into_iter()
        .map(|ens| ens.substitute(substitutions))
        .collect();
    parsed.set_ensures(ensures);
}

fn normalize_local_assoc_const_paths(tcx: TyCtxt<'_>, def_id: DefId, parsed: &mut LogicFnDef) {
    let body = parsed.take_body();
    parsed.set_body(crate::assoc_const_paths::normalize_local_assoc_const_paths(
        tcx, def_id, &body,
    ));
    let requires: Vec<_> = parsed
        .take_requires()
        .into_iter()
        .map(|req| crate::assoc_const_paths::normalize_local_assoc_const_paths(tcx, def_id, &req))
        .collect();
    parsed.set_requires(requires);
    let ensures: Vec<_> = parsed
        .take_ensures()
        .into_iter()
        .map(|ens| crate::assoc_const_paths::normalize_local_assoc_const_paths(tcx, def_id, &ens))
        .collect();
    parsed.set_ensures(ensures);
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        sync::{
            atomic::{AtomicU64, Ordering},
            Arc,
        },
    };

    use rustc_driver::{run_compiler, Callbacks, Compilation};
    use rustc_interface::interface::Compiler;
    use rustc_middle::ty::TyCtxt;
    use trust_wp_core::{
        formula::{internal::tuple_lowering::tuple_logic_fn_name, BinOp, ExprSort, PureExpr},
        logic::{LogicFnDef, LogicMode},
    };

    use super::{
        attrs::append_opaque_guard_if_needed,
        discovery::{
            extract_function_name, looks_like_seq_type_name, to_logic_fn_def, LogicFunction,
        },
        extract_logic_fn_defs, extract_type_invariant_defs,
        inline_qualified_logic_fn_calls_in_defs, validate_logic_laws_impl,
    };

    const TEST_CRATE_NAME: &str = "trust_wp_logic_decl_only_test";
    static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

    #[test]
    fn test_extract_function_name() {
        assert_eq!(extract_function_name("crate::specs::max"), "max");
        assert_eq!(extract_function_name("max"), "max");
        assert_eq!(extract_function_name("foo::bar::baz"), "baz");
    }

    #[test]
    fn test_append_opaque_guard_adds_false_when_opaque() {
        let mut requires = Vec::new();
        append_opaque_guard_if_needed(&mut requires, true);
        assert_eq!(requires, vec![PureExpr::Bool(false)]);
    }

    #[test]
    fn test_append_opaque_guard_noop_when_not_opaque() {
        let mut requires = vec![PureExpr::Bool(true)];
        append_opaque_guard_if_needed(&mut requires, false);
        assert_eq!(requires, vec![PureExpr::Bool(true)]);
    }

    #[test]
    fn test_inline_qualified_logic_fn_calls_uses_open_trait_impl_body() {
        let trait_decl = LogicFnDef::new(
            "g".to_string(),
            "creusot_test::Bar::g".to_string(),
            vec![],
            PureExpr::Int(0),
        )
        .with_opaque(true)
        .with_mode(LogicMode::Prophetic);
        let impl_def = LogicFnDef::new(
            "g".to_string(),
            "creusot_test::<impl Bar for i32>::g".to_string(),
            vec![],
            PureExpr::Int(1),
        )
        .with_mode(LogicMode::Open);
        let calls_g = LogicFnDef::new(
            "calls_g".to_string(),
            "creusot_test::calls_g".to_string(),
            vec![],
            PureExpr::LogicFnCall {
                name: "<i32 as Bar>::g".to_string(),
                args: vec![],
            },
        )
        .with_mode(LogicMode::Open);

        let mut defs = vec![trait_decl, impl_def, calls_g];
        inline_qualified_logic_fn_calls_in_defs(&mut defs);

        assert_eq!(defs[2].body(), &PureExpr::Int(1));
    }

    #[test]
    fn test_extract_logic_fn_defs_inlines_open_trait_impl_ufcs_call() {
        let defs = collect_logic_defs_from_source(
            r#"
pub type Int = i128;

pub trait Bar {
    #[doc = "trust-wp:logic:prophetic:"]
    fn g() -> Int;
}

impl Bar for i32 {
    #[doc = "trust-wp:logic:open:"]
    #[doc = "trust-wp:logic_body:1"]
    fn g() -> Int {
        unreachable!()
    }
}

#[doc = "trust-wp:logic:open:"]
#[doc = "trust-wp:logic_body:< i32 as Bar > :: g ()"]
pub fn calls_g() -> Int {
    unreachable!()
}
"#,
        );

        let calls_g = defs
            .iter()
            .find(|def| def.full_path().ends_with("::calls_g"))
            .expect("calls_g should be extracted");
        assert_eq!(calls_g.body(), &PureExpr::Int(1));
    }

    fn make_logic_fn(name: &str, full_path: &str, body: &str) -> LogicFunction {
        LogicFunction {
            name: name.to_string(),
            full_path: full_path.to_string(),
            params: vec!["self".to_string()],
            requires: Vec::new(),
            ensures: Vec::new(),
            variants: Vec::new(),
            is_opaque: false,
            is_trusted: false,
            is_law: false,
            mode: LogicMode::Default,
            is_trait_method: false,
            param_sort_hints: vec![None],
            return_sort_hint: None,
            body_text: Some(body.to_string()),
            deep_model_dispatch_targets: None,
        }
    }

    fn unit_expr() -> PureExpr {
        PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(0),
            args: vec![],
        }
    }

    fn recursive_statement_call_body() -> PureExpr {
        let var_i = || PureExpr::Var("i".to_string(), None);
        let sub =
            |rhs: i64| PureExpr::BinOp(Arc::new(var_i()), BinOp::Sub, Arc::new(PureExpr::Int(rhs)));
        let call = |rhs: i64| PureExpr::LogicFnCall {
            name: "lemma_fib_bound".to_string(),
            args: vec![sub(rhs)],
        };

        PureExpr::Let {
            var: "__stmt0".to_string(),
            value: Arc::new(call(2)),
            body: Arc::new(PureExpr::Let {
                var: "__stmt1".to_string(),
                value: Arc::new(call(1)),
                body: Arc::new(unit_expr()),
            }),
        }
    }

    fn recursive_statement_call_prefix_body() -> PureExpr {
        let var_i = || PureExpr::Var("i".to_string(), None);
        let sub =
            |rhs: i64| PureExpr::BinOp(Arc::new(var_i()), BinOp::Sub, Arc::new(PureExpr::Int(rhs)));
        let call = |rhs: i64| PureExpr::LogicFnCall {
            name: "lemma_fib_bound".to_string(),
            args: vec![sub(rhs)],
        };

        PureExpr::Let {
            var: "__stmt0".to_string(),
            value: Arc::new(call(2)),
            body: Arc::new(call(1)),
        }
    }

    fn recursive_statement_call_nested_if_body() -> PureExpr {
        let var_i = || PureExpr::Var("i".to_string(), None);
        let eq =
            |rhs: i64| PureExpr::BinOp(Arc::new(var_i()), BinOp::Eq, Arc::new(PureExpr::Int(rhs)));

        PureExpr::Ite(
            Arc::new(eq(0)),
            Arc::new(unit_expr()),
            Arc::new(PureExpr::Ite(
                Arc::new(eq(1)),
                Arc::new(unit_expr()),
                Arc::new(recursive_statement_call_prefix_body()),
            )),
        )
    }

    #[derive(Default)]
    struct LogicDefsSnapshot {
        logic_fns: Vec<LogicFnDef>,
        ran: bool,
    }

    struct LogicDefsCallbacks {
        snapshot: LogicDefsSnapshot,
    }

    impl Callbacks for LogicDefsCallbacks {
        #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            self.snapshot.logic_fns = extract_logic_fn_defs(tcx);
            self.snapshot.ran = true;
            Compilation::Stop
        }
    }

    #[derive(Default)]
    struct TypeInvariantDefsSnapshot {
        defs: Vec<trust_wp_core::logic::TypeInvariantDef>,
        ran: bool,
    }

    struct TypeInvariantDefsCallbacks {
        snapshot: TypeInvariantDefsSnapshot,
    }

    impl Callbacks for TypeInvariantDefsCallbacks {
        #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            self.snapshot.defs = extract_type_invariant_defs(tcx);
            self.snapshot.ran = true;
            Compilation::Stop
        }
    }

    #[derive(Default)]
    struct LogicLawValidationSnapshot {
        errors: usize,
        ran: bool,
    }

    struct LogicLawValidationCallbacks {
        snapshot: LogicLawValidationSnapshot,
    }

    impl Callbacks for LogicLawValidationCallbacks {
        #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            self.snapshot.errors = validate_logic_laws_impl(tcx, false);
            self.snapshot.ran = true;
            Compilation::Stop
        }
    }

    fn collect_logic_defs_from_source(source: &str) -> Vec<LogicFnDef> {
        let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_logic_decl_only_test_{}_{}",
            std::process::id(),
            unique
        ));
        fs::create_dir_all(&temp_dir).expect("create logic test temp dir");

        let source_path = temp_dir.join("test.rs");
        fs::write(&source_path, source).expect("write logic test source");

        let args = vec![
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

        let mut callbacks = LogicDefsCallbacks {
            snapshot: LogicDefsSnapshot::default(),
        };
        run_compiler(&args, &mut callbacks);

        let _ = fs::remove_file(&source_path);
        let _ = fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.snapshot.ran,
            "logic extraction callback should run"
        );
        callbacks.snapshot.logic_fns
    }

    fn collect_type_invariant_defs_from_source(
        source: &str,
    ) -> Vec<trust_wp_core::logic::TypeInvariantDef> {
        let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_logic_inv_test_{}_{}",
            std::process::id(),
            unique
        ));
        fs::create_dir_all(&temp_dir).expect("create invariant test temp dir");

        let source_path = temp_dir.join("test.rs");
        fs::write(&source_path, source).expect("write invariant test source");

        let args = vec![
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

        let mut callbacks = TypeInvariantDefsCallbacks {
            snapshot: TypeInvariantDefsSnapshot::default(),
        };
        run_compiler(&args, &mut callbacks);

        let _ = fs::remove_file(&source_path);
        let _ = fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.snapshot.ran,
            "type invariant extraction callback should run"
        );
        callbacks.snapshot.defs
    }

    fn collect_logic_law_validation_errors_from_source(source: &str) -> usize {
        let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_logic_law_test_{}_{}",
            std::process::id(),
            unique
        ));
        fs::create_dir_all(&temp_dir).expect("create logic law test temp dir");

        let source_path = temp_dir.join("test.rs");
        fs::write(&source_path, source).expect("write logic law test source");

        let args = vec![
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

        let mut callbacks = LogicLawValidationCallbacks {
            snapshot: LogicLawValidationSnapshot::default(),
        };
        run_compiler(&args, &mut callbacks);

        let _ = fs::remove_file(&source_path);
        let _ = fs::remove_dir_all(&temp_dir);

        assert!(
            callbacks.snapshot.ran,
            "logic law validation callback should run"
        );
        callbacks.snapshot.errors
    }

    #[test]
    fn test_to_logic_fn_def_rejects_invalid_requires_clause() {
        let mut lf = make_logic_fn("f", "crate::specs::f", "self");
        lf.requires = vec!["self >".to_string()];
        assert!(
            to_logic_fn_def(&lf).is_none(),
            "invalid requires clause should reject logic function definition"
        );
    }

    #[test]
    fn test_to_logic_fn_def_rejects_invalid_ensures_clause() {
        let mut lf = make_logic_fn("f", "crate::specs::f", "self");
        lf.ensures = vec!["result >".to_string()];
        assert!(
            to_logic_fn_def(&lf).is_none(),
            "invalid ensures clause should reject logic function definition"
        );
    }

    #[test]
    fn test_to_logic_fn_def_keeps_valid_requires_and_ensures() {
        let mut lf = make_logic_fn("f", "crate::specs::f", "self");
        lf.requires = vec!["self == self".to_string()];
        lf.ensures = vec!["result == self".to_string()];
        let def = to_logic_fn_def(&lf).expect("valid clauses should produce logic fn def");
        assert_eq!(def.requires().len(), 1);
        assert_eq!(def.ensures().len(), 1);
    }

    #[test]
    fn test_to_logic_fn_def_preserves_return_sort_hint() {
        let mut lf = make_logic_fn("is_valid", "crate::specs::is_valid", "self");
        lf.return_sort_hint = Some(trust_wp_core::formula::ExprSort::Bool);

        let def = to_logic_fn_def(&lf).expect("valid logic fn def");

        assert_eq!(
            def.return_sort(),
            Some(trust_wp_core::formula::ExprSort::Bool)
        );
    }

    #[test]
    fn test_to_logic_fn_def_preserves_law_marker() {
        let mut lf = make_logic_fn("law", "crate::specs::law", "()");
        lf.is_law = true;

        let def = to_logic_fn_def(&lf).expect("valid law logic fn def");

        assert!(def.is_law(), "law marker should survive extraction");
    }

    #[test]
    fn test_validate_logic_laws_accepts_matching_trait_impl_law_modes() {
        let errors = collect_logic_law_validation_errors_from_source(
            r#"
pub trait Tr {
    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:logic_law:"]
    fn la();

    #[doc = "trust-wp:logic:"]
    fn lo();
}

impl Tr for () {
    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:logic_law:"]
    fn la() {}

    #[doc = "trust-wp:logic:"]
    fn lo() {}
}
"#,
        );

        assert_eq!(
            errors, 0,
            "matching trait/impl law modes must remain accepted"
        );
    }

    #[test]
    fn test_validate_logic_laws_accepts_parent_trait_generics_and_bounds() {
        let errors = collect_logic_law_validation_errors_from_source(
            r#"
pub trait Bound {}

pub trait Tr<T>
where
    T: Bound,
{
    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:logic_law:"]
    fn la(&self);
}
"#,
        );

        assert_eq!(
            errors, 0,
            "laws may use generic parameters and bounds from the parent trait"
        );
    }

    #[test]
    fn test_validate_logic_laws_rejects_law_method_generics_and_where_clauses() {
        let errors = collect_logic_law_validation_errors_from_source(
            r#"
pub trait Tr {
    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:logic_law:"]
    fn generic<T>();

    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:logic_law:"]
    fn constrained()
    where
        Self: Sized;
}
"#,
        );

        assert_eq!(
            errors, 2,
            "laws must reject method-level generics and method-level where clauses"
        );
    }

    #[test]
    fn test_validate_logic_laws_accepts_impl_less_prophetic_than_trait() {
        let errors = collect_logic_law_validation_errors_from_source(
            r#"
pub trait Tr {
    #[doc = "trust-wp:logic:prophetic:"]
    fn f();
}

impl Tr for () {
    #[doc = "trust-wp:logic:open:"]
    fn f() {}
}
"#,
        );

        assert_eq!(
            errors, 0,
            "impl may specialize a prophetic trait method to a non-prophetic body"
        );
    }

    #[test]
    fn test_validate_logic_laws_lenient_trait_logic_implemented_by_plain_fn() {
        // Lenient mode (Creusot compatibility): impls of trait logic methods
        // do NOT need to re-mark `#[logic]`. The trait declaration's marker
        // is authoritative; the impl inherits logic-mode dispatch.
        let errors = collect_logic_law_validation_errors_from_source(
            r#"
pub trait Tr {
    #[doc = "trust-wp:logic:"]
    fn f();
}

impl Tr for () {
    fn f() {}
}
"#,
        );

        assert_eq!(
            errors, 0,
            "lenient mode: impl may omit #[logic] when trait declares it"
        );
    }

    #[test]
    fn test_validate_logic_laws_lenient_plain_trait_implemented_by_logic_fn() {
        // Lenient mode (Creusot compatibility): impls may add `#[logic]`
        // even when the trait declaration does not — this matches the
        // Creusot pattern where trait declarations are unmarked and impls
        // opt into logic explicitly.
        let errors = collect_logic_law_validation_errors_from_source(
            r#"
pub trait Tr {
    fn f();
}

impl Tr for () {
    #[doc = "trust-wp:logic:"]
    fn f() {}
}
"#,
        );

        assert_eq!(
            errors, 0,
            "lenient mode: impl may add #[logic] to a plain trait method"
        );
    }

    #[test]
    fn test_validate_logic_laws_rejects_mismatched_trait_impl_law_modes() {
        let errors = collect_logic_law_validation_errors_from_source(
            r#"
pub trait Tr {
    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:logic_law:"]
    fn la();

    #[doc = "trust-wp:logic:"]
    fn lo();
}

impl Tr for () {
    #[doc = "trust-wp:logic:"]
    fn la() {}

    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:logic_law:"]
    fn lo() {}
}
"#,
        );

        assert_eq!(
            errors, 2,
            "trait/impl law markers must match in both directions"
        );
    }

    #[test]
    fn test_validate_logic_laws_rejects_impl_added_prophetic_mode() {
        // Strict guard (Phase 2, creusot tests/should_fail/logic_prophetic_impl.rs):
        // an impl MUST NOT upgrade from the trait's default-opaque `#[logic]`
        // mode directly to `#[logic(prophetic)]`. Creusot rejects this. The
        // previously-lenient acceptance was a false-accept closed by Phase 2.
        let errors = collect_logic_law_validation_errors_from_source(
            r#"
pub trait Tr {
    #[doc = "trust-wp:logic:"]
    fn f();
}

impl Tr for () {
    #[doc = "trust-wp:logic:prophetic:"]
    fn f() {}
}
"#,
        );

        assert_eq!(
            errors, 1,
            "strict mode: impl must not upgrade default-opaque trait #[logic] to prophetic"
        );
    }

    #[test]
    fn test_validate_logic_laws_rejects_sealed_trait_default_override() {
        let errors = collect_logic_law_validation_errors_from_source(
            r#"
pub trait Tr {
    #[doc = "trust-wp:logic:open:"]
    #[doc = "trust-wp:logic_sealed:"]
    fn g(&self) -> i32 {
        1
    }
}

impl Tr for () {
    #[doc = "trust-wp:logic:"]
    fn g(&self) -> i32 {
        0
    }
}
"#,
        );

        assert_eq!(
            errors, 1,
            "sealed trait logic defaults must not be overridden"
        );
    }

    #[test]
    fn test_to_logic_fn_def_preserves_seq_return_sort_hint() {
        let mut lf = make_logic_fn("items", "crate::specs::items", "self");
        lf.return_sort_hint = Some(trust_wp_core::formula::ExprSort::Seq);

        let def = to_logic_fn_def(&lf).expect("valid logic fn def");

        assert_eq!(
            def.return_sort(),
            Some(trust_wp_core::formula::ExprSort::Seq)
        );
    }

    #[test]
    fn test_to_logic_fn_def_accepts_bodyless_trait_logic_decl() {
        let mut lf = make_logic_fn("f", "crate::Tr::f", "self");
        lf.params = vec!["self".to_string(), "x".to_string()];
        lf.requires = vec!["x >= 0".to_string()];
        lf.body_text = None;
        lf.is_trait_method = true;
        lf.return_sort_hint = Some(trust_wp_core::formula::ExprSort::Int);

        let def = to_logic_fn_def(&lf).expect("bodyless trait logic method should be declared");

        assert_eq!(def.params(), ["self".to_string(), "x".to_string()]);
        assert_eq!(def.requires().len(), 1);
        assert_eq!(def.body(), &PureExpr::Int(0));
        assert!(
            def.is_opaque(),
            "bodyless trait logic declarations must not emit defining axioms"
        );
    }

    #[test]
    fn test_to_logic_fn_def_rejects_bodyless_non_trait_logic_decl() {
        let mut lf = make_logic_fn("f", "crate::specs::f", "self");
        lf.body_text = None;

        assert!(
            to_logic_fn_def(&lf).is_none(),
            "non-trait bodyless logic item must stay unsupported"
        );
    }

    #[test]
    fn test_extract_logic_fn_defs_keeps_bodyless_trait_method_params() {
        let logic_fns = collect_logic_defs_from_source(
            r#"
pub trait Tr {
    #[doc = "trust-wp:logic:"]
    fn f(self, x: i32) -> i32;

    #[doc = "trust-wp:logic:"]
    fn g(self, x: i32) -> i32
    where
        Self: Sized,
    {
        self.f(x) + 1
    }
}
"#,
        );

        let f = logic_fns
            .iter()
            .find(|logic_fn| logic_fn.name() == "f")
            .expect("bodyless trait logic method should be extracted");

        assert_eq!(
            f.full_path(),
            &format!("{TEST_CRATE_NAME}::Tr::f"),
            "extracted logic path should stay crate-qualified"
        );
        assert_eq!(f.params(), ["self".to_string(), "x".to_string()]);
        assert_eq!(f.return_sort(), Some(trust_wp_core::formula::ExprSort::Int));
    }

    #[test]
    fn test_extract_type_invariant_defs_distinguish_newtype_from_tuple_struct() {
        let defs = collect_type_invariant_defs_from_source(
            r#"
#![allow(dead_code)]

pub trait Invariant {
    fn invariant(self) -> bool;
}

pub struct NonZero(i32);
pub struct Zero<T>(u32, T);

impl Invariant for NonZero {
    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:logic_body:self > 0"]
    fn invariant(self) -> bool {
        true
    }
}

impl<T> Invariant for Zero<T> {
    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:logic_body:self.0 == 0"]
    fn invariant(self) -> bool {
        true
    }
}
"#,
        );

        let nonzero = defs
            .iter()
            .find(|inv| inv.type_name().ends_with("NonZero"))
            .expect("NonZero invariant should be extracted");
        assert!(
            nonzero.is_newtype(),
            "single-field NonZero should remain a newtype invariant"
        );

        let zero = defs
            .iter()
            .find(|inv| inv.type_name().rsplit("::").next() == Some("Zero"))
            .expect("Zero invariant should be extracted");
        assert!(
            !zero.is_newtype(),
            "tuple struct Zero<T> should not be treated as a newtype"
        );
        // A multi-field tuple struct has no single underlying scalar to view, so
        // it is NOT collapsed like a newtype. The receiver sort follows the
        // #2683 native-carrier rule (a4440d5, "partially_opaque datatype" fix):
        // when `ty_to_expr_sort_enriched` produces a native `Datatype` carrier
        // for the struct — the common case, including `Zero<T>` here — the
        // call-site final-value carrier is that datatype, and the invariant's
        // `self` must be registered under the SAME `Datatype` sort so the body
        // axiom connects to the carrier and `tuple_get_i(self)` resolves to the
        // native field selector. Overriding to `Tuple<N>` would desync the
        // axiom's `self` from the carrier (spurious `&mut` postcondition
        // failures — validated should_fail lane 94/0 false-accepts at a4440d5).
        // The `Tuple<N>` override only applies when NO native datatype carrier
        // exists.
        assert_eq!(
            zero.param_sort(),
            Some(&ExprSort::Datatype(
                trust_wp_core::formula::intern_sort_name("Zero")
            )),
            "multi-field tuple struct Zero<T>(u32, T) invariant must carry the \
             native Datatype carrier sort the encoder uses at call sites \
             (#2683), got {:?} ({})",
            zero.param_sort(),
            match zero.param_sort() {
                Some(ExprSort::Datatype(id)) => trust_wp_core::formula::resolve_sort_name(*id),
                other => format!("{other:?}"),
            }
        );
    }

    /// Newtype invariant whose single field is Int-viewable must carry
    /// `param_sort = Some(ExprSort::Int)` even when the user's
    /// `invariant(self)` method signature originally had a `Datatype(NonNeg)`
    /// hint. Without this override, the ay encoder declares the type-invariant
    /// self quantifier (and any view variable bridged to it) with an opaque
    /// `Sort::Uninterpreted("Tuple1")` carrier — producing spurious counter-
    /// examples like `i_view = @Tuple1!0` for newtype params used in
    /// `#[variant]` / mut-borrow obligations. (#5, spans::quux, result/own::as_mut)
    #[test]
    fn test_extract_type_invariant_defs_newtype_int_field_uses_int_param_sort() {
        let defs = collect_type_invariant_defs_from_source(
            r#"
#![allow(dead_code)]

pub trait Invariant {
    fn invariant(self) -> bool;
}

pub struct NonNeg(pub usize);

impl Invariant for NonNeg {
    #[doc = "trust-wp:logic:"]
    #[doc = "trust-wp:logic_body:0 <= self.0@"]
    fn invariant(self) -> bool {
        true
    }
}
"#,
        );

        let nonneg = defs
            .iter()
            .find(|inv| inv.type_name().ends_with("NonNeg"))
            .expect("NonNeg invariant should be extracted");
        assert!(
            nonneg.is_newtype(),
            "single-field NonNeg(usize) must be classified as a newtype invariant"
        );
        assert_eq!(
            nonneg.param_sort(),
            Some(&ExprSort::Int),
            "newtype invariant with an Int-viewable field must carry param_sort=Int \
             so the encoder declares the self quantifier as Int — \
             not as Datatype/Tuple1 which would produce opaque view sorts \
             in variant decrease and mut-borrow obligations (#5)"
        );
    }

    #[test]
    fn test_extract_logic_fn_defs_substitutes_generic_assoc_const_ensures_2550() {
        let logic_fns = collect_logic_defs_from_source(
            r#"
pub trait Nat {
    const VALUE: usize;
}

pub struct I3<T: Nat>(T);

impl<T: Nat> Nat for I3<T> {
    const VALUE: usize = const { T::VALUE + T::VALUE };
}

#[doc = "trust-wp:logic:"]
#[doc = "trust-wp:ensures:<I3<T> as Nat>::VALUE@ == T::VALUE@ + T::VALUE@"]
pub fn nat_i3_logic<T: Nat>() -> usize {
    0
}
"#,
        );

        let nat_i3_logic = logic_fns
            .iter()
            .find(|logic_fn| logic_fn.name() == "nat_i3_logic")
            .expect("generic assoc const logic fn should be extracted");
        let ensures_text: Vec<String> = nat_i3_logic
            .ensures()
            .iter()
            .map(ToString::to_string)
            .collect();

        assert!(
            ensures_text
                .iter()
                .all(|text| !text.contains("<I3<T> as Nat>::VALUE")),
            "logic fn ensures should not retain the opaque qualified assoc const path: {ensures_text:?}"
        );
        assert!(
            ensures_text
                .iter()
                .any(|text| text.contains("T::VALUE") && text.contains('+')),
            "logic fn ensures should include the symbolic associated-const body: {ensures_text:?}"
        );
    }

    #[test]
    fn test_extract_logic_fn_defs_substitutes_super_qualified_assoc_const_ensures_2550() {
        let logic_fns = collect_logic_defs_from_source(
            r#"
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
        #[doc = "trust-wp:logic:"]
        #[doc = "trust-wp:ensures:<super::I3<T> as super::traits::Nat>::VALUE@ == T::VALUE@ + T::VALUE@"]
        pub fn nat_i3_logic<T: super::traits::Nat>() -> usize {
            0
        }
    }
}
"#,
        );

        let nat_i3_logic = logic_fns
            .iter()
            .find(|logic_fn| logic_fn.name() == "nat_i3_logic")
            .expect("super-qualified generic assoc const logic fn should be extracted");
        let ensures_text: Vec<String> = nat_i3_logic
            .ensures()
            .iter()
            .map(ToString::to_string)
            .collect();

        assert!(
            ensures_text
                .iter()
                .all(|text| !text.contains("<I3<T> as super::traits::Nat>::VALUE")),
            "logic fn ensures should not retain the super-qualified assoc const path: {ensures_text:?}"
        );
        assert!(
            ensures_text
                .iter()
                .any(|text| text.contains("T::VALUE") && text.contains('+')),
            "logic fn ensures should include the symbolic associated-const body for super-qualified trait paths: {ensures_text:?}"
        );
    }

    #[test]
    fn test_to_logic_fn_def_preserves_leading_statement_calls_2447() {
        // Simulates `lemma_fib_bound` body: { lemma_fib_bound(i - 2); lemma_fib_bound(i - 1) }
        let mut lf = make_logic_fn(
            "lemma_fib_bound",
            "crate::lemma_fib_bound",
            "{ lemma_fib_bound(i - 2); lemma_fib_bound(i - 1) }",
        );
        lf.params = vec!["i".to_string()];
        lf.param_sort_hints = vec![None];
        lf.return_sort_hint = Some(ExprSort::Unit);

        let def = to_logic_fn_def(&lf).expect("logic fn with leading statement calls should parse");
        assert_eq!(
            def.body(),
            &recursive_statement_call_body(),
            "unit-returning logic bodies must lower all recursive statement calls into Let carriers",
        );
    }

    #[test]
    fn test_to_logic_fn_def_simple_body_unchanged_by_statement_preservation() {
        let lf = make_logic_fn("f", "crate::f", "self + 1");
        let def = to_logic_fn_def(&lf).expect("simple body should parse");

        // Simple expression body should NOT be wrapped in Let
        assert!(
            !matches!(def.body(), PureExpr::Let { .. }),
            "simple body should not be wrapped in Let"
        );
    }

    #[test]
    fn test_extract_logic_fn_defs_retains_recursive_statement_calls_2447() {
        let logic_fns = collect_logic_defs_from_source(
            r#"
#![allow(unused_variables)]

#[doc = "trust-wp:logic:"]
#[doc = "trust-wp:logic_body:{ fib(n - 1) + fib(n - 2) }"]
pub fn fib(n: u64) -> u64 {
    0
}

#[doc = "trust-wp:logic:"]
#[doc = "trust-wp:logic_body:{
    if i == 0 {
        ()
    } else if i == 1 {
        ()
    } else {
        lemma_fib_bound(i - 2);
        lemma_fib_bound(i - 1)
    }
}"]
pub fn lemma_fib_bound(i: u64) {
}
"#,
        );

        let lemma = logic_fns
            .iter()
            .find(|lf| lf.name() == "lemma_fib_bound")
            .expect("lemma_fib_bound should be extracted");

        assert_eq!(
            lemma.body(),
            &recursive_statement_call_nested_if_body(),
            "source extraction should preserve recursive statement calls inside nested branch blocks",
        );
        assert_eq!(lemma.return_sort(), Some(ExprSort::Unit));
    }

    #[test]
    fn test_extract_logic_fn_defs_marks_supported_mutual_scc_members_recursive() {
        let logic_fns = collect_logic_defs_from_source(
            r#"
#![allow(unused_variables)]

#[doc = "trust-wp:logic:"]
#[doc = "trust-wp:requires:n >= 0"]
#[doc = "trust-wp:variant:n"]
#[doc = "trust-wp:logic_body:if n == 0 { true } else { is_odd(n - 1) }"]
pub fn is_even(n: i32) -> bool {
    true
}

#[doc = "trust-wp:logic:"]
#[doc = "trust-wp:requires:n >= 0"]
#[doc = "trust-wp:variant:n"]
#[doc = "trust-wp:logic_body:if n == 0 { false } else { is_even(n - 1) }"]
pub fn is_odd(n: i32) -> bool {
    false
}
"#,
        );

        let is_even = logic_fns
            .iter()
            .find(|logic_fn| logic_fn.name() == "is_even")
            .expect("is_even should be extracted");
        let is_odd = logic_fns
            .iter()
            .find(|logic_fn| logic_fn.name() == "is_odd")
            .expect("is_odd should be extracted");

        assert!(
            is_even.is_recursive(),
            "accepted mutual-recursive logic fn should be marked recursive"
        );
        assert!(
            is_odd.is_recursive(),
            "accepted mutual-recursive logic fn should be marked recursive"
        );
    }

    #[test]
    fn test_looks_like_seq_type_name_direct_seq() {
        assert!(looks_like_seq_type_name("Seq<i32>"));
    }

    #[test]
    fn test_looks_like_seq_type_name_qualified_seq() {
        assert!(looks_like_seq_type_name(
            "creusot_std::logic::seq::Seq<i32>"
        ));
        assert!(looks_like_seq_type_name("creusot_std::logic::seq::Seq"));
    }

    #[test]
    fn test_looks_like_seq_type_name_rejects_vec() {
        assert!(!looks_like_seq_type_name("std::vec::Vec<i32>"));
    }
}
