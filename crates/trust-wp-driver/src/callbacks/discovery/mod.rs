// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract detection and discovery.
//!
//! Finds functions with trust-wp contract attributes, discovers extern_spec!
//! entries, resolves trait contracts and inheritance.

mod callable_escape;
pub(crate) mod erasure;
pub(crate) mod source_parsing;
mod trait_contracts;
pub(crate) mod trusted;

#[cfg(test)]
mod tests;

use std::collections::{HashMap, HashSet};

pub(crate) use callable_escape::clear_callable_escape_cache;
pub(in crate::callbacks) use callable_escape::{
    closures_defined_by_body, crate_callable_escapes, CallableEscape, EscapedCallable,
};
pub(super) use erasure::{collect_erasure_pairs, validate_erasure_pair};
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    Node, TraitFn, TraitItemKind,
};
use rustc_middle::ty::TyCtxt;
use source_parsing::{
    collect_loop_contract_attrs, collect_loop_contract_attrs_from_source, extend_unique,
    get_contract_attrs,
};
pub(super) use trait_contracts::{
    apply_trait_contract_inheritance, find_trait_contracts, has_invariant_bearing_signature,
    inherited_param_renames, rename_inherited_params, restate_inherited_clauses,
};
use trust_wp_core::logic::TypeInvariantDef;
use trust_wp_driver::{normalize_extern_spec_path, parse_extern_spec_docs, StdSpec};
use trusted::has_trusted_marker;

use super::{
    super::{
        attr_utils::{
            get_contract_attrs_from_doc, get_contract_attrs_from_proc_macro, has_check_mode,
        },
        contracts::{FunctionContract, TraitOrigin},
    },
    parsing::{only_type_param_invariants, param_invariant_grant},
};

/// Discover all extern_spec! entries in the crate.
///
/// Searches for functions with `trust-wp:extern_spec:target=...` doc markers
/// and extracts their contracts. Returns a map from normalized target path
/// to StdSpec, along with a count of duplicate declarations detected.
///
/// Duplicate local extern_specs (two `extern_spec!` blocks targeting the same
/// function) are reported as errors and skipped. (#2686)
pub(super) fn discover_extern_specs(tcx: TyCtxt<'_>) -> (HashMap<String, StdSpec>, usize) {
    let mut specs = HashMap::new();
    let mut duplicate_count = 0usize;

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();

        // Only consider functions (extern_spec stubs are generated as functions)
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        // Specification type-check helpers (`__trust_wp_spec_tc_*`, emitted for
        // contracts on bodyless trait methods) are not program code.
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local_def_id) {
            continue;
        }

        // Get attributes and extract doc strings
        let attrs = tcx.get_all_attrs(def_id);
        let doc_values: Vec<String> = attrs
            .iter()
            .filter_map(|attr| crate::attr_utils::doc_marker_str(attr).map(|s| s.to_string()))
            .collect();

        // Try to parse as extern_spec entry
        match parse_extern_spec_docs(doc_values.iter().map(|s| s.as_str())) {
            Ok(Some(entry)) => {
                let normalized = normalize_extern_spec_path(&entry.target_path);
                let spec = StdSpec {
                    inv_requires: Vec::new(),
                    capture_inv_requires: Vec::new(),
                    requires: entry.requires,
                    ensures: entry.ensures,
                    param_names: None,
                };
                if specs.contains_key(&normalized) {
                    let fn_name = tcx.def_path_str(def_id);
                    eprintln!(
                        "trust-wp: error: duplicate extern_spec for `{normalized}` \
                         (declared again in `{fn_name}`)"
                    );
                    duplicate_count += 1;
                } else {
                    specs.insert(normalized, spec);
                }
            }
            Ok(None) => {}
            Err(e) => {
                let fn_name = tcx.def_path_str(def_id);
                eprintln!("trust-wp: warning: malformed extern spec on `{fn_name}`: {e}");
            }
        }
    }

    (specs, duplicate_count)
}

/// Find all functions with trust-wp contract attributes.
pub(super) fn find_contract_functions(tcx: TyCtxt<'_>) -> Vec<FunctionContract> {
    let mut contracts = Vec::new();

    // Iterate over all local definitions
    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();

        // Only consider functions, methods, and closures.
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
            continue;
        }
        // Specification type-check helpers (`__trust_wp_spec_tc_*`, emitted for
        // contracts on bodyless trait methods) are not program code.
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local_def_id) {
            continue;
        }

        // Skip bodyless trait method declarations (e.g., `fn foo(&self);` without
        // a default body). These have contracts that should only be processed by
        // `find_trait_contracts` for call-site inheritance — including them here
        // causes ICEs when the verification pipeline tries to access their
        // non-existent MIR bodies. (#2205)
        if let Node::TraitItem(item) = tcx.hir_node_by_def_id(local_def_id) {
            if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Required(_))) {
                continue;
            }
        }

        // Check for contract attributes
        // Support multiple styles (checked in this order):
        // 1. Doc-embedded: #[doc = "trust-wp:requires:..."] (current proc-macro output)
        // 2. Tool attributes: #[trust_wp::spec::requires = "..."] (legacy)
        // 3. Proc macro style: #[requires(...)] (fallback)
        let attrs = tcx.get_all_attrs(def_id);

        // Check for trusted marker (postconditions assumed, body not verified)
        let trusted = has_trusted_marker(tcx, def_id, attrs);
        if trusted && trusted::trusted_code_is_denied_for_item(tcx, def_id, attrs) {
            tcx.dcx()
                .span_err(tcx.def_span(def_id), "used the `#[trusted]` attribute");
            continue;
        }
        // Check for explicit termination marker.
        let terminates = has_check_mode(attrs, "terminates");
        // Check for ghost function marker (#[check(ghost)]).
        let ghost = has_check_mode(attrs, "ghost");
        // Try doc-embedded attributes first (current proc-macro output)
        let mut requires = get_contract_attrs_from_doc(attrs, "requires");
        let mut ensures = get_contract_attrs_from_doc(attrs, "ensures");
        let mut invariants = get_contract_attrs_from_doc(attrs, "invariant");
        let mut variants = get_contract_attrs_from_doc(attrs, "variant");

        // Fall back to legacy tool attributes
        if requires.is_empty() && ensures.is_empty() && invariants.is_empty() && variants.is_empty()
        {
            requires = get_contract_attrs(attrs, &["trust-wp", "spec", "requires"]);
            ensures = get_contract_attrs(attrs, &["trust-wp", "spec", "ensures"]);
            invariants = get_contract_attrs(attrs, &["trust-wp", "spec", "invariant"]);
            variants = get_contract_attrs(attrs, &["trust-wp", "spec", "variant"]);
        }

        // Fall back to proc macro attributes if still not found
        if requires.is_empty() && ensures.is_empty() && invariants.is_empty() && variants.is_empty()
        {
            requires = get_contract_attrs_from_proc_macro(attrs, "requires");
            ensures = get_contract_attrs_from_proc_macro(attrs, "ensures");
            invariants = get_contract_attrs_from_proc_macro(attrs, "invariant");
            variants = get_contract_attrs_from_proc_macro(attrs, "variant");
        }

        // D-177: the function's own clauses name a parameter pattern's bindings
        // as projections of the parameter. Loop invariants and loop variants
        // (merged below) are left alone: in the body those names are locals.
        crate::param_patterns::destructure_contract_clauses(
            tcx,
            local_def_id,
            "requires",
            &mut requires,
        );
        crate::param_patterns::destructure_contract_clauses(
            tcx,
            local_def_id,
            "ensures",
            &mut ensures,
        );
        crate::param_patterns::destructure_contract_clauses(
            tcx,
            local_def_id,
            "variant",
            &mut variants,
        );
        // D-179: a name every call binds to an argument by position, read by
        // a clause that has no parameter of that name, is refused.
        for (clause_kind, clauses) in [
            ("requires", &mut requires),
            ("ensures", &mut ensures),
            ("variant", &mut variants),
        ] {
            crate::param_patterns::refuse_positional_alias_collisions(
                tcx,
                local_def_id,
                clause_kind,
                clauses,
            );
        }
        // D-181: a postcondition reads a `&mut` a tuple or array parameter
        // holds only through `*`, `^` or `@`.
        crate::param_patterns::refuse_unplaced_held_mut_param_reads(
            tcx,
            local_def_id,
            "ensures",
            &mut ensures,
        );
        // D-238: a closure's clauses are read in its caller's body, where a
        // name the function binds more than once is the parameter.
        for (clause_kind, clauses) in [("requires", &mut requires), ("ensures", &mut ensures)] {
            crate::param_patterns::resolve_closure_clause_names(
                tcx,
                local_def_id,
                clause_kind,
                clauses,
            );
        }

        // Loop-level `#[invariant(...)]` / `#[variant(...)]` attributes are attached
        // to HIR loop expressions, not function items. Collect them from the body so
        // Creusot-style statement attributes activate loop verification. (#873)
        let (
            loop_invariants,
            loop_variants,
            per_loop_invariants,
            per_loop_variants,
            all_loop_spans,
        ) = collect_loop_contract_attrs(tcx, local_def_id);
        extend_unique(&mut invariants, loop_invariants);
        extend_unique(&mut variants, loop_variants);
        let (source_invariants, source_variants) =
            collect_loop_contract_attrs_from_source(tcx, def_id);
        extend_unique(&mut invariants, source_invariants);
        extend_unique(&mut variants, source_variants);

        // Resolve trait origin for impl methods using opt_associated_item
        let trait_origin = tcx.opt_associated_item(def_id).and_then(|assoc| {
            // trait_item_def_id is set when this is an impl of a trait method
            assoc.trait_item_def_id().map(|trait_method_id| {
                // The trait DefId is the parent of the trait method
                let trait_def_id = tcx.parent(trait_method_id);
                let method_name = tcx.item_name(trait_method_id).to_string();
                TraitOrigin {
                    trait_def_id,
                    trait_method_name: method_name,
                    inherits_clauses: false,
                }
            })
        });

        // Trait default methods with bodies need verification even without explicit
        // contracts so call-site obligations (e.g., invoking a contracted trait method)
        // are checked (#1203).
        let trait_default_with_body = is_bodyful_trait_method(tcx, local_def_id);

        // Contract-free functions still owe Creusot's machine-int arithmetic
        // goals (program-function preconditions of `add`/`sub`/`mul`/`neg`/
        // `div`/`rem`, inline-const overflow). (int-overflow obligations)
        let arithmetic_panic_sites = !trusted && has_arithmetic_panic_sites(tcx, local_def_id);

        // Include functions with any contract attribute, trusted marker, trait origin,
        // or bodyful trait default method.
        // (trait origin means we may inherit contracts later)
        if !requires.is_empty()
            || !ensures.is_empty()
            || !invariants.is_empty()
            || !variants.is_empty()
            || terminates
            || ghost
            || trusted
            || trait_origin.is_some()
            || trait_default_with_body
            || arithmetic_panic_sites
        {
            contracts.push(FunctionContract {
                local_def_id,
                def_id,
                requires,
                ensures,
                invariants,
                per_loop_invariants,
                per_loop_variants,
                all_loop_spans,
                variants,
                terminates,
                ghost,
                trusted,
                trait_origin,
                capture_owner_only: false,
            });
        }
    }

    contracts
}

/// Whether a HIR body holds a machine-integer operation that can panic of its
/// OWN: a nested closure or coroutine is a body of its own and is not searched.
fn hir_body_has_arithmetic_panic_site(tcx: TyCtxt<'_>, body_id: rustc_hir::BodyId) -> bool {
    use rustc_hir::intravisit::{self, Visitor};

    struct Finder<'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
        found: bool,
    }

    impl<'tcx> Visitor<'tcx> for Finder<'tcx> {
        type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;
        type MaybeTyCtxt = TyCtxt<'tcx>;

        fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
            self.tcx
        }

        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            use rustc_hir::{AssignOpKind, BinOpKind, ExprKind, UnOp};
            if self.found {
                return;
            }
            // Only this body's own expressions have typeck entries here;
            // nested closure bodies share the root's typeck results.
            // `&u8 + u8` / `u8 += &u8` resolve to core's forwarding operator
            // impls, which panic exactly as the primitive operation does.
            let integral = |e: &'tcx rustc_hir::Expr<'tcx>| {
                self.typeck
                    .expr_ty_opt(e)
                    .is_some_and(|ty| ty.peel_refs().is_integral())
            };
            let signed = |e: &'tcx rustc_hir::Expr<'tcx>| {
                self.typeck
                    .expr_ty_opt(e)
                    .is_some_and(|ty| ty.peel_refs().is_signed())
            };
            self.found = match expr.kind {
                ExprKind::Binary(op, lhs, _) => {
                    matches!(
                        op.node,
                        BinOpKind::Add
                            | BinOpKind::Sub
                            | BinOpKind::Mul
                            | BinOpKind::Div
                            | BinOpKind::Rem
                            | BinOpKind::Shl
                            | BinOpKind::Shr
                    ) && integral(lhs)
                }
                ExprKind::AssignOp(op, lhs, _) => {
                    matches!(
                        op.node,
                        AssignOpKind::AddAssign
                            | AssignOpKind::SubAssign
                            | AssignOpKind::MulAssign
                            | AssignOpKind::DivAssign
                            | AssignOpKind::RemAssign
                            | AssignOpKind::ShlAssign
                            | AssignOpKind::ShrAssign
                    ) && integral(lhs)
                }
                // `-1i8` is a negated LITERAL: rustc lowers it to a constant
                // with no `OverflowNeg` assert, so it owes no goal.
                ExprKind::Unary(UnOp::Neg, operand) => {
                    signed(operand) && !matches!(operand.kind, ExprKind::Lit(_))
                }
                ExprKind::ConstBlock(_) => true,
                // A closure body is its own MIR body: its arithmetic panic
                // sites are that body's obligations, not the enclosing fn's.
                ExprKind::Closure(_) => return,
                _ => false,
            };
            if !self.found {
                intravisit::walk_expr(self, expr);
            }
        }
    }

    let body = tcx.hir_body(body_id);
    let typeck = tcx.typeck_body(body_id);
    let mut finder = Finder {
        tcx,
        typeck,
        found: false,
    };
    finder.visit_body(body);
    finder.found
}

/// Whether a bodyful local function (or plain user closure) contains a
/// machine-integer operation that can panic: `+ - * / % << >>` (or their
/// compound-assignment forms) on primitive integers, unary `-` on a signed
/// integer, or an inline `const { .. }` block.
///
/// Spec-only items (anything carrying a `trust-wp:` doc marker: logic,
/// predicate, law, extern-spec shims) and `#[trusted]` items are excluded.
pub(crate) fn has_arithmetic_panic_sites(tcx: TyCtxt<'_>, local_def_id: LocalDefId) -> bool {
    let def_id = local_def_id.to_def_id();
    match tcx.def_kind(def_id) {
        DefKind::Fn | DefKind::AssocFn => {}
        // A closure body is its own MIR body and owes its own arithmetic
        // goals. Only a plain user closure written directly in a program fn:
        // never one produced by a macro expansion (ghost/snapshot/proof_assert
        // machinery), never one inside a spec-marked or trusted item, and
        // never a coroutine body: no lane verifies one, so a coroutine that
        // owes anything is refused through `discover_coroutine_obligation_bodies`
        // instead of being made a target here.
        DefKind::Closure => {
            if tcx.coroutine_kind(def_id).is_some() || tcx.def_span(def_id).from_expansion() {
                return false;
            }
            let root = tcx.typeck_root_def_id(def_id);
            if !matches!(tcx.def_kind(root), DefKind::Fn | DefKind::AssocFn) {
                return false;
            }
            let mut owner = tcx.parent(def_id);
            loop {
                // Program contracts (`requires`/`ensures`/`invariant`/
                // `variant` markers) keep a closure a program closure; any
                // other `trust-wp:` marker (logic, extern_spec, proof_assert,
                // ...) makes the item spec code.
                let owner_attrs = tcx.get_all_attrs(owner);
                if owner_attrs.iter().any(|attr| {
                    crate::attr_utils::doc_marker_str(attr).is_some_and(|value| {
                        value
                            .as_str()
                            .strip_prefix("trust-wp:")
                            .is_some_and(|rest| {
                                !["requires:", "ensures:", "invariant:", "variant:"]
                                    .iter()
                                    .any(|program| rest.starts_with(program))
                            })
                    })
                }) || has_trusted_marker(tcx, owner, owner_attrs)
                {
                    return false;
                }
                if owner == root {
                    break;
                }
                owner = tcx.parent(owner);
            }
        }
        _ => return false,
    }
    // The contract/std shim crates are not user programs: their contract-free
    // runtime hosts (e.g. the `i128`-backed ghost `Int`) are outside the
    // verified surface, exactly as `purity_validation` scopes them out. Their
    // contracted items are still discovered through the ordinary predicate.
    let local_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE);
    if matches!(
        local_crate_name.as_str(),
        "trust_wp_std" | "trust_wp" | "creusot_std" | "creusot_contracts" | "trust_wp_lib"
    ) {
        return false;
    }
    let attrs = tcx.get_all_attrs(def_id);
    if attrs.iter().any(|attr| {
        crate::attr_utils::doc_marker_str(attr)
            .is_some_and(|value| value.as_str().starts_with("trust-wp:"))
    }) {
        return false;
    }
    if has_trusted_marker(tcx, def_id, attrs) {
        return false;
    }
    let Some(body_id) = tcx.hir_node_by_def_id(local_def_id).body_id() else {
        return false;
    };
    hir_body_has_arithmetic_panic_site(tcx, body_id)
}

pub(super) fn is_bodyful_trait_method(tcx: TyCtxt<'_>, local_def_id: LocalDefId) -> bool {
    let def_id = local_def_id.to_def_id();
    tcx.opt_associated_item(def_id).is_some_and(|assoc| {
        matches!(assoc.container, rustc_middle::ty::AssocContainer::Trait)
            && (tcx.defaultness(def_id).has_value()
                || matches!(
                    tcx.hir_node_by_def_id(local_def_id),
                    Node::TraitItem(item)
                        if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Provided(_)))
                )
                || tcx.is_mir_available(def_id))
    })
}

/// Discover functions that should be verified due to type invariant injection,
/// even without explicit `#[requires]`/`#[ensures]` annotations (#359).
///
/// In Creusot, functions with parameters or return types that have
/// `impl Invariant for T` automatically get invariant pre/postconditions.
/// This function finds unannotated functions whose types match defined
/// type invariants and adds them to the contracts list.
pub(super) fn discover_invariant_bearing_functions(
    tcx: TyCtxt<'_>,
    contracts: &mut Vec<FunctionContract>,
    type_invariant_defs: &[TypeInvariantDef],
) {
    if type_invariant_defs.is_empty() {
        return;
    }

    let invariant_type_names: HashSet<&str> =
        type_invariant_defs.iter().map(|d| d.type_name()).collect();

    // Build set of already-discovered functions so we don't add duplicates
    let existing: HashSet<DefId> = contracts.iter().map(|c| c.def_id).collect();

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();

        // Only consider functions and methods (not closures — they get
        // invariant injection via their parent function's contract).
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        // Specification type-check helpers (`__trust_wp_spec_tc_*`, emitted for
        // contracts on bodyless trait methods) are not program code.
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local_def_id) {
            continue;
        }

        // Skip bodyless trait method declarations (#2205). These have no
        // HIR body or usable MIR; the verification pipeline would ICE in
        // `body_owned_by` when trying to access their non-existent bodies.
        if let Node::TraitItem(item) = tcx.hir_node_by_def_id(local_def_id) {
            if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Required(_))) {
                continue;
            }
        }

        // Skip functions already discovered via contract attributes
        if existing.contains(&def_id) {
            continue;
        }

        // Skip logic functions (they are specification-only)
        let attrs = tcx.get_all_attrs(def_id);
        if super::super::logic::has_logic_marker(attrs) {
            continue;
        }

        // Skip trusted functions without contracts (nothing to verify)
        if has_trusted_marker(tcx, def_id, attrs) {
            continue;
        }

        // Check if any parameter or the return type matches a type with a defined invariant
        if has_invariant_bearing_signature(tcx, def_id, &invariant_type_names) {
            contracts.push(FunctionContract {
                local_def_id,
                def_id,
                requires: vec![],
                ensures: vec![],
                invariants: vec![],
                per_loop_invariants: vec![],
                per_loop_variants: vec![],
                all_loop_spans: vec![],
                variants: vec![],
                terminates: false,
                ghost: false,
                trusted: false,
                trait_origin: None,
                capture_owner_only: false,
            });
        }
    }
}

/// Discover functions that contain `proof_assert!` but have no contract annotations.
///
/// When a function like `ghost_only()` uses `proof_assert!` inside a `ghost! { ... }` block
/// but has no `#[requires]`/`#[ensures]` attributes, it will not appear in the contracts
/// list. Without a contract entry, the verification loop in `verify_contracts` never
/// iterates over this function, so its proof_asserts are never checked. (#1581)
///
/// This function scans all MIR body owners for proof_assert closures (identified by the
/// `trust-wp:proof_assert:` doc marker attribute) and creates synthetic empty-contract entries
/// for their containing functions, enabling the per-function proof_assert verification
/// loop to pick them up.
pub(super) fn discover_proof_assert_functions(
    tcx: TyCtxt<'_>,
    contracts: &mut Vec<FunctionContract>,
) {
    use rustc_middle::mir::{Rvalue, StatementKind};

    let existing: HashSet<DefId> = contracts.iter().map(|c| c.def_id).collect();

    // Collect functions that contain proof_asserts. We scan MIR bodies
    // for closure aggregates with the proof_assert doc marker, matching
    // the same detection logic as `find_proof_asserts_in_mir`.
    let mut pa_fns: HashSet<LocalDefId> = HashSet::new();

    for local_def_id in tcx.hir_body_owners() {
        let def_id = local_def_id.to_def_id();

        // Functions, methods and closures. A closure is a function of its
        // own: Creusot proves its assertions in the closure's VC whether or
        // not it carries a contract, so a contract-free closure left out here
        // is a body whose assertions no pass examines
        // (proof_assert_in_contractless_closure_never_examined.rs). A
        // coroutine body is admitted too, so that the pass refuses its
        // assertions by name instead of never meeting them
        // (async_fn_body_assertion_never_examined.rs).
        let def_kind = tcx.def_kind(def_id);
        if !matches!(def_kind, DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
            continue;
        }
        // Creusot trusts a closure whose enclosing item is trusted
        // (`is_trusted_item` walks the parents), so its body is not a goal.
        if def_kind == DefKind::Closure {
            let root = tcx.typeck_root_def_id(def_id);
            if has_trusted_marker(tcx, root, tcx.get_all_attrs(root)) {
                continue;
            }
        }
        // Specification type-check helpers (`__trust_wp_spec_tc_*`, emitted for
        // contracts on bodyless trait methods) are not program code.
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local_def_id) {
            continue;
        }

        // Skip functions already in the contracts list
        if existing.contains(&def_id) {
            continue;
        }

        // Skip logic functions (specification-only)
        let attrs = tcx.get_all_attrs(def_id);
        if super::super::logic::has_logic_marker(attrs) {
            continue;
        }

        // Check MIR body for proof_assert closures
        if !tcx.is_mir_available(def_id) {
            continue;
        }

        // Skip bodyless trait method declarations (#2205). `is_mir_available`
        // returns true for these (rustc generates an unreachable shim), but
        // `mir_borrowck` panics in `body_owned_by` because no HIR body exists.
        if let Node::TraitItem(item) = tcx.hir_node_by_def_id(local_def_id) {
            if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Required(_))) {
                continue;
            }
        }

        // Trigger borrow checking to populate MIR cache.
        // Must use typeck_root_def_id, not the function itself — closures and
        // nested items share their root's borrowck result.
        let root = tcx.typeck_root_def_id(def_id).expect_local();
        let _ = tcx.mir_borrowck(root);

        let Some(body_with_facts) = super::try_get_body_with_context(tcx, local_def_id) else {
            continue;
        };

        // Walk MIR looking for proof_assert closure aggregates
        let body = &body_with_facts.body;

        let has_proof_assert = body.basic_blocks.iter().any(|bb_data| {
            bb_data.statements.iter().any(|stmt| {
                if let StatementKind::Assign((
                    _,
                    Rvalue::Aggregate(
                        rustc_middle::mir::AggregateKind::Closure(closure_def_id, _),
                        _,
                    ),
                )) = &stmt.kind
                {
                    // Check if this closure has the proof_assert doc marker
                    if let Some(local) = closure_def_id.as_local() {
                        let hir_id = tcx.local_def_id_to_hir_id(local);
                        let attrs = tcx.hir_attrs(hir_id);
                        return attrs.iter().any(|attr| {
                            crate::attr_utils::doc_marker_str(attr).is_some_and(|v| {
                                let s = v.as_str();
                                s.starts_with("trust-wp:proof_assert:")
                                    || s.starts_with("trust-wp:trusted_proof_assert:")
                            })
                        });
                    }
                }
                false
            })
        });

        if has_proof_assert {
            pa_fns.insert(local_def_id);
        }
    }

    for local_def_id in pa_fns {
        let def_id = local_def_id.to_def_id();
        contracts.push(FunctionContract {
            local_def_id,
            def_id,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            per_loop_invariants: vec![],
            per_loop_variants: vec![],
            all_loop_spans: vec![],
            variants: vec![],
            terminates: false,
            ghost: false,
            trusted: false,
            trait_origin: None,
            capture_owner_only: false,
        });
    }
}

/// Discover contractless functions that BUILD a closure whose captures hold a
/// type-invariant grant.
///
/// A closure's body is verified holding `inv(capture)`; the code that builds
/// the closure is the hand-over that owes it, exactly as a call site owes a
/// callee's parameter invariants. That obligation is raised during the
/// builder's own MIR extraction, so a builder the verification loop never
/// visits pays nothing and the grant is free again (D-66). NARROW by
/// construction: the predicate is the very vector the construction site will
/// be charged, so nothing enters here that does not owe.
pub(super) fn discover_closure_capture_invariant_owners(
    tcx: TyCtxt<'_>,
    contracts: &mut Vec<FunctionContract>,
    type_invariant_defs: &[TypeInvariantDef],
) {
    use rustc_middle::mir::{Rvalue, StatementKind};

    if type_invariant_defs.is_empty() {
        return;
    }
    let existing: HashSet<DefId> = contracts.iter().map(|c| c.def_id).collect();
    let mut owners: Vec<LocalDefId> = Vec::new();

    for local_def_id in tcx.hir_body_owners() {
        let def_id = local_def_id.to_def_id();

        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local_def_id) {
            continue;
        }
        if existing.contains(&def_id) {
            continue;
        }
        let attrs = tcx.get_all_attrs(def_id);
        if super::super::logic::has_logic_marker(attrs) {
            continue;
        }
        // A trusted body is assumed, not verified: it owes nothing here either.
        if has_trusted_marker(tcx, def_id, attrs) {
            continue;
        }
        if !tcx.is_mir_available(def_id) {
            continue;
        }
        // Bodyless trait method declarations report MIR (an unreachable shim)
        // but have no HIR body, and `body_owned_by` panics on them.
        if let Node::TraitItem(item) = tcx.hir_node_by_def_id(local_def_id) {
            if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Required(_))) {
                continue;
            }
        }
        // Closures and nested items share their typeck root's borrowck result.
        let root = tcx.typeck_root_def_id(def_id).expect_local();
        let _ = tcx.mir_borrowck(root);
        let Some(body_with_facts) = super::try_get_body_with_context(tcx, local_def_id) else {
            continue;
        };

        let builds_granted_closure = body_with_facts.body.basic_blocks.iter().any(|bb_data| {
            bb_data.statements.iter().any(|stmt| {
                let StatementKind::Assign((
                    _,
                    Rvalue::Aggregate(
                        rustc_middle::mir::AggregateKind::Closure(closure_def_id, _),
                        _,
                    ),
                )) = &stmt.kind
                else {
                    return false;
                };
                !crate::callbacks::type_invariants::build_capture_invariants(
                    &crate::callbacks::closure_enrichment::closure_capture_fields(
                        tcx,
                        *closure_def_id,
                    ),
                    type_invariant_defs,
                )
                .is_empty()
            })
        });

        if builds_granted_closure {
            owners.push(local_def_id);
        }
    }

    for local_def_id in owners {
        contracts.push(FunctionContract {
            local_def_id,
            def_id: local_def_id.to_def_id(),
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            per_loop_invariants: vec![],
            per_loop_variants: vec![],
            all_loop_spans: vec![],
            variants: vec![],
            terminates: false,
            ghost: false,
            trusted: false,
            trait_origin: None,
            capture_owner_only: true,
        });
    }
}

/// Fn-trait call methods whose Creusot semantics are the std specs
/// `FN_CALL` / `FN_MUT_CALL_MUT` / `FN_ONCE_CALL_ONCE`: the caller owes
/// `precondition(args)` and receives `postcondition{,_mut,_once}(..)`.
const FN_TRAIT_CALL_PATHS: &[&str] = &[
    "core::ops::Fn::call",
    "std::ops::Fn::call",
    "core::ops::FnMut::call_mut",
    "std::ops::FnMut::call_mut",
    "core::ops::FnOnce::call_once",
    "std::ops::FnOnce::call_once",
];

/// Whether `body` calls `Fn::call` / `FnMut::call_mut` / `FnOnce::call_once`
/// on a receiver whose type, after peeling references, is a generic type
/// parameter (`F: Fn(..)`, `&F`, `&mut F`).
///
/// Such a call carries a Creusot `call requires` goal
/// (`precondition_F self args`, e.g. `closures/03_generic_bound.coma`) even
/// when the enclosing function has no contract, so the function is a
/// verification target. NARROW on purpose: concrete closures and fn items are
/// resolved through their own specs and are not what this predicate is for.
pub(in crate::callbacks) fn body_calls_through_generic_fn_bound(
    tcx: TyCtxt<'_>,
    body: &rustc_middle::mir::Body<'_>,
) -> bool {
    use rustc_middle::{
        mir::{Operand, TerminatorKind},
        ty::TyKind,
    };
    body.basic_blocks.iter().any(|bb_data| {
        let Some(terminator) = bb_data.terminator.as_ref() else {
            return false;
        };
        let TerminatorKind::Call { func, .. } = &terminator.kind else {
            return false;
        };
        let Operand::Constant(deref!(constant)) = func else {
            return false;
        };
        let TyKind::FnDef(callee, generic_args) = constant.const_.ty().kind() else {
            return false;
        };
        if !FN_TRAIT_CALL_PATHS.contains(&tcx.def_path_str(*callee).as_str()) {
            return false;
        }
        generic_args
            .skip_binder()
            .first()
            .and_then(|arg| arg.as_type())
            .is_some_and(|self_ty| matches!(self_ty.peel_refs().kind(), TyKind::Param(_)))
    })
}

/// [`body_calls_through_generic_fn_bound`] for a local function, warming its
/// borrowck MIR first. Returns `false` when no MIR body is available.
pub(in crate::callbacks) fn fn_calls_through_generic_fn_bound(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
) -> bool {
    let def_id = local_def_id.to_def_id();
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return false;
    }
    if !tcx.is_mir_available(def_id) {
        return false;
    }
    if let Node::TraitItem(item) = tcx.hir_node_by_def_id(local_def_id) {
        if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Required(_))) {
            return false;
        }
    }
    let root = tcx.typeck_root_def_id(def_id).expect_local();
    let _ = tcx.mir_borrowck(root);
    super::try_get_body_with_context(tcx, local_def_id).is_some_and(|body_with_facts| {
        body_calls_through_generic_fn_bound(tcx, &body_with_facts.body)
    })
}

/// Whether `def_id` carries a `#[requires]` clause, in any of the three
/// spellings `find_contract_functions` reads (doc-embedded proc-macro output,
/// legacy tool attribute, proc-macro attribute).
fn has_requires_clause(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    has_contract_clause(tcx, def_id, "requires")
}

/// Whether `def_id` carries a `kind` clause (`requires` or `ensures`), in any
/// of the three spellings `find_contract_functions` reads.
fn has_contract_clause(tcx: TyCtxt<'_>, def_id: DefId, kind: &str) -> bool {
    let attrs = tcx.get_all_attrs(def_id);
    !get_contract_attrs_from_doc(attrs, kind).is_empty()
        || !get_contract_attrs(attrs, &["trust-wp", "spec", kind]).is_empty()
        || !get_contract_attrs_from_proc_macro(attrs, kind).is_empty()
}

/// Whether a call of `callee` at `args`, made from the body of `caller`, may
/// owe a parameter type invariant the body it enters was granted (D-141): an
/// obligation the call lane charges only inside a body that is itself a
/// verification target.
///
/// The body is the one the call lane charges: the item the call resolves to,
/// with the grant instantiated at the arguments it is entered at (a
/// type-parameter clause fixed to a type no part of which carries an
/// invariant owes nothing, and one the instantiation cannot state is refused
/// there, which is an obligation too). Where a trait method's implementation
/// is not determined, the declaration and every local implementation of it:
/// the call lane owes the declaration's vector when it covers them all and
/// refuses otherwise, so a grant on any of them makes the call an obligation
/// either way. The grant is read by [`param_invariant_grant`], the vector the
/// spec tables store, with one over-approximation: whether the table keeps an
/// entry for a body whose grant is type-parameter invariants alone depends on
/// its contract clauses, inherited ones included, which are not final here, so
/// a written clause or an impl that may inherit one counts. Over-approximating
/// makes a caller a target; under-approximating credits one no lane examined.
pub(in crate::callbacks) fn call_may_enter_invariant_grant<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    callee: DefId,
    args: rustc_middle::ty::GenericArgs<'tcx>,
    type_invariant_defs: &[TypeInvariantDef],
) -> bool {
    if type_invariant_defs.is_empty() {
        return false;
    }
    if let Some((runs, runs_args)) = instance_that_runs(tcx, callee, args, caller) {
        return runs.is_local() && grant_owed_at(tcx, runs, Some(runs_args), type_invariant_defs);
    }
    let Some(trait_def_id) = tcx.trait_of_assoc(callee) else {
        return callee.is_local() && grant_owed_at(tcx, callee, Some(args), type_invariant_defs);
    };
    if tcx.impl_of_assoc(callee).is_some() {
        return callee.is_local() && grant_owed_at(tcx, callee, Some(args), type_invariant_defs);
    }
    (callee.is_local() && grant_owed_at(tcx, callee, None, type_invariant_defs))
        || tcx
            .all_impls(trait_def_id)
            .filter(|impl_def_id| impl_def_id.is_local())
            .filter_map(|impl_def_id| {
                tcx.impl_item_implementor_ids(impl_def_id)
                    .get(&callee)
                    .copied()
            })
            .any(|item| item.is_local() && grant_owed_at(tcx, item, None, type_invariant_defs))
}

/// The item a call of `callee` at `args` from `caller` runs, and the generic
/// arguments it runs at, when resolution determines them.
fn instance_that_runs<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    args: rustc_middle::ty::GenericArgs<'tcx>,
    caller: DefId,
) -> Option<(DefId, rustc_middle::ty::GenericArgs<'tcx>)> {
    use rustc_middle::ty::{Instance, InstanceKind, TypeVisitableExt, TypingEnv};
    if args.has_escaping_bound_vars() {
        return None;
    }
    let typing_env = TypingEnv::post_analysis(tcx, caller);
    // Resolution normalizes and may reach trait selection on shapes nothing
    // else asks about; a panic there is an undetermined body, not a crash.
    let instance = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let args = tcx
            .try_normalize_erasing_regions(
                typing_env,
                rustc_middle::ty::set_aliases_to_non_rigid(tcx, args),
            )
            .ok()?;
        Instance::try_resolve(tcx, typing_env, callee, args)
            .ok()
            .flatten()
    }))
    .ok()
    .flatten()?;
    let InstanceKind::Item(item) = instance.def else {
        return None;
    };
    Some((item, instance.args))
}

/// Whether `def_id`'s grant, stated at `args` when they are known, owes
/// anything or cannot be stated.
fn grant_owed_at<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: Option<rustc_middle::ty::GenericArgs<'tcx>>,
    type_invariant_defs: &[TypeInvariantDef],
) -> bool {
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return false;
    }
    let grant = param_invariant_grant(tcx, def_id, type_invariant_defs);
    if grant.is_empty() {
        return false;
    }
    // A grant of type-parameter invariants alone earns an entry only beside a
    // contract clause, written or inherited from the trait method an impl
    // implements (`build_user_spec_table`, `build_trait_spec_table`).
    if only_type_param_invariants(&grant)
        && !has_contract_clause(tcx, def_id, "requires")
        && !has_contract_clause(tcx, def_id, "ensures")
        && tcx.impl_of_assoc(def_id).is_none()
    {
        return false;
    }
    let Some(args) = args else {
        return true;
    };
    crate::callbacks::instantiate_type_param_invariants(tcx, &grant, args)
        .is_none_or(|owed| !owed.is_empty())
}

/// Normalized target paths of the crate's own `extern_spec!` declarations that
/// carry a `requires`.
///
/// A quiet re-read of the same doc markers `discover_extern_specs` parses:
/// that pass reports duplicate and malformed declarations, and running it a
/// second time would print each of those lines twice. Here the parse only
/// decides whether a body is worth walking, so a declaration this cannot read
/// is simply not a reason to walk it.
fn local_extern_spec_requires_targets(tcx: TyCtxt<'_>) -> HashSet<String> {
    let mut targets = HashSet::new();
    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let doc_values: Vec<String> = tcx
            .get_all_attrs(def_id)
            .iter()
            .filter_map(|attr| crate::attr_utils::doc_marker_str(attr).map(|s| s.to_string()))
            .collect();
        if let Ok(Some(entry)) = parse_extern_spec_docs(doc_values.iter().map(String::as_str)) {
            if !entry.requires.is_empty() {
                targets.insert(normalize_extern_spec_path(&entry.target_path));
            }
        }
    }
    targets
}

/// Whether a block reachable from the entry along normal (non-unwind) edges
/// calls a callee that may carry a precondition: a LOCAL callee carrying
/// `#[requires]`, a foreign callee described by a builtin std spec or by one of
/// the crate's own `extern_spec!` declarations, or a callee this pass cannot
/// name at all.
///
/// Creusot states that callee's precondition as a `callee requires` goal at
/// the call site, and trust-wp's call lanes emit it — but only inside a body
/// that is itself a verification target, which is exactly what a contract-free
/// caller is not (D-25).
fn body_calls_requires_bearing_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    type_invariant_defs: &[TypeInvariantDef],
) -> bool {
    use rustc_middle::mir::{TerminatorKind, START_BLOCK};
    let mut extern_targets: Option<HashSet<String>> = None;
    let mut visited = HashSet::new();
    let mut worklist = vec![START_BLOCK];
    while let Some(bb) = worklist.pop() {
        if !visited.insert(bb) {
            continue;
        }
        let data = &body.basic_blocks[bb];
        if data.is_cleanup {
            continue;
        }
        let terminator = data.terminator();
        if let TerminatorKind::Call { func, .. } = &terminator.kind {
            // The callee identity is read off the operand rather than through
            // call resolution: this pass only decides whether to make the
            // CALLER a target, and an over-approximation costs a walk, not a
            // credit. A callee resolution that disagrees is the call lane's
            // own decision, taken in the call lane's own environment.
            let Some((callee, args)) = func.const_fn_def() else {
                // An operand that names no `FnDef` — a reified `fn` pointer, a
                // call through any other value — hides the callee from THIS
                // pass, not from the call lane, which charges whatever
                // precondition it resolves through the same pointer. Reading
                // the silence as "no precondition owed here" is an
                // UNDER-approximation, and that costs a credit: it is the
                // whole of contract_free_fnptr_requires_uncharged.rs. An
                // unnamed callee is therefore a reason to WALK the body.
                return true;
            };
            // A parameter invariant the body it enters was granted is a
            // precondition like a written one: the call lane charges it at
            // this call, and only a verification target has a call lane.
            if call_may_enter_invariant_grant(
                tcx,
                body.source.def_id(),
                callee,
                args,
                type_invariant_defs,
            ) {
                return true;
            }
            if callee.is_local() {
                if has_requires_clause(tcx, callee) {
                    return true;
                }
            } else {
                let path = tcx.def_path_str(callee);
                if trust_wp_driver::lookup_spec_with_extern(None, &path)
                    .is_some_and(|spec| !spec.requires.is_empty())
                {
                    return true;
                }
                let targets =
                    extern_targets.get_or_insert_with(|| local_extern_spec_requires_targets(tcx));
                if targets.contains(&normalize_extern_spec_path(&path)) {
                    return true;
                }
            }
        }
        for successor in terminator.successors() {
            if !body.basic_blocks[successor].is_cleanup {
                worklist.push(successor);
            }
        }
    }
    false
}

/// Whether a local function owes a goal Creusot states at a site trust-wp's
/// extraction lanes already charge: an abort obligation
/// ([`crate::mir_analysis::body_reaches_diverging_call`]), a callee
/// precondition ([`body_calls_requires_bearing_callee`]) or a runtime check
/// ([`crate::mir_analysis::body_reaches_runtime_check`]: an index bounds
/// check, whose failing edge panics exactly as an `assert!` arm does).
///
/// Read by BOTH the discovery pass that makes such a function a verification
/// target and the extraction gate that decides whether a clause-free contract
/// is worth extracting. One predicate, because a body admitted by one and
/// refused by the other is a target of nothing — the shape this closes.
pub(in crate::callbacks) fn fn_owes_abort_or_callee_precondition(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
    type_invariant_defs: &[TypeInvariantDef],
) -> bool {
    let def_id = local_def_id.to_def_id();
    // A closure is a target only when it ESCAPES. Creusot gives a
    // contract-free closure no goal of its own: `coma:extspec` makes its body
    // its specification, so its aborts, callee preconditions and runtime
    // checks are its PRECONDITION, owed by each caller through
    // `precondition(args)`, which trust-wp charges at a direct call and at a
    // generic hop (D-54); verifying such a closure under `requires true`
    // refuses programs the oracle accepts
    // (contract_free_closure_call_uncharged_control). A closure handed to a
    // callee trust-wp does not verify has no such caller: the library calls
    // it with whatever it holds, so its body is verified under `requires
    // true` and the host rests on that verdict (D-118).
    if matches!(tcx.def_kind(def_id), DefKind::Closure) {
        return callable_escape::closure_escapes_to_unverified_code(
            tcx,
            local_def_id,
            type_invariant_defs,
        ) && body_owes_abort_or_callee_precondition(tcx, local_def_id, type_invariant_defs);
    }
    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
        return false;
    }
    if !tcx.is_mir_available(def_id) {
        return false;
    }
    if let Node::TraitItem(item) = tcx.hir_node_by_def_id(local_def_id) {
        if matches!(item.kind, TraitItemKind::Fn(_, TraitFn::Required(_))) {
            return false;
        }
    }
    body_owes_abort_or_callee_precondition(tcx, local_def_id, type_invariant_defs)
}

/// The body arm of [`fn_owes_abort_or_callee_precondition`], shared by
/// functions and escaping closures.
///
/// The runtime-check arm is read here and not only through
/// `has_arithmetic_panic_sites`: that predicate excludes every item carrying a
/// `trust-wp:` marker, and a clause-free `#[check(terminates)]` body is such
/// an item, discovered by its marker and then refused by the extraction gate
/// while its overflow or bounds check went unexamined.
fn body_owes_abort_or_callee_precondition(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
    type_invariant_defs: &[TypeInvariantDef],
) -> bool {
    let def_id = local_def_id.to_def_id();
    if !tcx.is_mir_available(def_id) {
        return false;
    }
    let root = tcx.typeck_root_def_id(def_id).expect_local();
    let _ = tcx.mir_borrowck(root);
    super::try_get_body_with_context(tcx, local_def_id).is_some_and(|body_with_facts| {
        crate::mir_analysis::body_reaches_diverging_call(tcx, &body_with_facts.body)
            || body_calls_requires_bearing_callee(tcx, &body_with_facts.body, type_invariant_defs)
            || crate::mir_analysis::body_reaches_runtime_check(&body_with_facts.body)
    })
}

/// Discover contract-free functions that owe an abort obligation, a callee
/// precondition or a runtime check.
///
/// Creusot emits `Terminator::Abort` (`<bb> = {false} any`, the goal kind
/// `unreachable`) for every diverging call, a `callee requires` goal at
/// every call to a contracted callee, and an `index in bounds` goal at every
/// built-in index. Without this pass such a function is a
/// verification target of NOTHING: its obligations are stated in no run, and a
/// crate whose other items verify exits 0 with
/// `fn boom(a: u32) { assert!(a == 1) }` and `fn hop() { needs_nonzero(0) }`
/// sitting in it unexamined. Adding a target only ADDS obligations; a
/// clause-free `Verified` stays capped by `cap_clause_free_verdict`, so this
/// can move a verdict towards a refutation or a refusal, never away from one.
pub(super) fn discover_abort_obligation_functions(
    tcx: TyCtxt<'_>,
    contracts: &mut Vec<FunctionContract>,
    type_invariant_defs: &[TypeInvariantDef],
) {
    let existing: HashSet<DefId> = contracts.iter().map(|c| c.def_id).collect();
    let mut found: Vec<LocalDefId> = Vec::new();

    for local_def_id in tcx.hir_body_owners() {
        let def_id = local_def_id.to_def_id();
        // A closure is admitted only when it escapes (D-118); the predicate
        // below says which.
        if !matches!(
            tcx.def_kind(def_id),
            DefKind::Fn | DefKind::AssocFn | DefKind::Closure
        ) {
            continue;
        }
        // Specification type-check helpers (`__trust_wp_spec_tc_*`, emitted for
        // contracts on bodyless trait methods) are not program code.
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local_def_id) {
            continue;
        }
        if existing.contains(&def_id) {
            continue;
        }
        let attrs = tcx.get_all_attrs(def_id);
        if super::super::logic::has_logic_marker(attrs) || has_trusted_marker(tcx, def_id, attrs) {
            continue;
        }
        if fn_owes_abort_or_callee_precondition(tcx, local_def_id, type_invariant_defs) {
            found.push(local_def_id);
        }
    }

    for local_def_id in found {
        contracts.push(FunctionContract {
            local_def_id,
            def_id: local_def_id.to_def_id(),
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            per_loop_invariants: vec![],
            per_loop_variants: vec![],
            all_loop_spans: vec![],
            variants: vec![],
            terminates: false,
            ghost: false,
            trusted: false,
            trait_origin: None,
            capture_owner_only: false,
        });
    }
}

/// Whether a body [`is_coroutine_body`] reports — a coroutine, or an `async fn`
/// item or async closure that only builds one — owes anything at all.
///
/// The test is the complement of a short list, not a list of obligations, so
/// a site no lane charges still counts. A body owes unless every terminator
/// outside its cleanup blocks is control flow, a drop or a proved-dead edge,
/// no statement builds a spec closure (`proof_assert!`, ghost and snapshot
/// machinery), no HIR expression is an arithmetic panic site (MIR built
/// without overflow checks carries no overflow `Assert`), and no local or
/// capture has a type invariant. A body whose MIR cannot be read owes.
///
/// [`is_coroutine_body`]: crate::callbacks::verification::skip_decision::is_coroutine_body
fn coroutine_body_owes_obligation(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
    invariant_type_names: &HashSet<&str>,
) -> bool {
    use rustc_middle::mir::{AggregateKind, Rvalue, StatementKind, TerminatorKind};

    if tcx
        .hir_node_by_def_id(local_def_id)
        .body_id()
        .is_some_and(|body_id| hir_body_has_arithmetic_panic_site(tcx, body_id))
    {
        return true;
    }
    let root = tcx
        .typeck_root_def_id(local_def_id.to_def_id())
        .expect_local();
    let _ = tcx.mir_borrowck(root);
    let Some(body_with_facts) = super::try_get_body_with_context(tcx, local_def_id) else {
        return true;
    };
    let body = &body_with_facts.body;
    let spec_closure = |closure: DefId| {
        closure.as_local().is_some_and(|local| {
            tcx.hir_attrs(tcx.local_def_id_to_hir_id(local))
                .iter()
                .any(|attr| {
                    crate::attr_utils::doc_marker_str(attr)
                        .is_some_and(|value| value.as_str().starts_with("trust-wp:"))
                })
        })
    };
    let owes_in_blocks = body
        .basic_blocks
        .iter()
        .filter(|bb| !bb.is_cleanup)
        .any(|bb| {
            // `Unreachable` is an edge rustc's exhaustiveness check proved dead
            // and owes nothing, by the rule `body_reaches_diverging_call` states;
            // `CoroutineDrop` is the exit a body suspended at a `drop` edge takes
            // when the coroutine is dropped, not code the user wrote. A `Drop`
            // owes nothing here, as at a contract-free program fn's drop site: a
            // local destructor's body is a verification target of its own
            // (async_block_drop_panicking_destructor.rs). A `Yield` owes: no lane
            // models what runs after a suspension.
            let terminator_owes = !matches!(
                bb.terminator().kind,
                TerminatorKind::Goto { .. }
                    | TerminatorKind::SwitchInt { .. }
                    | TerminatorKind::Return
                    | TerminatorKind::Unreachable
                    | TerminatorKind::Drop { .. }
                    | TerminatorKind::CoroutineDrop
                    | TerminatorKind::FalseEdge { .. }
                    | TerminatorKind::FalseUnwind { .. }
            );
            terminator_owes
                || bb.statements.iter().any(|stmt| {
                    matches!(
                        &stmt.kind,
                        StatementKind::Assign((
                            _,
                            Rvalue::Aggregate(AggregateKind::Closure(closure, _), _),
                        )) if spec_closure(*closure)
                    )
                })
        });
    owes_in_blocks
        || body
            .local_decls
            .iter()
            .any(|decl| trait_contracts::type_has_invariant(tcx, decl.ty, invariant_type_names))
        || (tcx.def_kind(local_def_id) == DefKind::Closure
            && tcx.closure_captures(local_def_id).iter().any(|capture| {
                trait_contracts::type_has_invariant(tcx, capture.place.ty(), invariant_type_names)
            }))
}

/// Discover every coroutine body that owes an obligation, so that the contract
/// loop REFUSES it (`SkipDecision::CoroutineBody`) instead of no pass meeting
/// it.
///
/// Creusot does not verify a coroutine: its MIR translation rejects the
/// coroutine aggregate a builder holds and treats `Yield` as unreachable, so
/// refusing is the matching verdict, and it is the only one no credit can
/// rest on. Without this pass the refusal met only a body another pass had
/// already admitted — a contracted `async fn` item, or a coroutine holding a
/// `proof_assert!` — and a contract-free `async fn`, an `async` block or an
/// async closure whose only obligation was an overflow, an index, a panic or
/// a callee's `requires` was examined by nothing while the crate exited 0
/// (async_block_overflow_never_examined.rs). Candidates are chosen by the very
/// predicate the contract loop refuses on, so every body admitted here is
/// refused there. A coroutine inside a trusted item is skipped, as Creusot's
/// `is_trusted_item` skips every body under a trusted item.
pub(super) fn discover_coroutine_obligation_bodies(
    tcx: TyCtxt<'_>,
    contracts: &mut Vec<FunctionContract>,
    type_invariant_defs: &[TypeInvariantDef],
) {
    let existing: HashSet<DefId> = contracts.iter().map(|c| c.def_id).collect();
    let invariant_type_names: HashSet<&str> =
        type_invariant_defs.iter().map(|d| d.type_name()).collect();
    let mut found: Vec<LocalDefId> = Vec::new();

    for local_def_id in tcx.hir_body_owners() {
        let def_id = local_def_id.to_def_id();
        if existing.contains(&def_id)
            || !crate::callbacks::verification::skip_decision::is_coroutine_body(tcx, def_id)
        {
            continue;
        }
        let root = tcx.typeck_root_def_id(def_id);
        let mut owner = def_id;
        let under_trusted_item = loop {
            if has_trusted_marker(tcx, owner, tcx.get_all_attrs(owner)) {
                break true;
            }
            if owner == root {
                break false;
            }
            owner = tcx.parent(owner);
        };
        if under_trusted_item {
            continue;
        }
        if coroutine_body_owes_obligation(tcx, local_def_id, &invariant_type_names) {
            found.push(local_def_id);
        }
    }

    for local_def_id in found {
        contracts.push(FunctionContract {
            local_def_id,
            def_id: local_def_id.to_def_id(),
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            per_loop_invariants: vec![],
            per_loop_variants: vec![],
            all_loop_spans: vec![],
            variants: vec![],
            terminates: false,
            ghost: false,
            trusted: false,
            trait_origin: None,
            capture_owner_only: false,
        });
    }
}

/// Discover contractless functions that call through a generic `Fn`/`FnMut`/
/// `FnOnce` bound.
///
/// Creusot emits a `call requires` goal `precondition_F f args` for every such
/// call (and makes `postcondition_F f args result` available after it). Without
/// this pass a function like `fn closure_param<F: Fn(u32)>(f: F) { f(0) }` is
/// never a verification target, its goal is silently dropped, and the run
/// reports all-zero telemetry. Adding a target only ADDS obligations.
pub(super) fn discover_generic_fn_bound_call_functions(
    tcx: TyCtxt<'_>,
    contracts: &mut Vec<FunctionContract>,
) {
    let existing: HashSet<DefId> = contracts.iter().map(|c| c.def_id).collect();
    let mut found: Vec<LocalDefId> = Vec::new();

    for local_def_id in tcx.hir_body_owners() {
        let def_id = local_def_id.to_def_id();
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        // Specification type-check helpers (`__trust_wp_spec_tc_*`, emitted for
        // contracts on bodyless trait methods) are not program code.
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local_def_id) {
            continue;
        }
        if existing.contains(&def_id) {
            continue;
        }
        let attrs = tcx.get_all_attrs(def_id);
        if super::super::logic::has_logic_marker(attrs) || has_trusted_marker(tcx, def_id, attrs) {
            continue;
        }
        if fn_calls_through_generic_fn_bound(tcx, local_def_id) {
            found.push(local_def_id);
        }
    }

    for local_def_id in found {
        contracts.push(FunctionContract {
            local_def_id,
            def_id: local_def_id.to_def_id(),
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            per_loop_invariants: vec![],
            per_loop_variants: vec![],
            all_loop_spans: vec![],
            variants: vec![],
            terminates: false,
            ghost: false,
            trusted: false,
            trait_origin: None,
            capture_owner_only: false,
        });
    }
}
