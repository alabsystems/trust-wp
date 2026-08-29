// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! THIR-level `#[erasure(target)]` equivalence scaffold (Phase 5c).
//!
//! # Background
//!
//! Creusot lets a function be annotated with `#[erasure(target)]` to assert
//! that, after stripping ghost/snapshot/proof code and applying A-normal form,
//! the annotated (spec-enriched) body is equivalent to the runtime `target`
//! body. Creusot enforces this semantically via a dedicated THIR-level pass
//! (`reference/creusot/creusot/src/validate/erasure.rs`).
//!
//! trust-wp accepts the `#[erasure(target)]` attribute today via the proc macro
//! in [`crates/trust-wp-macros/src/marker_attrs.rs`], which emits a doc marker
//! `#[doc = "trust-wp:erasure:<target>"]`. The driver already runs a partial
//! HIR-level equivalence pass in
//! [`crate::ghost::erasure::validate_erasure_attributes`]; that pass handles
//! direct-return shapes, simple calls, and binary expressions. This module is
//! a complementary **driver-side discovery + structural pre-check** that runs
//! after the contract discovery phase and is wired into the structured result
//! protocol via the new `erasure_errors` counter.
//!
//! # What this module checks (Phase 5c STUB)
//!
//! For every local function `lhs` whose `#[erasure(target)]` doc marker is
//! present, we:
//!
//! 1. Parse the target string from the `trust-wp:erasure:` doc marker.
//! 2. Skip wildcard targets (`_`) — Creusot uses these to opt out of the
//!    equivalence check.
//! 3. Resolve the target to a local `DefId` (by suffix-matching on the
//!    function name; full path resolution is deferred — see below).
//! 4. Validate the pair via [`validate_erasure_pair`], which performs a
//!    minimal sanity check:
//!    - Both `lhs` and `rhs` must be functions/assoc-fns with HIR bodies.
//!    - The `rhs` (target) body must be non-empty (i.e. not just `unit` or
//!      a single `()` expression — which would mean the runtime counterpart
//!      has nothing to be equivalent to).
//!
//! # What is deferred (vs. full Creusot semantics)
//!
//! - **THIR-level structural equivalence after ghost stripping.** Creusot
//!   walks both THIR bodies, strips `ghost!`/`snapshot!`/`proof_assert!`
//!   constructs, normalizes to A-normal form, and compares operator-by-operator.
//!   This module does not yet replicate that walk.
//! - **A-normal form rewriting.** Creusot's check is invariant under common
//!   ANF rewrites (let-binding intermediates, reborrows, autoref). We do not
//!   yet perform any rewriting.
//! - **Cross-crate target resolution.** Creusot resolves `#[erasure(target)]`
//!   paths through the full module + trait-method resolver. This module only
//!   resolves targets that live in the same crate as the `lhs`.
//! - **Generic-argument matching.** Creusot rejects erasure pairs whose
//!   generic substitutions are not compatible. This module ignores generics
//!   when matching `lhs`/`rhs`.
//! - **Ghost-field projection equivalence.** Tuples like `(x, ghost!(x))`
//!   require projecting away the ghost field before comparison. Deferred.
//! - **Trait-method targets.** Targets like `<i32 as Quux>::quux` are
//!   accepted but only matched on the trailing method name today; the trait
//!   constraint is not enforced.
//!
//! The HIR-level pass at [`crate::ghost::erasure::validate_erasure_attributes`]
//! continues to catch the simple structural mismatches it already covered.
//! The Phase 5c scaffold's role is to ensure the attribute is plumbed end-to-end
//! through discovery → wire protocol so that future work can replace the stub
//! check with a real THIR walk without re-plumbing the result protocol.
//!
//! # Design Reference
//!
//! - Creusot upstream pass: `reference/creusot/creusot/src/validate/erasure.rs`
//! - Creusot test fixture: `reference/creusot/tests/should_succeed/specification/erasure.rs`
//! - Proc macro: `crates/trust-wp-macros/src/marker_attrs.rs::process_erasure`
//! - Existing HIR-level partial check: `crates/trust-wp-driver/src/ghost/erasure.rs`

use std::collections::HashMap;

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::ty::TyCtxt;

use crate::attr_utils::get_erasure_targets;

/// One discovered `#[erasure(lhs → rhs)]` pair.
///
/// `lhs` is the spec-enriched function carrying the attribute; `rhs` is the
/// runtime target the attribute points at. `target_text` is the raw target
/// string parsed from the doc marker (useful for diagnostics).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ErasurePair {
    pub(crate) lhs: DefId,
    pub(crate) rhs: DefId,
    pub(crate) target_text: String,
}

/// Find every local function with a `trust-wp:erasure:<target>` doc marker and
/// resolve the (lhs, rhs) DefId pair.
///
/// Wildcard targets (`_`) are skipped — Creusot uses these to opt out of the
/// equivalence check, so we accept them silently.
///
/// Returns an empty vector for std-shim crates (`trust-wp`, `trust_wp_std`,
/// `creusot_contracts`, `creusot_std`, `trust_wp_lib`) to avoid spurious
/// errors when those crates are compiled with the driver attached.
pub(crate) fn collect_erasure_pairs(tcx: TyCtxt<'_>) -> Vec<ErasurePair> {
    let local_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
    if matches!(
        local_crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts" | "trust_wp_lib"
    ) {
        return Vec::new();
    }

    let local_fns_by_name = collect_local_functions_by_name(tcx);
    let mut pairs = Vec::new();

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let attrs = tcx.get_all_attrs(def_id);
        let targets = get_erasure_targets(attrs);
        if targets.is_empty() {
            continue;
        }

        for target_text in targets {
            // Wildcard target: explicit opt-out of equivalence checking (Creusot parity).
            if target_text.trim() == "_" {
                continue;
            }

            // Skip unresolvable targets silently here: the existing HIR-level pass
            // (`ghost::erasure::validate_erasure_attributes`) already reports
            // unresolved targets as user-facing diagnostics. Recording an error
            // here too would double-count it in `erasure_errors`.
            let Some(target_local) = resolve_local_target(tcx, &local_fns_by_name, &target_text)
            else {
                continue;
            };

            pairs.push(ErasurePair {
                lhs: def_id,
                rhs: target_local.to_def_id(),
                target_text,
            });
        }
    }

    pairs
}

/// Validate one `(lhs, rhs)` erasure pair.
///
/// This is the Phase 5c STUB. It performs the structural pre-conditions that
/// any future full THIR-equivalence check will also need, without yet doing
/// the actual body comparison. See the module-level docs for the full
/// "what is checked vs deferred" matrix.
///
/// Returns `Ok(())` if the pair passes the stub checks, `Err(reason)`
/// otherwise. Callers should record one [`erasure_errors`] increment per
/// `Err` they observe, via
/// [`crate::result_protocol_state::record_erasure_error`].
///
/// [`erasure_errors`]: trust_wp_core::result_protocol::StructuredVerificationResult::erasure_errors
pub(crate) fn validate_erasure_pair(tcx: TyCtxt<'_>, lhs: DefId, rhs: DefId) -> Result<(), String> {
    // Both sides must be functions/assoc-fns.
    let lhs_kind = tcx.def_kind(lhs);
    if !matches!(lhs_kind, DefKind::Fn | DefKind::AssocFn) {
        return Err(format!(
            "#[erasure] lhs `{}` is not a function (def_kind = {:?})",
            tcx.def_path_str(lhs),
            lhs_kind
        ));
    }
    let rhs_kind = tcx.def_kind(rhs);
    if !matches!(rhs_kind, DefKind::Fn | DefKind::AssocFn) {
        return Err(format!(
            "#[erasure] target `{}` is not a function (def_kind = {:?})",
            tcx.def_path_str(rhs),
            rhs_kind
        ));
    }

    // Both sides must have HIR bodies.
    let Some(lhs_local) = lhs.as_local() else {
        // Cross-crate lhs is impossible (we only collect local pairs).
        return Err(format!(
            "#[erasure] lhs `{}` must be a local function",
            tcx.def_path_str(lhs)
        ));
    };
    let Some(rhs_local) = rhs.as_local() else {
        return Err(format!(
            "#[erasure] target `{}` must be a local function (cross-crate targets are deferred)",
            tcx.def_path_str(rhs)
        ));
    };

    let lhs_body_id = tcx.hir_node_by_def_id(lhs_local).body_id();
    if lhs_body_id.is_none() {
        return Err(format!(
            "#[erasure] lhs `{}` has no body",
            tcx.def_path_str(lhs)
        ));
    }
    let Some(rhs_body_id) = tcx.hir_node_by_def_id(rhs_local).body_id() else {
        return Err(format!(
            "#[erasure] target `{}` has no body",
            tcx.def_path_str(rhs)
        ));
    };

    // Note: a previous Phase 5c stub rejected targets with empty bodies.
    // That was too aggressive — Creusot accepts e.g. `pub fn ghost_split() {}`
    // as a valid target whose erasure is `()`, paired with a subject whose
    // body strips entirely to `()` after ghost projection (see
    // `tests/should_succeed/specification/erasure.rs::ghost_split` /
    // `ghost_split2`). We defer to the HIR-level structural check in
    // `crate::ghost::erasure::validate_erasure_attributes` for the actual
    // equivalence verdict.
    let _ = rhs_body_id;

    Ok(())
}

/// Build a `function_name -> [LocalDefId]` index for same-crate erasure target lookup.
fn collect_local_functions_by_name(tcx: TyCtxt<'_>) -> HashMap<String, Vec<LocalDefId>> {
    let mut by_name: HashMap<String, Vec<LocalDefId>> = HashMap::new();
    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        by_name
            .entry(tcx.item_name(def_id).as_str().to_string())
            .or_default()
            .push(local_def_id);
    }
    by_name
}

/// Resolve a `#[erasure(target)]` target string to a local DefId.
///
/// Strips generic arguments and module path prefixes, then matches by the
/// trailing identifier. Prefers candidates that have a body (the runtime
/// counterpart is expected to be implemented, not just declared).
fn resolve_local_target(
    tcx: TyCtxt<'_>,
    local_fns_by_name: &HashMap<String, Vec<LocalDefId>>,
    target: &str,
) -> Option<LocalDefId> {
    let base = erasure_target_base_name(target)?;
    let candidates = local_fns_by_name.get(&base)?;
    candidates
        .iter()
        .copied()
        .find(|candidate| tcx.hir_node_by_def_id(*candidate).body_id().is_some())
        .or_else(|| candidates.first().copied())
}

/// Extract the trailing identifier from an `#[erasure(...)]` target string.
///
/// Examples:
/// - `foo`                    → `Some("foo")`
/// - `crate::nested`          → `Some("nested")`
/// - `baz::<42>`              → `Some("baz")`
/// - `<i32 as Tr>::takes_ref` → `Some("takes_ref")`
/// - `private crate::nested`  → `Some("nested")` (Creusot's `private` visibility hint)
fn erasure_target_base_name(target: &str) -> Option<String> {
    let compact: String = target.chars().filter(|ch| !ch.is_whitespace()).collect();

    // For UFCS targets like `<Type as Trait>::method`, the method name follows
    // the closing `>::`. Strip the entire qualifier before the trailing path.
    let after_qualifier: &str = if compact.starts_with('<') {
        compact
            .find(">::")
            .map_or(compact.as_str(), |idx| &compact[idx + 3..])
    } else {
        compact.as_str()
    };

    // For paths with const-generic suffix like `baz::<42>`, drop everything
    // from the first `<` onward (not the leading `<` of a UFCS qualifier).
    let without_generics = after_qualifier
        .find("::<")
        .or_else(|| after_qualifier.find('<'))
        .map_or(after_qualifier, |index| &after_qualifier[..index]);

    without_generics
        .rsplit("::")
        .next()
        .filter(|name| !name.is_empty())
        .map(str::to_string)
}

/// Heuristic: does this HIR body look trivially empty (no statements and no
/// non-unit tail expression)?
///
/// This is intentionally conservative. A body like `fn f() {}` lowers to a
/// `Block` whose tail expression is `()`, so we accept that as "empty enough"
/// to fail the stub check only when there is literally nothing for the
/// erasure to be equivalent to (e.g., a `loop {}` would NOT be empty).
///
/// Note: as of Phase 6 (`#[erasure]` rewrite normalization), the structural
/// equivalence verdict has moved to
/// `crate::ghost::erasure::validate_erasure_attributes`. This helper is
/// retained for its tests and any future stub-check resurrection.
#[allow(dead_code)]
fn is_trivially_empty_body(body: &rustc_hir::Body<'_>) -> bool {
    use rustc_hir::ExprKind;

    fn is_unit_tail(expr: &rustc_hir::Expr<'_>) -> bool {
        match expr.kind {
            ExprKind::Tup(items) if items.is_empty() => true,
            ExprKind::Block(block, _) => {
                block.stmts.is_empty() && block.expr.is_none_or(is_unit_tail)
            }
            ExprKind::DropTemps(inner) => is_unit_tail(inner),
            _ => false,
        }
    }

    is_unit_tail(body.value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn erasure_target_base_name_handles_simple_ident() {
        assert_eq!(erasure_target_base_name("foo"), Some("foo".to_string()));
    }

    #[test]
    fn erasure_target_base_name_strips_module_path() {
        assert_eq!(
            erasure_target_base_name("crate::nested"),
            Some("nested".to_string())
        );
    }

    #[test]
    fn erasure_target_base_name_strips_generics() {
        assert_eq!(
            erasure_target_base_name("baz::<42>"),
            Some("baz".to_string())
        );
    }

    #[test]
    fn erasure_target_base_name_handles_trait_method() {
        // `<i32 as Tr>::takes_ref` (whitespace stripped) → `takes_ref`
        assert_eq!(
            erasure_target_base_name("<i32 as Tr>::takes_ref"),
            Some("takes_ref".to_string())
        );
    }

    #[test]
    fn erasure_target_base_name_handles_private_prefix() {
        // Creusot syntax `#[erasure(private crate::nested)]` — whitespace is
        // stripped, leaving `privatecrate::nested`; we then split on `::`.
        assert_eq!(
            erasure_target_base_name("private crate::nested"),
            Some("nested".to_string())
        );
    }

    #[test]
    fn erasure_target_base_name_empty_input_is_none() {
        assert_eq!(erasure_target_base_name(""), None);
    }
}
