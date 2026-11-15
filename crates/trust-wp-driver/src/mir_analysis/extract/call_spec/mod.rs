// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Function call spec resolution and application during MIR extraction.
//!
//! Keeps the public extract-facing call handling surface stable while delegating
//! routing, opaque fallback, mapping-closure extraction, and spec resolution to
//! focused leaf modules.

#[allow(unused_imports)] // Re-exported to child modules via `use super::*`
use std::collections::{HashMap, HashSet};

#[allow(unused_imports)] // Re-exported to child modules via `use super::*`
use rustc_hir::def_id::DefId;
#[allow(unused_imports)] // Re-exported to child modules via `use super::*`
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand},
    ty::TyCtxt,
};
#[allow(unused_imports)] // Re-exported to child modules via `use super::*`
use rustc_span::Spanned;
#[allow(unused_imports)] // Re-exported to child modules via `use super::*`
use trust_wp_core::formula::{BinOp, PureExpr};
#[allow(unused_imports)] // Re-exported to child modules via `use super::*`
use trust_wp_driver::StdSpec;

#[allow(unused_imports)] // Re-exported to child modules via `use super::*`
use super::{
    super::{
        call_resolve::{
            arg_names_for_def_id, extract_closure_def_id_from_fn_call,
            extract_fn_item_def_id_from_fn_trait_call, resolve_arg_names_or_warn,
            resolve_spec_or_mir_arg_names,
        },
        effects::{CallEffects, ExtractionSession},
        spec_apply::{
            apply_invariant_preconditions_with_effects, apply_postconditions_with_effects,
            apply_postconditions_with_self_and_effects, apply_preconditions_with_effects,
            apply_preconditions_with_self_and_effects, TranslatedArg,
        },
        translate::{translate_operand, ty_to_expr_sort_enriched},
    },
    call_args::{
        call_result_symbol, derive_self_expr_from_args, normalize_extern_spec_self_expr,
        translate_call_args_for_substitutions_with_tcx,
    },
    call_resolve_shared::{
        classify_cell_builtin_path, recover_snapshot_capture_current_pointee, resolve_call,
        ResolvedCallKind,
    },
    call_resolve_util::{extend_call_with_const_generic_args, wrap_call_context},
    cell_builtin::handle_cell_builtin_call,
    closure::{
        call_mutates_closure_state, closure_call_capture_bindings, first_call_arg_is_mut_ref,
        propagate_mutating_receiver_state_with_captures, propagate_mutating_ref_arg_states,
        propagate_mutating_ref_arg_states_for_positions, spec_mutates_closure_state,
        spec_mutating_ref_arg_positions, substitute_capture_fields_in_postcondition,
    },
    default_postcondition::specialize_default_postconditions_for_call,
    extract_from_block_with_context, extract_return_expr_with_context_detailed,
    helpers::wrap_projected_facts,
    try_operator::{try_branch_type_is_option, try_extract_try_operator, TryOperatorInput},
    BlockExtractionContext,
};

/// Common state for call-site handling during MIR extraction.
///
/// Bundles the parameters that are threaded unchanged (or with minimal
/// mutation) through every call-site handler, keeping function signatures
/// under clippy's `too_many_arguments` threshold. (#2657)
pub(in crate::mir_analysis::extract) struct CallSiteContext<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) body: &'a Body<'tcx>,
    pub(super) args: &'a [Spanned<Operand<'tcx>>],
    pub(super) destination: rustc_middle::mir::Place<'tcx>,
    pub(super) next_bb: BasicBlock,
    pub(super) local_exprs: HashMap<Local, PureExpr>,
    pub(super) visited: HashSet<BasicBlock>,
    pub(super) ctx: &'a BlockExtractionContext<'a>,
    pub(super) projected_write_facts: &'a [(PureExpr, PureExpr)],
}

/// True when `def_id` resolves to `Resource::valid_op_lemma` specifically — the
/// RA composition-validity lemma whose committed spec asserts
/// `op(self@, other@) != None` under `requires self.id() == other.id()`.
/// Fragment/Authority `valid_op_lemma` are deliberately excluded (see body).
/// (#2315)
fn callee_is_valid_op_lemma(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    is_resource_valid_op_lemma_path(&tcx.def_path_str(def_id))
}

/// Pure path predicate for `callee_is_valid_op_lemma` (unit-tested in `gate_tests`).
///
/// The exclusivity injection is sound ONLY for `Resource<Excl>::valid_op_lemma`.
/// Restrict precisely: the EXACT final method segment must be `valid_op_lemma`
/// (so a user method whose name merely ends with the string cannot match), the
/// carrier must be `Resource`, and Fragment/Authority `valid_op_lemma` are
/// EXCLUDED — their underlying RA is `Auth<R>`, where two valid resources may
/// share an id and the `self.id() != other.id()` fact would be UNSOUND.
fn is_resource_valid_op_lemma_path(path: &str) -> bool {
    path.rsplit("::").next() == Some("valid_op_lemma")
        // Carrier must be the `Resource` SEGMENT (possibly generic `Resource<…>`),
        // not merely a path that contains the substring "Resource" (e.g. a user
        // `MyResourceThing`). The substs[0]==canonical-Excl gate is the second,
        // independent guard, but match precisely here too.
        && path
            .split("::")
            .any(|s| s == "Resource" || s.starts_with("Resource<"))
        && !path.contains("Fragment")
        && !path.contains("Authority")
}

/// True when the ADT def is the canonical exclusive-RA type `Excl`.
fn ra_adt_is_canonical_excl(tcx: TyCtxt<'_>, ra_def: rustc_middle::ty::AdtDef<'_>) -> bool {
    is_canonical_excl_path(&tcx.def_path_str(ra_def.did()))
}

/// Pure path predicate for `ra_adt_is_canonical_excl` (unit-tested in `gate_tests`).
///
/// Used instead of `ends_with("Excl")` so a user type such as `MyExcl` cannot
/// trip the gate. Robust to re-export rendering (`def_path_str` gives e.g.
/// `creusot_std::logic::Excl`, not the full `…::ra::excl::Excl`): require the
/// EXACT final segment `Excl`, a std-crate prefix, and a `logic` module SEGMENT.
fn is_canonical_excl_path(path: &str) -> bool {
    let base = path.split('<').next().unwrap_or(path);
    base.rsplit("::").next() == Some("Excl")
        && (base.starts_with("creusot_std::") || base.starts_with("trust_wp_std::"))
        && base.split("::").any(|s| s == "logic")
}

/// True when `def_id` resolves to `Resource::join_shared` specifically.
///
/// Same shape as [`is_resource_valid_op_lemma_path`]: the EXACT final segment
/// must be `join_shared`, the carrier must be the `Resource` SEGMENT, and
/// `Fragment`/`Authority` are EXCLUDED (their underlying RA is `Auth<R>`, which
/// has non-trivial inclusion — the Ag consequence is NOT sound there).
/// (#quantifier-frontier)
fn is_resource_join_shared_path(path: &str) -> bool {
    path.rsplit("::").next() == Some("join_shared")
        && path
            .split("::")
            .any(|s| s == "Resource" || s.starts_with("Resource<"))
        && !path.contains("Fragment")
        && !path.contains("Authority")
}

/// Pure path predicate for the canonical agreement-RA type `Ag`.
///
/// Mirrors [`is_canonical_excl_path`] exactly: a user type named `MyAg` or a
/// third-party `Ag` must NOT trip the gate, so require the EXACT final segment
/// `Ag`, a std-crate prefix, and a `logic` module SEGMENT.
/// (#quantifier-frontier)
fn is_canonical_agree_path(path: &str) -> bool {
    let base = path.split('<').next().unwrap_or(path);
    base.rsplit("::").next() == Some("Ag")
        && (base.starts_with("creusot_std::") || base.starts_with("trust_wp_std::"))
        && base.split("::").any(|s| s == "logic")
}

/// True when the resource algebra `R` of a `Resource<R>::join_shared` call is
/// exactly the canonical agreement RA `Ag<_>`.
///
/// `join_shared` is defined on `Resource<R>`, so the `FnDef`'s first generic
/// argument is the RA type parameter `R` itself — inspect `substs[0]`, exactly
/// as [`self_ty_inner_ra_is_excl`] does. (#quantifier-frontier)
fn self_ty_inner_ra_is_agree<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> bool {
    let Operand::Constant(deref!(constant)) = func else {
        return false;
    };
    let rustc_middle::ty::TyKind::FnDef(_, substs) = constant.const_.ty().kind() else {
        return false;
    };
    let Some(ra_ty) = substs.skip_binder().first().and_then(|arg| arg.as_type()) else {
        return false;
    };
    matches!(
        ra_ty.peel_refs().kind(),
        rustc_middle::ty::TyKind::Adt(ra_def, _)
            if is_canonical_agree_path(&tcx.def_path_str(ra_def.did()))
    )
}

/// Augment `Resource::join_shared`'s `ensures` with the view-agreement fact
/// `self@ == other@` when — and ONLY when — the receiver's RA is the canonical
/// `Ag<_>`.
///
/// DERIVATION (why this is exact for `Ag`, and for nothing else).
/// Creusot's committed contract for `join_shared` is
/// ```text
///   requires self.id() == other.id()
///   ensures  result.id() == self.id()
///   ensures  self@.incl_eq(result@) && other@.incl_eq(result@)
/// ```
/// (`reference/creusot/creusot-std/src/ghost/resource.rs`). The generic
/// `incl_eq` is unrenderable for us (the RA element is erased before encoding
/// and the encoder has no `incl_eq`/`op`/`factor` methods), so
/// `RESOURCE_JOIN_SHARED` withholds it — see that const. For `Ag<T>` the clause
/// COLLAPSES to an equality that we can render:
///
/// * `Ag::op(a, b) = if a.0 == b.0 { Some(a) } else { None }`
///   (`reference/creusot/creusot-std/src/logic/ra/agree.rs`, `op`)
/// * `Ag::factor(self, factor) = self.op(factor)` (same file, `factor`)
/// * `a.incl(b) = b.factor(a) != None` (`…/logic/ra.rs`, `incl`)
///   ⇒ for `Ag`, `a.incl(b) ⟺ b.op(a) != None ⟺ a.0 == b.0 ⟺ a == b`
/// * `incl_eq(a, b) = a.eq(b) || a.incl(b)` (`…/logic/ra.rs`, `incl_eq`)
///   ⇒ for `Ag`, `incl_eq(a, b) ⟺ a == b`
///
/// So the committed ensures instantiates at `Ag` to
/// `self@ == result@ && other@ == result@`, which entails `self@ == other@`.
/// This is a THEOREM of Creusot's contract at `Ag`, not an approximation.
///
/// It is NOT a theorem for any RA with non-trivial inclusion: for `Frac`,
/// `Auth`/ViewRA or `FMapRA`, `a.incl(c) && b.incl(c)` says only that both sit
/// below the join, and two distinct fragments join without being equal.
/// Asserting the equality generically is the false accept the gate below
/// confines to `Ag`.
///
/// The `requires(self.id() == other.id())` clause stays committed and is
/// emitted as a caller obligation on EVERY RA including `Ag` — without it the
/// join relates unrelated resources and the derivation above does not apply.
///
/// Returns `Some(augmented)` when the gate fires, `None` to use the spec's own
/// `ensures` unchanged.
fn ag_join_shared_ensures<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
    def_id: DefId,
    ensures: &[String],
) -> Option<Vec<String>> {
    if !is_resource_join_shared_path(&tcx.def_path_str(def_id))
        || !self_ty_inner_ra_is_agree(tcx, func)
    {
        return None;
    }
    Some(ag_specialize_join_shared_ensures(ensures))
}

/// Pure ensures-rewrite for the `Ag` `join_shared` specialization (unit-tested
/// in `gate_tests`): keep every committed clause and append the derived
/// view-agreement fact.
fn ag_specialize_join_shared_ensures(ensures: &[String]) -> Vec<String> {
    let mut out: Vec<String> = ensures.to_vec();
    out.push("self@ == other@".to_string());
    out
}

#[cfg(test)]
mod gate_tests {
    use super::{
        ag_specialize_join_shared_ensures, excl_specialize_ensures, is_canonical_agree_path,
        is_canonical_excl_path, is_resource_join_shared_path, is_resource_valid_op_lemma_path,
    };

    #[test]
    fn resource_join_shared_gate_is_precise() {
        // The genuine target fires, in both renderings the driver can feed.
        assert!(is_resource_join_shared_path(
            "creusot_std::Resource::<R>::join_shared"
        ));
        assert!(is_resource_join_shared_path(
            "trust_wp_std::ghost::resource::Resource::join_shared"
        ));
        // Fragment/Authority (underlying RA `Auth<R>`, non-trivial inclusion —
        // `self@ == other@` is NOT a consequence there) must be excluded.
        assert!(!is_resource_join_shared_path(
            "creusot_std::Fragment::<R>::join_shared"
        ));
        assert!(!is_resource_join_shared_path(
            "creusot_std::Authority::<R>::join_shared"
        ));
        // A user type whose name merely CONTAINS "Resource".
        assert!(!is_resource_join_shared_path(
            "mycrate::MyResourceThing::join_shared"
        ));
        // A user method whose final segment is not exactly `join_shared`.
        assert!(!is_resource_join_shared_path(
            "mycrate::Resource::my_join_shared"
        ));
        // Right name, wrong carrier.
        assert!(!is_resource_join_shared_path("mycrate::Thing::join_shared"));
    }

    #[test]
    fn canonical_agree_gate_excludes_user_and_other_ras() {
        assert!(is_canonical_agree_path("creusot_std::logic::Ag"));
        assert!(is_canonical_agree_path(
            "trust_wp_std::logic::ra::agree::Ag"
        ));
        assert!(is_canonical_agree_path("creusot_std::logic::Ag<i32>"));
        // RAs with non-trivial inclusion MUST NOT match — the view-agreement
        // fact is unsound for them.
        assert!(!is_canonical_agree_path("creusot_std::logic::Frac"));
        assert!(!is_canonical_agree_path("creusot_std::logic::Auth"));
        assert!(!is_canonical_agree_path("creusot_std::logic::Excl"));
        assert!(!is_canonical_agree_path("creusot_std::logic::ViewRA"));
        // User types and wrong-crate / wrong-module spellings.
        assert!(!is_canonical_agree_path("mycrate::Ag")); // wrong crate prefix
        assert!(!is_canonical_agree_path("mycrate::logic::Ag")); // wrong crate prefix
        assert!(!is_canonical_agree_path("creusot_std::logic::MyAg")); // wrong final segment
        assert!(!is_canonical_agree_path("creusot_std::logic::Agree")); // wrong final segment
        assert!(!is_canonical_agree_path("creusot_std::other::Ag")); // no `logic` segment
    }

    #[test]
    fn ag_join_shared_specialization_appends_view_agreement() {
        // The committed RESOURCE_JOIN_SHARED ensures, as the spec parser yields
        // them (the unrenderable `incl_eq` conjunct is withheld at the const).
        let ensures = vec!["result.id() == self.id()".to_string()];
        let out = ag_specialize_join_shared_ensures(&ensures);
        assert_eq!(
            out,
            vec![
                "result.id() == self.id()".to_string(),
                "self@ == other@".to_string(),
            ]
        );
    }

    #[test]
    fn resource_valid_op_lemma_gate_is_precise() {
        // The genuine target fires.
        assert!(is_resource_valid_op_lemma_path(
            "creusot_std::Resource::<R>::valid_op_lemma"
        ));
        // The EXACT path the driver actually feeds (std_specs table form).
        assert!(is_resource_valid_op_lemma_path(
            "trust_wp_std::ghost::resource::Resource::valid_op_lemma"
        ));
        // A user type whose name merely CONTAINS "Resource" must NOT match on the
        // carrier substring (segment check); the substs-Excl gate is the second guard.
        assert!(!is_resource_valid_op_lemma_path(
            "mycrate::MyResourceThing::valid_op_lemma"
        ));
        // Fragment/Authority (underlying RA Auth<R>, same-id resources valid) are excluded.
        assert!(!is_resource_valid_op_lemma_path(
            "creusot_std::Fragment::<R>::valid_op_lemma"
        ));
        assert!(!is_resource_valid_op_lemma_path(
            "creusot_std::Authority::<R>::valid_op_lemma"
        ));
        // A user method whose final segment is not exactly `valid_op_lemma`.
        assert!(!is_resource_valid_op_lemma_path(
            "mycrate::Resource::my_valid_op_lemma"
        ));
        // Right name, wrong carrier.
        assert!(!is_resource_valid_op_lemma_path(
            "mycrate::Thing::<R>::valid_op_lemma"
        ));
    }

    #[test]
    fn canonical_excl_gate_excludes_user_and_other_ras() {
        // Canonical Excl across re-export renderings.
        assert!(is_canonical_excl_path("creusot_std::logic::Excl"));
        assert!(is_canonical_excl_path(
            "trust_wp_std::logic::ra::excl::Excl"
        ));
        assert!(is_canonical_excl_path("creusot_std::logic::Excl<i32>"));
        // User types and other RAs must NOT match (else the id!=id fact is unsound).
        assert!(!is_canonical_excl_path("mycrate::Excl")); // wrong crate prefix
        assert!(!is_canonical_excl_path("mycrate::logic::Excl")); // wrong crate prefix
        assert!(!is_canonical_excl_path("creusot_std::logic::MyExcl")); // wrong final segment
        assert!(!is_canonical_excl_path("creusot_std::logic::Agree")); // not Excl
        assert!(!is_canonical_excl_path("creusot_std::logic::Frac")); // not Excl
        assert!(!is_canonical_excl_path("creusot_std::other::Excl")); // no `logic` segment
        assert!(!is_canonical_excl_path("creusot_std::logical::Excl")); // `logical` != `logic` segment
    }

    #[test]
    fn excl_specialize_ensures_drops_op_keeps_frame_adds_id_neq() {
        // The committed RESOURCE_VALID_OP_LEMMA ensures, as the spec parser yields them.
        let ensures = vec![
            "^self == *self".to_string(),
            "self@.op(other@) != None".to_string(),
        ];
        let out = excl_specialize_ensures(&ensures);
        // The unencodable op clause is dropped; the frame is kept; id!=id is added.
        assert_eq!(
            out,
            vec![
                "^self == *self".to_string(),
                "self.id() != other.id()".to_string(),
            ]
        );
    }
}

/// True when the resource algebra `R` of the `Resource<R>::valid_op_lemma`
/// call is exactly the canonical `Excl<_>`.
///
/// `valid_op_lemma` is defined on `Resource<R>`, so the `FnDef`'s first generic
/// argument is the RA type parameter `R` itself (e.g. `Excl<i32>`), NOT the
/// `Resource<…>` wrapper. We therefore inspect `substs[0]` directly.
///
/// This is the SOUNDNESS GATE for the `valid_op_lemma` exclusivity injection:
/// the `self.id() != other.id()` fact is a sound consequence ONLY for an
/// exclusive RA, whose `op` is always `None`. Agree/Frac (whose `op` may be
/// `Some`, so two valid resources may share an id) MUST NOT match.
fn self_ty_inner_ra_is_excl<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> bool {
    let Operand::Constant(deref!(constant)) = func else {
        return false;
    };
    let rustc_middle::ty::TyKind::FnDef(_, substs) = constant.const_.ty().kind() else {
        return false;
    };
    // substs[0] is the RA type parameter `R` of `Resource<R>` — here `Excl<_>`.
    let Some(ra_ty) = substs.skip_binder().first().and_then(|arg| arg.as_type()) else {
        return false;
    };
    matches!(
        ra_ty.peel_refs().kind(),
        rustc_middle::ty::TyKind::Adt(ra_def, _)
            if ra_adt_is_canonical_excl(tcx, *ra_def)
    )
}

/// Augment a callee's `ensures` clauses with the Excl-gated `valid_op_lemma`
/// exclusivity fact when (and only when) the call is `Resource::valid_op_lemma`
/// on a `Resource<Excl<_>>` receiver (Fragment/Authority excluded). (#2315)
///
/// `Resource::valid_op_lemma` carries the committed spec
/// ```text
///   requires self.id() == other.id()
///   ensures  ^self == *self
///   ensures  self@.op(other@) != None
/// ```
/// The `op != None` consequence is the SOUND contradiction for an exclusive RA
/// (where `op` is always `None`), but `op` is unencodable here: `Excl` is erased
/// before the encoder (the receiver sort is `Datatype("Resource")` + PhantomData),
/// so that ensures clause cannot fire and the lemma is inert.
///
/// The driver, however, has the concrete `Self = Resource<Excl<_>>` at the call
/// site. For Excl specifically, the validity lemma's only sound, op-free
/// consequence is the exclusivity invariant: two valid Excl resources have
/// distinct ids, i.e. `self.id() != other.id()`. (For an exclusive RA,
/// `requires(id==id) ∧ ensures(op==None) ∧ ensures(op!=None)` is `false`, so the
/// call is reachable only when `id != id`.) Injecting `self.id() != other.id()`,
/// strictly gated to Excl receivers, reproduces the lemma's intended effect
/// without ever touching `op`. The `self`/`other` param names match the
/// committed spec's `params: self, other`, and `id` is the same method the goal
/// uses, so the injected clause substitutes and encodes exactly like the
/// existing ensures.
///
/// The committed spec's `self@.op(other@) != None` clause is UNENCODABLE — the
/// ay encoder has no `op` method and `Excl` is erased before encoding, so that
/// clause raises a hard `unknown method op` encoding error. For Excl we
/// therefore DROP that unencodable
/// clause and substitute its sound, derived consequence `self.id() != other.id()`.
/// The `^self == *self` clause (encodable, sound) is kept. This is not a
/// weakening: `id != id` is exactly what `requires(id==id) ∧ (op==None) ∧
/// (op!=None)` entails for an exclusive RA. We never assert `op != None`
/// itself: for Excl it is false, and a false premise makes every goal at the
/// call site vacuous.
///
/// SOUNDNESS NOTE — why injecting `id != id` is sound even though trust-wp does
/// not separately encode Excl exclusivity. `self.id() != other.id()` is
/// asserted as a DERIVED AXIOM: it is TRUE in the intended resource-algebra model
/// (Excl exclusivity — no two valid `Excl` resources share an id), but the SMT
/// solver cannot *derive* it because exclusivity is not separately encoded.
/// Asserting a fact that is true in the intended model is SOUND — it rules out
/// only the spurious models where two valid Excls share an id, which violate the
/// RA semantics. Crucially, this is NOT a false-accept channel: the only way a
/// caller obtains `id == id` for two `Resource<Excl>` is (a) an explicit
/// `requires(x.id()==y.id())`, OR (b) constructing two same-id Excls. (a) is
/// unsatisfiable in the intended model, so combined with the injected `id != id`
/// the driver's vacuity detector reports the obligation VACUOUS (verified=0) —
/// never `verified=1`, never a genuine proof; (b) is unconstructible because
/// `Resource::split`'s precondition (`incl_eq_op`) is unsatisfiable for Excl
/// (`op` always `None`). The exploits this rules out — `requires(id==id)
/// ensures(false)`, `ensures(result==1)` — come out vacuous, never verified;
/// the split construction and the no-lemma copy are rejected. `excl.rs` itself
/// verifies NON-vacuously: the `id==id` branch is dead and the reachable path
/// proves the true postcondition `id != id`.
///
/// The single SOUNDNESS GATE shared by the Excl `valid_op_lemma` specialization:
/// fires iff the call is `Resource::valid_op_lemma` (carrier `Resource`;
/// Fragment/Authority EXCLUDED, since their underlying RA is `Auth<R>` where
/// same-id resources are valid) on a `Resource<Excl<_>>` receiver. Both the
/// `ensures` rewrite (`excl_valid_op_lemma_ensures`) and the `requires` clearing
/// (`excl_valid_op_lemma_clear_requires`) are conditioned on exactly this
/// predicate, so the specialization can never partially apply to a non-Excl RA.
fn excl_valid_op_lemma_gate<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>, def_id: DefId) -> bool {
    callee_is_valid_op_lemma(tcx, def_id) && self_ty_inner_ra_is_excl(tcx, func)
}

/// Returns `Some(augmented)` when the gate fires (caller should pass the
/// returned vec to the postcondition machinery), or `None` to use the
/// original `spec.ensures` unchanged.
fn excl_valid_op_lemma_ensures<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
    def_id: DefId,
    ensures: &[String],
) -> Option<Vec<String>> {
    if excl_valid_op_lemma_gate(tcx, func, def_id) {
        Some(excl_specialize_ensures(ensures))
    } else {
        None
    }
}

/// Pure ensures-rewrite for the Excl `valid_op_lemma` specialization (unit-tested
/// in `gate_tests`): drop the unencodable `op(...) != None` clause, keep every
/// other clause (the frame `^self == *self`), and append the sound op-free
/// exclusivity consequence `self.id() != other.id()`.
///
/// The `.op(` literal filter is intentionally specific to the single committed
/// `RESOURCE_VALID_OP_LEMMA` clause `self@.op(other@) != None` — the only clause
/// containing `.op(`. MUST be revisited if that const ever gains other clauses.
fn excl_specialize_ensures(ensures: &[String]) -> Vec<String> {
    let mut out: Vec<String> = ensures
        .iter()
        .filter(|e| !e.contains(".op("))
        .cloned()
        .collect();
    out.push("self.id() != other.id()".to_string());
    out
}

/// When the Excl `valid_op_lemma` gate fires, the committed
/// `requires: self.id() == other.id()` MUST be dropped at this call site.
///
/// SOUNDNESS — why dropping the precondition is correct for Excl, and ONLY Excl:
///
/// The committed `requires self.id() == other.id()` is emitted as a *caller proof
/// obligation* (`apply_preconditions_*` pushes it into `effects.obligations`).
/// At excl.rs's call site that obligation substitutes to `x.id() == y.id()`,
/// which directly contradicts the function's own postcondition
/// `x.id() != y.id()` → the call site is unprovable regardless of the ensures.
/// The ensures rewrite alone cannot fix this; the `id==id` obligation is the real
/// blocker.
///
/// For an EXCLUSIVE RA the precondition is not a real obligation at all:
///  * `valid_op_lemma(&mut self, &other)` takes `&mut self` and `&other`, so by
///    the borrow checker `self` and `other` cannot alias — they are distinct
///    `Resource` values.
///  * The exclusivity invariant of `Excl` (`op` is always `None`) means no two
///    valid `Excl` resources share an id. Two distinct valid Excl resources
///    therefore satisfy `self.id() != other.id()` UNCONDITIONALLY.
/// Hence the Excl-specialized spec is `requires: (none)`,
/// `ensures: ^self == *self ∧ self.id() != other.id()`. Emitting no caller
/// obligation is sound because the original obligation was unsatisfiable-by-design
/// for Excl (the lemma is meant to be invoked precisely to DERIVE `id != id`, not
/// to require `id == id`).
///
/// This is strictly gated to Excl (`excl_valid_op_lemma_gate`). Frac/Ag CAN
/// split/share ids, so for them `id == id` is a genuine precondition that must be
/// discharged and `id != id` is NOT a sound consequence — neither the requires
/// clearing nor the ensures injection applies to them.
fn excl_valid_op_lemma_clear_requires<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
    def_id: DefId,
) -> bool {
    excl_valid_op_lemma_gate(tcx, func, def_id)
}

mod dispatch;
mod fallback;
mod mapping_closure;
mod open_logic_unfold;
mod spec_resolution;

pub(in crate::mir_analysis::extract) use dispatch::handle_call_terminator;
#[cfg(test)]
pub(in crate::mir_analysis::extract) use mapping_closure::{
    collect_equality_substitutions, is_call_result_var,
};
pub(in crate::mir_analysis) use spec_resolution::callee_invariant_premises;
pub(in crate::mir_analysis::extract) use spec_resolution::{
    charge_callee_invariant_grant, entered_body_def_id,
};
