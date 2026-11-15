// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type gate for `Iterator::collect` specs.
//!
//! The generic `ITERATOR_COLLECT` table entry states nothing about the
//! collected value, because Creusot's contract relates `result` to the
//! PRODUCED sequence (`exists<done, prod> done.completed() &&
//! self.produces(prod, *done) && B::from_iter_post(prod, result)`), and that
//! sequence is not `self@` for adapters (`filter`, `map`, `rev`, `skip`, ...).
//!
//! This gate reads the call's monomorphized FnDef generic arguments
//! `Iterator::collect::<Self, B>` and, only for a whitelisted `(Self, B)` pair
//! whose produced sequence is exactly determined by `self@`, appends
//! `ITERATOR_COLLECT_ROUNDTRIP` (`result@ == self@`). The per-pair derivations
//! from Creusot's `produces` / `completed` / `from_iter_post` definitions are
//! documented on that constant in `trust-wp-std/src/std/iter/specs.rs`.
//!
//! Fail-closed: anything the gate cannot positively classify (generic `Self`,
//! a user override of `collect`, an element-type mismatch, an unknown path)
//! keeps the empty generic spec. A missed classification costs completeness,
//! never soundness.

use rustc_middle::{
    mir::{BasicBlock, Body, Operand, Place, TerminatorKind},
    ty::{self, GenericArgs, Ty, TyCtxt},
};
use trust_wp_driver::StdSpec;

/// A `(Self, B)` collect pair for which `result@ == self@` is a theorem.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CollectRoundtripPair {
    /// `alloc::vec::IntoIter<T>` into `Vec<T>`.
    VecIntoIter,
    /// `std::collections::hash_map::IntoIter<K, V>` into `HashMap<K, V, S>`.
    HashMapIntoIter,
    /// `std::collections::hash_set::IntoIter<T>` into `HashSet<T, S>`.
    HashSetIntoIter,
}

/// The std collections whose diagnostic items anchor type identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Collection {
    Vec,
    HashMap,
    HashSet,
}

impl Collection {
    const ALL: [Collection; 3] = [Collection::Vec, Collection::HashMap, Collection::HashSet];

    fn diagnostic_sym(self) -> rustc_span::Symbol {
        match self {
            Collection::Vec => rustc_span::sym::Vec,
            Collection::HashMap => rustc_span::sym::HashMap,
            Collection::HashSet => rustc_span::sym::HashSet,
        }
    }

    /// Crate-qualified, verbose def path of the collection's `IntoIter`
    /// struct, as defined in the same crate as the collection itself.
    fn into_iter_def_path(self) -> &'static str {
        match self {
            Collection::Vec => "alloc::vec::into_iter::IntoIter",
            Collection::HashMap => "std::collections::hash::map::IntoIter",
            Collection::HashSet => "std::collections::hash::set::IntoIter",
        }
    }

    fn pair(self) -> CollectRoundtripPair {
        match self {
            Collection::Vec => CollectRoundtripPair::VecIntoIter,
            Collection::HashMap => CollectRoundtripPair::HashMapIntoIter,
            Collection::HashSet => CollectRoundtripPair::HashSetIntoIter,
        }
    }
}

/// Provenance of an ADT, resolved from its `DefId` (never from a printed,
/// user-spoofable path such as `def_path_str`, which omits the crate for
/// local items: a user `mod alloc { mod vec { struct IntoIter } }` prints as
/// `alloc::vec::IntoIter`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeIdentity {
    /// Defined in the crate being verified.
    pub(crate) is_local: bool,
    /// `crate_name` + verbose def path (includes the defining crate).
    pub(crate) crate_qualified_path: String,
    /// The collection whose diagnostic item IS this `DefId`, if any.
    pub(crate) diagnostic_item: Option<Collection>,
    /// Collections whose diagnostic item is defined in this type's crate.
    pub(crate) crate_defines: Vec<Collection>,
}

/// Classify a `(Self, B)` pair by DefId provenance. The caller must
/// additionally check that the element type arguments agree (see
/// [`element_args_agree`]); this function only matches the constructors.
///
/// `B` must BE the collection's diagnostic item (`Vec`, `HashMap`,
/// `HashSet`). `Self` must be a non-local type, defined in the same crate as
/// that diagnostic item, whose crate-qualified def path is exactly the
/// collection's `IntoIter` struct. Everything else, including every local
/// item, is `None`.
pub(crate) fn classify_collect_roundtrip(
    self_id: &TypeIdentity,
    b_id: &TypeIdentity,
) -> Option<CollectRoundtripPair> {
    if self_id.is_local || b_id.is_local {
        return None;
    }
    let collection = b_id.diagnostic_item?;
    if !self_id.crate_defines.contains(&collection) {
        return None;
    }
    if self_id.crate_qualified_path != collection.into_iter_def_path() {
        return None;
    }
    Some(collection.pair())
}

/// Number of leading type arguments that must be identical between `Self`
/// and `B` for the pair (the element type(s); allocator and hasher
/// parameters do not affect the view).
pub(crate) fn element_arity(pair: CollectRoundtripPair) -> usize {
    match pair {
        CollectRoundtripPair::VecIntoIter | CollectRoundtripPair::HashSetIntoIter => 1,
        CollectRoundtripPair::HashMapIntoIter => 2,
    }
}

/// True when the first `arity` type arguments of both sides exist and are
/// pairwise equal.
pub(crate) fn element_args_agree<T: PartialEq>(self_tys: &[T], b_tys: &[T], arity: usize) -> bool {
    self_tys.len() >= arity
        && b_tys.len() >= arity
        && self_tys[..arity]
            .iter()
            .zip(&b_tys[..arity])
            .all(|(a, b)| a == b)
}

/// `(Self, B)` of a call to the trait method `Iterator::collect` itself (not
/// a user override), read from the FnDef generic arguments.
pub(crate) fn iterator_collect_call_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
) -> Option<(Ty<'tcx>, Ty<'tcx>)> {
    let Operand::Constant(constant) = func else {
        return None;
    };
    let ty::TyKind::FnDef(def_id, args) = constant.const_.ty().kind() else {
        return None;
    };
    let assoc = tcx.opt_associated_item(*def_id)?;
    if !matches!(assoc.container, ty::AssocContainer::Trait) {
        return None;
    }
    let trait_def_id = tcx.parent(*def_id);
    if !tcx.is_diagnostic_item(rustc_span::sym::Iterator, trait_def_id) {
        return None;
    }
    if tcx.item_name(*def_id).as_str() != "collect" {
        return None;
    }
    collect_self_and_target(args.skip_binder())
}

fn collect_self_and_target<'tcx>(args: GenericArgs<'tcx>) -> Option<(Ty<'tcx>, Ty<'tcx>)> {
    let mut tys = args.types();
    let self_ty = tys.next()?;
    let b_ty = tys.next()?;
    Some((self_ty, b_ty))
}

fn adt_identity<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(TypeIdentity, Vec<Ty<'tcx>>)> {
    let ty::TyKind::Adt(adt_def, args) = ty.kind() else {
        return None;
    };
    let did = adt_def.did();
    let crate_qualified_path = format!(
        "{}{}",
        tcx.crate_name(did.krate),
        tcx.def_path(did).to_string_no_crate_verbose()
    );
    let diagnostic_item = Collection::ALL
        .into_iter()
        .find(|c| tcx.is_diagnostic_item(c.diagnostic_sym(), did));
    let crate_defines = Collection::ALL
        .into_iter()
        .filter(|c| {
            tcx.get_diagnostic_item(c.diagnostic_sym())
                .is_some_and(|item| item.krate == did.krate)
        })
        .collect();
    let identity = TypeIdentity {
        is_local: did.is_local(),
        crate_qualified_path,
        diagnostic_item,
        crate_defines,
    };
    Some((identity, args.types().collect()))
}

/// Classify the `(Self, B)` pair of an `Iterator::collect` call.
pub(crate) fn collect_roundtrip_pair<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
) -> Option<CollectRoundtripPair> {
    let (self_ty, b_ty) = iterator_collect_call_types(tcx, func)?;
    let (self_id, self_tys) = adt_identity(tcx, self_ty)?;
    let (b_id, b_tys) = adt_identity(tcx, b_ty)?;
    let pair = classify_collect_roundtrip(&self_id, &b_id);
    let gated = pair.filter(|pair| element_args_agree(&self_tys, &b_tys, element_arity(*pair)));
    if std::env::var_os("TRUST_WP_DEBUG").is_some() {
        eprintln!("[TRUST_WP_DEBUG] collect gate: self={self_id:?} b={b_id:?} -> {gated:?}");
    }
    gated
}

/// True when the call is `Iterator::collect::<_, Vec<_>>` with `Vec` the
/// genuine `alloc` diagnostic item (never a local lookalike). Used by the
/// `map_inv` view-axiom binding: `Vec::from_iter_post(prod, res) == (prod ==
/// res@)`, so facts about the produced sequence hold of `res@` only for `Vec`.
pub(crate) fn is_collect_into_vec<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> bool {
    let Some((_, b_ty)) = iterator_collect_call_types(tcx, func) else {
        return false;
    };
    adt_identity(tcx, b_ty)
        .is_some_and(|(id, _)| !id.is_local && id.diagnostic_item == Some(Collection::Vec))
}

/// The unique block whose terminator is a `Call` writing `destination` and
/// returning to `target`. `None` when there is no such block or more than
/// one (fail closed: a call site that cannot be identified gets no facts).
pub(crate) fn call_block<'tcx>(
    body: &Body<'tcx>,
    destination: Place<'tcx>,
    target: BasicBlock,
) -> Option<BasicBlock> {
    let mut found = None;
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let Some(terminator) = data.terminator.as_ref() else {
            continue;
        };
        if let TerminatorKind::Call {
            destination: dest,
            target: Some(call_target),
            ..
        } = &terminator.kind
        {
            if *dest == destination && *call_target == target {
                if found.is_some() {
                    return None;
                }
                found = Some(bb);
            }
        }
    }
    found
}

/// True when `bb` lies on a CFG cycle (it is reachable from one of its own
/// successors, unwind edges included).
pub(crate) fn block_on_cycle(body: &Body<'_>, bb: BasicBlock) -> bool {
    let mut seen = rustc_index::bit_set::DenseBitSet::new_empty(body.basic_blocks.len());
    let mut stack: Vec<BasicBlock> = body.basic_blocks[bb].terminator().successors().collect();
    while let Some(next) = stack.pop() {
        if next == bb {
            return true;
        }
        if seen.insert(next) {
            stack.extend(body.basic_blocks[next].terminator().successors());
        }
    }
    false
}

/// True when the reachable block `bb` dominates every reachable `Return`
/// block, i.e. every normally-terminating execution passes through it.
pub(crate) fn dominates_every_return(body: &Body<'_>, bb: BasicBlock) -> bool {
    let dominators = body.basic_blocks.dominators();
    if !dominators.is_reachable(bb) {
        return false;
    }
    body.basic_blocks.iter_enumerated().all(|(ret, data)| {
        !matches!(
            data.terminator.as_ref().map(|t| &t.kind),
            Some(TerminatorKind::Return)
        ) || !dominators.is_reachable(ret)
            || dominators.dominates(bb, ret)
    })
}

/// Structural precondition for stating `map_inv(..).collect()` view facts as
/// FUNCTION-LEVEL assumptions (review S1): the `map_inv` call block and the
/// `collect` call block are both acyclic, the `map_inv` block dominates the
/// `collect` block, and the `collect` block dominates every return. Then
/// every normally-terminating execution runs exactly one `map_inv` call and
/// then exactly one `collect` call on its result, so the facts describe that
/// execution's single collected value.
pub(crate) fn map_inv_collect_site_is_structural(
    body: &Body<'_>,
    map_inv_block: BasicBlock,
    collect_block: BasicBlock,
) -> bool {
    let dominators = body.basic_blocks.dominators();
    dominators.is_reachable(map_inv_block)
        && dominators.is_reachable(collect_block)
        && !block_on_cycle(body, map_inv_block)
        && !block_on_cycle(body, collect_block)
        && dominators.dominates(map_inv_block, collect_block)
        && dominates_every_return(body, collect_block)
}

/// Append the gated roundtrip clauses to a resolved `collect` spec. Specs
/// for any other call, and collect calls outside the whitelist, are returned
/// unchanged. Appending is sound for any base spec: every appended clause is
/// a theorem of Creusot's contract for the classified pair.
pub(crate) fn refine_collect_spec<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
    mut spec: StdSpec,
) -> StdSpec {
    if collect_roundtrip_pair(tcx, func).is_none() {
        return spec;
    }
    let (params, ensures) = roundtrip_clauses();
    for clause in ensures {
        if !spec.ensures.contains(&clause) {
            spec.ensures.push(clause);
        }
    }
    if spec.param_names.is_none() {
        spec.param_names = Some(params);
    }
    spec
}

/// `(params, ensures)` of `ITERATOR_COLLECT_ROUNDTRIP`, read from the
/// trust-wp-std constant so the clause text has a single owner.
fn roundtrip_clauses() -> (Vec<String>, Vec<String>) {
    let mut params = Vec::new();
    let mut ensures = Vec::new();
    for line in trust_wp_std::std::iter::specs::ITERATOR_COLLECT_ROUNDTRIP.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("params:") {
            params.extend(rest.split(',').map(|p| p.trim().to_string()));
        } else if let Some(rest) = line.strip_prefix("ensures:") {
            ensures.push(rest.trim().to_string());
        }
    }
    (params, ensures)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn std_item(path: &str, diag: Option<Collection>, defines: &[Collection]) -> TypeIdentity {
        TypeIdentity {
            is_local: false,
            crate_qualified_path: path.to_string(),
            diagnostic_item: diag,
            crate_defines: defines.to_vec(),
        }
    }

    fn vec_ty() -> TypeIdentity {
        std_item("alloc::vec::Vec", Some(Collection::Vec), &[Collection::Vec])
    }
    fn hashmap_ty() -> TypeIdentity {
        std_item(
            "std::collections::hash::map::HashMap",
            Some(Collection::HashMap),
            &[Collection::HashMap, Collection::HashSet],
        )
    }
    fn hashset_ty() -> TypeIdentity {
        std_item(
            "std::collections::hash::set::HashSet",
            Some(Collection::HashSet),
            &[Collection::HashMap, Collection::HashSet],
        )
    }
    fn alloc_item(path: &str) -> TypeIdentity {
        std_item(path, None, &[Collection::Vec])
    }
    fn std_crate_item(path: &str) -> TypeIdentity {
        std_item(path, None, &[Collection::HashMap, Collection::HashSet])
    }

    #[test]
    fn whitelist_accepts_same_view_pairs() {
        assert_eq!(
            classify_collect_roundtrip(&alloc_item("alloc::vec::into_iter::IntoIter"), &vec_ty()),
            Some(CollectRoundtripPair::VecIntoIter)
        );
        assert_eq!(
            classify_collect_roundtrip(
                &std_crate_item("std::collections::hash::map::IntoIter"),
                &hashmap_ty()
            ),
            Some(CollectRoundtripPair::HashMapIntoIter)
        );
        assert_eq!(
            classify_collect_roundtrip(
                &std_crate_item("std::collections::hash::set::IntoIter"),
                &hashset_ty()
            ),
            Some(CollectRoundtripPair::HashSetIntoIter)
        );
    }

    /// Review F1: a LOCAL item whose printed path is `alloc::vec::IntoIter`
    /// (or even whose crate-qualified path matches) must never classify.
    #[test]
    fn local_lookalikes_never_classify() {
        let mut local_into_iter = alloc_item("alloc::vec::into_iter::IntoIter");
        local_into_iter.is_local = true;
        assert_eq!(
            classify_collect_roundtrip(&local_into_iter, &vec_ty()),
            None
        );
        // The review's p1 shape: local crate `creusot_test`, printed path
        // `alloc::vec::IntoIter`; its crate defines no collection.
        let p1 = TypeIdentity {
            is_local: true,
            crate_qualified_path: "creusot_test::alloc::vec::IntoIter".to_string(),
            diagnostic_item: None,
            crate_defines: vec![],
        };
        assert_eq!(classify_collect_roundtrip(&p1, &vec_ty()), None);
        // B-side lookalike: a local `mod std { mod vec { struct Vec } }`.
        let local_vec = TypeIdentity {
            is_local: true,
            crate_qualified_path: "creusot_test::std::vec::Vec".to_string(),
            diagnostic_item: None,
            crate_defines: vec![],
        };
        assert_eq!(
            classify_collect_roundtrip(&alloc_item("alloc::vec::into_iter::IntoIter"), &local_vec),
            None
        );
        let mut local_vec_claiming_item = vec_ty();
        local_vec_claiming_item.is_local = true;
        assert_eq!(
            classify_collect_roundtrip(
                &alloc_item("alloc::vec::into_iter::IntoIter"),
                &local_vec_claiming_item
            ),
            None
        );
        // HashMap / HashSet lookalikes.
        let local_hm = TypeIdentity {
            is_local: true,
            crate_qualified_path: "creusot_test::std::collections::HashMap".to_string(),
            diagnostic_item: None,
            crate_defines: vec![],
        };
        assert_eq!(
            classify_collect_roundtrip(
                &std_crate_item("std::collections::hash::map::IntoIter"),
                &local_hm
            ),
            None
        );
        let mut local_hs_iter = std_crate_item("std::collections::hash::set::IntoIter");
        local_hs_iter.is_local = true;
        assert_eq!(
            classify_collect_roundtrip(&local_hs_iter, &hashset_ty()),
            None
        );
    }

    /// A non-local type in some OTHER crate whose path text matches is still
    /// refused: `Self` must live in the crate that defines B's diagnostic item.
    #[test]
    fn foreign_crate_lookalikes_never_classify() {
        let foreign = std_item("alloc::vec::into_iter::IntoIter", None, &[]);
        assert_eq!(classify_collect_roundtrip(&foreign, &vec_ty()), None);
        let foreign_vec = std_item("alloc::vec::Vec", None, &[]);
        assert_eq!(
            classify_collect_roundtrip(
                &alloc_item("alloc::vec::into_iter::IntoIter"),
                &foreign_vec
            ),
            None
        );
        // Visible re-export spellings are not the crate-qualified def path.
        for spelled in ["alloc::vec::IntoIter", "std::vec::IntoIter"] {
            assert_eq!(
                classify_collect_roundtrip(&alloc_item(spelled), &vec_ty()),
                None
            );
        }
    }

    #[test]
    fn whitelist_rejects_adapters_and_cross_collection_pairs() {
        for (self_path, in_alloc) in [
            ("core::iter::adapters::filter::Filter", false),
            ("core::iter::adapters::map::Map", false),
            ("core::iter::adapters::rev::Rev", false),
            ("core::iter::adapters::skip::Skip", false),
            ("core::iter::adapters::take::Take", false),
            ("core::iter::adapters::chain::Chain", false),
            ("core::iter::adapters::step_by::StepBy", false),
            ("core::iter::adapters::enumerate::Enumerate", false),
            ("core::iter::adapters::copied::Copied", false),
            ("core::iter::sources::once::Once", false),
            ("core::ops::range::Range", false),
            ("alloc::vec::drain::Drain", true),
            // Not whitelisted: `to_ref_seq` has no stated body.
            ("core::slice::iter::Iter", false),
            ("std::collections::hash::map::Iter", false),
            ("std::collections::hash::set::Iter", false),
        ] {
            let self_id = if in_alloc {
                alloc_item(self_path)
            } else if self_path.starts_with("std::") {
                std_crate_item(self_path)
            } else {
                std_item(self_path, None, &[])
            };
            for b in [vec_ty(), hashmap_ty(), hashset_ty()] {
                assert_eq!(
                    classify_collect_roundtrip(&self_id, &b),
                    None,
                    "{self_path} -> {b:?} must not get the roundtrip"
                );
            }
        }
        let vec_iter = alloc_item("alloc::vec::into_iter::IntoIter");
        assert_eq!(classify_collect_roundtrip(&vec_iter, &hashmap_ty()), None);
        assert_eq!(classify_collect_roundtrip(&vec_iter, &hashset_ty()), None);
        let hs_iter = std_crate_item("std::collections::hash::set::IntoIter");
        assert_eq!(classify_collect_roundtrip(&hs_iter, &vec_ty()), None);
        assert_eq!(classify_collect_roundtrip(&hs_iter, &hashmap_ty()), None);
        let hm_iter = std_crate_item("std::collections::hash::map::IntoIter");
        assert_eq!(classify_collect_roundtrip(&hm_iter, &hashset_ty()), None);
        let string = std_item("alloc::string::String", None, &[Collection::Vec]);
        assert_eq!(classify_collect_roundtrip(&vec_iter, &string), None);
    }

    #[test]
    fn roundtrip_clauses_are_exactly_the_view_equality() {
        let (params, ensures) = roundtrip_clauses();
        assert_eq!(params, vec!["self".to_string()]);
        assert_eq!(ensures, vec!["result@ == self@".to_string()]);
    }

    /// Review S2: `adt_identity` on REAL rustc types (a compiled fixture's
    /// fn signature), so a wrong identity computation (crate name, verbose
    /// def path, diagnostic items, locality) fails here rather than only in
    /// hand-built `TypeIdentity` values.
    #[test]
    fn adt_identity_classifies_real_rustc_types() {
        use std::sync::atomic::{AtomicU64, Ordering};

        static COUNTER: AtomicU64 = AtomicU64::new(0);

        type Outcome = (
            TypeIdentity,
            TypeIdentity,
            Option<CollectRoundtripPair>,
            bool,
        );

        struct RealTypes {
            pairs: Vec<(usize, usize)>,
            results: Vec<Outcome>,
            ran: bool,
        }

        impl rustc_driver::Callbacks for RealTypes {
            #[allow(clippy::elidable_lifetime_names)]
            fn after_analysis<'tcx>(
                &mut self,
                _compiler: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                for owner in tcx.hir_body_owners() {
                    let def_id = owner.to_def_id();
                    if !matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::Fn)
                        || tcx.opt_item_name(def_id).map(|n| n.as_str() == "sig") != Some(true)
                    {
                        continue;
                    }
                    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                    let inputs = sig.inputs();
                    for &(self_idx, b_idx) in &self.pairs {
                        let (self_id, self_tys) =
                            adt_identity(tcx, inputs[self_idx]).expect("Self is an ADT");
                        let (b_id, b_tys) = adt_identity(tcx, inputs[b_idx]).expect("B is an ADT");
                        let pair = classify_collect_roundtrip(&self_id, &b_id);
                        let agree = pair.is_some_and(|pair| {
                            element_args_agree(&self_tys, &b_tys, element_arity(pair))
                        });
                        self.results.push((self_id, b_id, pair, agree));
                    }
                    self.ran = true;
                }
                rustc_driver::Compilation::Stop
            }
        }

        let source = r#"
pub mod alloc {
    pub mod vec {
        pub struct IntoIter<T>(pub Vec<T>);
    }
}
pub mod lookalike {
    pub mod vec {
        pub struct Vec<T>(pub ::std::vec::Vec<T>);
    }
}
#[allow(clippy::too_many_arguments)]
pub fn sig(
    _0: std::vec::IntoIter<u32>,
    _1: Vec<u32>,
    _2: std::collections::hash_map::IntoIter<u32, u8>,
    _3: std::collections::HashMap<u32, u8>,
    _4: std::collections::hash_set::IntoIter<u32>,
    _5: std::collections::HashSet<u32>,
    _6: alloc::vec::IntoIter<u32>,
    _7: lookalike::vec::Vec<u32>,
    _8: Vec<u64>,
    _9: std::collections::hash_map::IntoIter<u32, u16>,
    _10: std::iter::Rev<std::vec::IntoIter<u32>>,
) {
}
"#;
        let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_collect_gate_real_types_{}_{}",
            std::process::id(),
            unique
        ));
        std::fs::create_dir_all(&temp_dir).expect("create test temp dir");
        let source_path = temp_dir.join("test.rs");
        std::fs::write(&source_path, source).expect("write test source");
        let args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_collect_gate_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];
        let pairs = vec![
            (0, 1),  // real Vec IntoIter -> Vec<u32>
            (2, 3),  // real HashMap IntoIter -> HashMap<u32, u8>
            (4, 5),  // real HashSet IntoIter -> HashSet<u32>
            (6, 1),  // LOCAL alloc::vec::IntoIter -> Vec
            (0, 7),  // real IntoIter -> LOCAL Vec lookalike
            (0, 8),  // element mismatch u32 -> u64
            (9, 3),  // value mismatch u16 -> u8
            (10, 1), // adapter
            (0, 3),  // cross collection
            (4, 1),  // cross collection
        ];
        let mut callbacks = RealTypes {
            pairs,
            results: Vec::new(),
            ran: false,
        };
        rustc_driver::run_compiler(&args, &mut callbacks);
        let _ = std::fs::remove_dir_all(&temp_dir);
        assert!(callbacks.ran, "fixture fn `sig` not found");
        let got: Vec<(Option<CollectRoundtripPair>, bool)> = callbacks
            .results
            .iter()
            .map(|(_, _, pair, agree)| (*pair, *agree))
            .collect();
        assert_eq!(
            got,
            vec![
                (Some(CollectRoundtripPair::VecIntoIter), true),
                (Some(CollectRoundtripPair::HashMapIntoIter), true),
                (Some(CollectRoundtripPair::HashSetIntoIter), true),
                (None, false),
                (None, false),
                (Some(CollectRoundtripPair::VecIntoIter), false),
                (Some(CollectRoundtripPair::HashMapIntoIter), false),
                (None, false),
                (None, false),
                (None, false),
            ],
            "identities: {:#?}",
            callbacks.results
        );
        let (real_iter, real_vec, _, _) = &callbacks.results[0];
        assert!(!real_iter.is_local && !real_vec.is_local);
        assert_eq!(
            real_iter.crate_qualified_path,
            "alloc::vec::into_iter::IntoIter"
        );
        assert_eq!(real_vec.diagnostic_item, Some(Collection::Vec));
        let (local_iter, _, _, _) = &callbacks.results[3];
        assert!(local_iter.is_local);
        assert_eq!(
            local_iter.crate_qualified_path,
            "trust_wp_collect_gate_test::alloc::vec::IntoIter"
        );
        assert_eq!(local_iter.diagnostic_item, None);
        let (_, local_vec, _, _) = &callbacks.results[4];
        assert!(local_vec.is_local);
        assert_eq!(local_vec.diagnostic_item, None);
    }

    #[test]
    fn element_args_must_agree() {
        assert!(element_args_agree(&["u32"], &["u32", "Global"], 1));
        assert!(!element_args_agree(&["u32"], &["u64"], 1));
        assert!(element_args_agree(&["K", "V"], &["K", "V", "S"], 2));
        assert!(!element_args_agree(&["K", "V"], &["K", "W", "S"], 2));
        assert!(!element_args_agree(&["K"], &["K", "V"], 2));
        assert!(!element_args_agree::<&str>(&[], &[], 1));
    }
}
