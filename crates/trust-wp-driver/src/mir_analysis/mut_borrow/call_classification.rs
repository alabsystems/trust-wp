// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-site classification for mutable borrow analysis.
//!
//! Classifies function calls by kind (Fn-trait, IndexMut, Snapshot) to
//! determine how the mut-borrow extractor should handle them.

use rustc_middle::{
    mir::{Body, Operand},
    ty::{TyCtxt, TyKind},
};

/// Fn-trait method paths that must bail the mut-borrow extractor.
///
/// Note: `Fn::call` is excluded because it takes `&self` (shared reference)
/// and cannot mutate captured state. Only `FnMut::call_mut` and
/// `FnOnce::call_once` can modify the closure environment. Including
/// `Fn::call` here caused `proof_assert!` closures (which use `Fn::call`)
/// to abort branch extraction, preventing correct conditional final-value
/// tracking in closures like `09_fnonce_resolve.rs`. (#2318)
const FN_TRAIT_MUTATING_METHODS: &[&str] = &[
    "core::ops::FnMut::call_mut",
    "std::ops::FnMut::call_mut",
    "core::ops::FnOnce::call_once",
    "std::ops::FnOnce::call_once",
];

/// All Fn-trait method paths (including non-mutating `Fn::call`).
const FN_TRAIT_ALL_METHODS: &[&str] = &[
    "core::ops::Fn::call",
    "std::ops::Fn::call",
    "core::ops::FnMut::call_mut",
    "std::ops::FnMut::call_mut",
    "core::ops::FnOnce::call_once",
    "std::ops::FnOnce::call_once",
];

/// Check whether a call's arguments include any `&mut` references or the call
/// is a mutating Fn-trait method, indicating the call may mutate tracked
/// parameters.
///
/// Returns true (bail) when:
/// 1. Any argument has `&mut T` type — might modify tracked params.
/// 2. The call target is a mutating Fn-trait method (`FnMut::call_mut`,
///    `FnOnce::call_once`) — these need identity-final-value synthesis which
///    only triggers when `mut_borrow_body` is `None`. (#537)
///
/// Note: `Fn::call` is intentionally excluded from check 2 because it takes
/// `&self` (shared reference) and cannot mutate the closure environment.
/// `proof_assert!` closures use `Fn::call`, and including it here caused
/// branch extraction to abort on `proof_assert!` calls, preventing correct
/// conditional final-value tracking. (#2318)
pub(super) fn call_may_mutate_params(
    tcx: TyCtxt<'_>,
    args: &[rustc_span::Spanned<Operand<'_>>],
    body: &Body<'_>,
    func: &Operand<'_>,
) -> bool {
    // Check 1: any argument with &mut type — might modify tracked params
    for arg in args {
        let local = match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => place.local,
            Operand::Constant(_) | Operand::RuntimeChecks(_) => continue,
        };
        let ty = body.local_decls[local].ty;
        if let TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut) = ty.kind() {
            return true;
        }
    }
    // Check 2: mutating Fn-trait calls via DefId path inspection.
    // Only FnMut::call_mut and FnOnce::call_once are included here;
    // Fn::call (shared reference) is non-mutating and must NOT bail. (#2318)
    if is_fn_trait_mutating_call(tcx, func) {
        return true;
    }
    false
}

/// Check if a function call targets any Fn-trait method by inspecting the
/// callee's `DefId` path.
///
/// This correctly detects `Fn::call`, `FnMut::call_mut`, and
/// `FnOnce::call_once` regardless of whether the receiver is a concrete
/// closure type or a generic `F: Fn(...)` type parameter.
pub(super) fn is_fn_trait_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    if let Operand::Constant(deref!(constant)) = func {
        if let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() {
            // Refusal-direction classifier (an Fn-trait call bails the
            // tracker), so a lookalike may only make results stricter.
            let path = tcx.def_path_str(*def_id);
            return FN_TRAIT_ALL_METHODS.iter().any(|m| path == *m);
        }
    }
    false
}

/// Check if a function call targets a *mutating* Fn-trait method.
///
/// Returns `true` for `FnMut::call_mut` and `FnOnce::call_once`, which take
/// `&mut self` or `self` respectively and may modify the closure environment.
/// Returns `false` for `Fn::call`, which takes `&self` (shared reference)
/// and cannot mutate captured state.
///
/// Used by `call_may_mutate_params` to avoid bailing on non-mutating
/// `proof_assert!` closures that call through `Fn::call`. (#2318)
pub(super) fn is_fn_trait_mutating_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    if let Operand::Constant(deref!(constant)) = func {
        if let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() {
            // Refusal-direction classifier (a mutating call bails the
            // tracker), so a lookalike may only make results stricter: keep
            // matching non-std items too.
            let path = tcx.def_path_str(*def_id);
            return FN_TRAIT_MUTATING_METHODS.iter().any(|m| path == *m);
        }
    }
    false
}

/// Check if a function call targets an `IndexMut::index_mut` method.
///
/// Returns the resolved `DefId` path if matched, so the caller can use it
/// for spec lookup. Matches both UFCS-qualified paths (e.g.,
/// `<Vec as IndexMut>::index_mut`) and plain paths (e.g., `Vec::index_mut`).
/// (#2124 Phase 4)
pub(super) fn is_index_mut_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    if let Operand::Constant(deref!(constant)) = func {
        if let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() {
            // Provenance: suffix match; only library `index_mut` impls have
            // the modelled spec-driven advancement.
            if !crate::provenance::is_builtin_provider(tcx, *def_id) {
                return false;
            }
            let path = tcx.def_path_str(*def_id);
            // Match any IndexMut::index_mut path — both concrete types and
            // trait-qualified paths.
            let stripped = strip_generics(&path);
            return stripped.ends_with("::index_mut")
                && (stripped.contains("IndexMut") || stripped.contains("::index_mut"));
        }
    }
    false
}

/// Check if a function call targets `Box::new` (or equivalent `alloc::boxed::Box::new`).
///
/// Returns `true` when the callee is `Box::new`, which creates a heap-allocated
/// wrapper around its single argument. For mutable borrow tracking, `Box::new`
/// is a transparent wrapper that preserves the identity of its argument — if the
/// argument reborrows a `&mut` parameter, the Box wrapping that reborrow still
/// aliases the same mutable reference. (#2318)
pub(super) fn is_box_new_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    if let Operand::Constant(deref!(constant)) = func {
        if let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() {
            // Provenance: `::Box::new` is a suffix match; only the real
            // `alloc::boxed::Box::new` is an identity-preserving wrapper.
            if !crate::provenance::is_std_item(tcx, *def_id) {
                return false;
            }
            let path = tcx.def_path_str(*def_id);
            let stripped = strip_generics(&path);
            return stripped == "Box::new"
                || stripped.ends_with("::Box::new")
                || stripped == "alloc::boxed::Box::new"
                || stripped == "std::boxed::Box::new";
        }
    }
    false
}

/// Check if a function call targets `Snapshot::capture` by inspecting the
/// callee's `DefId` path. (#547)
///
/// Matches both the full module path (`trust_wp_std::ghost::Snapshot::capture`)
/// and the re-export path (`trust_wp_std::Snapshot::capture`), with or without
/// generic parameters (e.g., `Snapshot::<i32>::capture`).
pub(super) fn is_snapshot_capture_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    if let Operand::Constant(deref!(constant)) = func {
        if let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() {
            // Provenance: only the spec library's capture freezes its argument.
            if !crate::provenance::is_spec_library_item(tcx, *def_id) {
                return false;
            }
            let path = tcx.def_path_str(*def_id);
            // Strip generic parameters for matching:
            // "Snapshot::<i32>::capture" -> "Snapshot::capture"
            let stripped = strip_generics(&path);
            return stripped.ends_with("::Snapshot::capture")
                // Type-directed `snapshot!` capture dispatch (bug/869): the
                // SEMANTIC capture is `snapshot_capture_select(&(expr))`, whose
                // sole inline `&(expr)` argument carries the captured place
                // exactly like `Snapshot::capture(&expr)`. The argument-less
                // `.capture()` tail is a pure identity and is NOT a capture.
                || stripped.ends_with("::snapshot_capture_select");
        }
    }
    false
}

/// Strip generic parameters from a path string.
/// E.g., `"Foo::<T>::bar::<U>"` -> `"Foo::bar"`.
pub(in crate::mir_analysis) fn strip_generics(path: &str) -> String {
    let mut result = String::with_capacity(path.len());
    let mut depth: u32 = 0;
    let chars: Vec<char> = path.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        match chars[i] {
            ':' if i + 2 < chars.len() && chars[i + 1] == ':' && chars[i + 2] == '<' => {
                // Skip `::` before `<`
                i += 2;
            }
            '<' => {
                depth += 1;
                i += 1;
            }
            '>' => {
                depth = depth.saturating_sub(1);
                i += 1;
            }
            c if depth == 0 => {
                result.push(c);
                i += 1;
            }
            _ => {
                i += 1;
            }
        }
    }
    result
}
