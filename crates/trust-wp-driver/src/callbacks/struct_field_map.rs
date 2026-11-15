// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Struct field name → positional index mapping.
//!
//! The contract parser produces `__trust_wp_field_<name>` for named field access,
//! while MIR extraction produces `__trust_wp_tuple_get_<index>`. This module builds
//! the mapping between the two representations by inspecting struct ADT definitions
//! in the function signature.

use std::collections::{HashMap, HashSet};

use rustc_hir::{
    def::Res,
    def_id::{DefId, LocalDefId},
    intravisit::Visitor,
};
use rustc_middle::{
    hir::nested_filter,
    ty::{AdtDef, Ty, TyCtxt, TypeckResults, VariantDef},
};
use trust_wp_ay::type_constants_for_int;

/// Extract the integer type name from a def_path for type constant resolution.
///
/// For inherent integer methods like `i32::checked_add` or `u8::saturating_sub`,
/// this extracts the type prefix (`"i32"`, `"u8"`) so the driver can call
/// `type_constants_for_int` to populate `Self::MIN`/`Self::MAX` constants. (#688)
///
/// Supports both short-form paths (`i32::checked_add`) and fully-qualified
/// forms (`core::num::i32::checked_add`, `core::num::<impl i32>::checked_add`).
/// Returns `None` if no known integer type token is found.
pub(super) fn extract_int_type_from_path(def_path: &str) -> Option<&str> {
    // Fast path for short-form entries like "i32::checked_add".
    if let Some(prefix) = def_path.split("::").next() {
        if type_constants_for_int(prefix).is_some() {
            return Some(prefix);
        }
    }

    // Fallback for fully-qualified forms. We scan each path segment for an
    // integer token, handling shapes like "core::num::i32::checked_add" and
    // "core::num::<impl i32>::checked_add".
    for segment in def_path.rsplit("::") {
        if type_constants_for_int(segment).is_some() {
            return Some(segment);
        }

        for token in segment.split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_')) {
            if !token.is_empty() && type_constants_for_int(token).is_some() {
                return Some(token);
            }
        }
    }

    None
}

/// Build a map from struct field names to positional indices for all struct
/// types that appear in the given function signature.
///
/// Used by the named field access rewrite pass to translate `__trust_wp_field_<name>`
/// (from the contract parser) into `__trust_wp_tuple_get_<index>` (matching MIR extraction).
pub(super) fn build_struct_field_map(tcx: TyCtxt<'_>, def_id: DefId) -> HashMap<String, usize> {
    let mut field_map = HashMap::new();
    let mut ambiguous_fields = HashSet::new();
    let mut visited = HashSet::new();
    // Closures don't have fn_sig(); their parameters are captures, not struct args.
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return field_map;
    }
    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_norm_wip();
    let sig = tcx.liberate_late_bound_regions(def_id, sig);
    for ty in sig.inputs() {
        collect_struct_fields_from_ty(
            tcx,
            *ty,
            &mut field_map,
            &mut ambiguous_fields,
            &mut visited,
            0,
        );
    }
    collect_struct_fields_from_ty(
        tcx,
        sig.output(),
        &mut field_map,
        &mut ambiguous_fields,
        &mut visited,
        0,
    );
    field_map
}

fn record_struct_field_index(
    field_map: &mut HashMap<String, usize>,
    ambiguous_fields: &mut HashSet<String>,
    field_name: &str,
    index: usize,
) {
    if ambiguous_fields.contains(field_name) {
        return;
    }
    match field_map.get(field_name) {
        Some(existing) if *existing != index => {
            field_map.remove(field_name);
            ambiguous_fields.insert(field_name.to_string());
        }
        Some(_) => {}
        None => {
            field_map.insert(field_name.to_string(), index);
        }
    }
}

fn collect_struct_fields_from_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    field_map: &mut HashMap<String, usize>,
    ambiguous_fields: &mut HashSet<String>,
    visited: &mut HashSet<DefId>,
    depth: usize,
) {
    let inner_ty = ty.peel_refs();
    match inner_ty.kind() {
        rustc_middle::ty::TyKind::Adt(adt_def, substs) => {
            if !adt_def.is_struct() {
                // Still recurse into generic type arguments for non-struct ADTs
                // (e.g., Vec<&mut SumTo10> — Vec is a struct, but enums could
                // also carry user struct types in their generic parameters).
                for arg in *substs {
                    if let Some(arg_ty) = arg.as_type() {
                        collect_struct_fields_from_ty(
                            tcx,
                            arg_ty,
                            field_map,
                            ambiguous_fields,
                            visited,
                            depth + 1,
                        );
                    }
                }
                return;
            }
            let adt_id = adt_def.did();
            // Recurse through local nested structs only. Traversing non-local nested
            // structs (for example `Vec`) can pollute the map with implementation
            // detail field names and create false ambiguities for user fields.
            if depth > 0 && !adt_id.is_local() {
                // Still recurse into generic type arguments so that user-defined
                // structs buried in non-local containers (e.g., SumTo10 inside
                // Vec<&mut SumTo10>) are discovered. (#1572)
                for arg in *substs {
                    if let Some(arg_ty) = arg.as_type() {
                        collect_struct_fields_from_ty(
                            tcx,
                            arg_ty,
                            field_map,
                            ambiguous_fields,
                            visited,
                            depth + 1,
                        );
                    }
                }
                return;
            }
            if !visited.insert(adt_id) {
                return;
            }
            if let Some(variant) = adt_def.variants().iter().next() {
                for (idx, field) in variant.fields.iter().enumerate() {
                    let field_name = field.name.to_string();
                    record_struct_field_index(field_map, ambiguous_fields, &field_name, idx);
                    let field_ty = field.ty(tcx, *substs).skip_norm_wip();
                    collect_struct_fields_from_ty(
                        tcx,
                        field_ty,
                        field_map,
                        ambiguous_fields,
                        visited,
                        depth + 1,
                    );
                }
            }
            // Also recurse into generic type arguments to discover user structs
            // in container types (e.g., Vec<&mut SumTo10>). (#1572)
            for arg in *substs {
                if let Some(arg_ty) = arg.as_type() {
                    collect_struct_fields_from_ty(
                        tcx,
                        arg_ty,
                        field_map,
                        ambiguous_fields,
                        visited,
                        depth + 1,
                    );
                }
            }
            visited.remove(&adt_id);
        }
        rustc_middle::ty::TyKind::Tuple(fields) => {
            for field_ty in *fields {
                collect_struct_fields_from_ty(
                    tcx,
                    field_ty,
                    field_map,
                    ambiguous_fields,
                    visited,
                    depth + 1,
                );
            }
        }
        rustc_middle::ty::TyKind::Array(elem_ty, _) | rustc_middle::ty::TyKind::Slice(elem_ty) => {
            collect_struct_fields_from_ty(
                tcx,
                *elem_ty,
                field_map,
                ambiguous_fields,
                visited,
                depth + 1,
            );
        }
        _ => {}
    }
}

// ── declaration-order field lists, keyed by constructor spelling ───────────
//
// `build_struct_field_map` answers "what index does a field NAME have", keyed
// by the bare name across every struct in one signature. That is the right
// shape for rewriting a field ACCESS (`x.inner`), where the contract text
// carries no type. It is the WRONG shape for a named-field PATTERN or
// CONSTRUCTOR: those name a specific type, they may name an ENUM VARIANT
// (which `collect_struct_fields_from_ty` skips — `!adt_def.is_struct()`
// returns early), and two unrelated types may share a field name at different
// indices, which the flat map can only answer by erasing both.
//
// The map below is keyed by the constructor SPELLING a contract may use
// (`C`, `E::C`, `m::E::C`, …) and answers with that constructor's fields in
// DECLARATION order. A spelling that two different constructors answer to with
// different field lists resolves to `None` — ambiguous, and therefore refused
// rather than guessed. Creusot needs none of this: it reads THIR, where rustc
// has already resolved every pattern field to a `FieldIdx`
// (`PatternKind::Constructor(variant, Box<[(FieldIdx, Pattern)]>)` in
// reference/creusot/creusot/src/translation/pearlite.rs). trust-wp parses
// contract TEXT, so the index has to be recovered here or the pattern refused.

/// Declaration-ordered field names for every named-field constructor a
/// contract may spell, keyed by every spelling that reaches it.
pub(in crate::callbacks) type CtorFieldOrder = HashMap<String, CtorCandidates>;

/// Cap on candidate lists kept per spelling.
///
/// The cap bounds the TABLE. It must never bound the ANSWER — see
/// [`CtorCandidates`].
const MAX_CTOR_CANDIDATES: usize = 8;

/// ONE constructor's field names, in DECLARATION order, copied out of rustc's
/// own `VariantDef`.
///
/// The inner `Vec` is private and [`DeclaredFields::from_variant`] is the only
/// way to build one outside tests, so a field list that did not come from a
/// declaration cannot be made at all. That matters because
/// `contract_rewrite::placement::FieldPlacement` — the only thing that turns a
/// pattern's field names into declaration indices — takes one of these: the
/// type carries the guarantee, so a later edit cannot reintroduce a guessed
/// placement without first inventing a declaration, which it cannot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::callbacks) struct DeclaredFields(Vec<String>);

impl DeclaredFields {
    /// The production constructor. rustc has already resolved the ADT and
    /// ordered its fields; this only copies that order out.
    ///
    /// `None` when the variant has no braced fields for a contract to spell:
    /// a tuple constructor names its fields `0`, `1`, … and is positional
    /// already, and a unit constructor has none.
    fn from_variant(variant: &rustc_middle::ty::VariantDef) -> Option<Self> {
        if variant.fields.is_empty()
            || !variant
                .fields
                .iter()
                .all(|f| !f.name.as_str().starts_with(|c: char| c.is_ascii_digit()))
        {
            return None;
        }
        Some(Self(
            variant.fields.iter().map(|f| f.name.to_string()).collect(),
        ))
    }

    /// The declared names, in declaration order.
    pub(in crate::callbacks) fn names(&self) -> &[String] {
        &self.0
    }

    /// Test-only: the declaration a unit-test fixture states directly, in
    /// place of the `VariantDef` a compiled crate would supply. Never
    /// compiled into the driver.
    #[cfg(test)]
    pub(in crate::callbacks) fn from_names_for_test(names: &[&str]) -> Self {
        Self(names.iter().map(|n| (*n).to_string()).collect())
    }
}

/// Every DISTINCT field list that answers to one constructor spelling, and
/// whether the table had to turn one away.
///
/// One entry is the common case. Several entries mean the spelling alone does
/// not pick a constructor — an unqualified `C` when two enums both declare a
/// variant `C`, say. That is not automatically a refusal: what a pattern needs
/// is where its fields SIT, so several candidates that agree on the placement
/// of the fields actually written resolve fine, and only candidates that
/// DISAGREE force the refusal.
///
/// Candidates arrive two ways, and the distinction is provenance, not
/// authority:
///
/// * [`Self::record_resolved`] — rustc RESOLVED this very spelling, in a
///   clause it type-checked, so this candidate is certainly one of the things
///   the spelling can mean here.
/// * [`Self::record_declared`] — some declaration in scope answers to this
///   spelling (its `def_path_str`, a `::`-suffix of it, an alias, `Self`).
///   That is a candidate, not an identification.
///
/// A resolved candidate does NOT displace the declared ones, and that is
/// deliberate. It would be tempting: a resolved answer is exact, and letting
/// it silence a crate-wide namesake would recover a proof the namesake
/// refuses. But the clauses merged into one function's contract do not all
/// come from the two places this driver harvests (its own body and its direct
/// callees') — a type invariant, a trait declaration's clause or an extern
/// spec contributes text too — so "resolved somewhere in this function's
/// clauses" is not "resolved for THIS occurrence". Preferring it would be a
/// guess about provenance, and a guess is the thing this table exists to
/// remove. Adding candidates can only move the outcome toward a refusal, so
/// this direction is the one that cannot misplace a field.
///
/// `capped` is the reason this is a struct rather than a bare `Vec`. A
/// candidate list dropped for exceeding [`MAX_CTOR_CANDIDATES`] may be the
/// REAL constructor, and then every surviving candidate is a decoy: they can
/// agree with each other perfectly and still place the pattern's fields at
/// indices that are not this constructor's — the very misplacement this table
/// exists to refuse (D-31), reopened by the table meant to close it
/// (s82v2_ctor_candidate_cap.rs). So the cap RECORDS that the set is
/// incomplete and `place_named_fields` refuses on it. A bounded table may
/// cost completeness; it may not cost soundness.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(in crate::callbacks) struct CtorCandidates {
    lists: Vec<DeclaredFields>,
    capped: bool,
}

impl CtorCandidates {
    /// Record the constructor rustc resolved this spelling to in a clause it
    /// type-checked.
    ///
    /// This is what makes a spelling no table here can CONSTRUCT
    /// (`self::E::C`, `super::super::E::C`, a re-export, an alias) placeable
    /// at all. It adds a candidate; it does not overrule the others — see the
    /// type's own documentation for why that direction is the sound one.
    pub(in crate::callbacks) fn record_resolved(&mut self, fields: DeclaredFields) {
        self.push(fields);
    }

    /// Record one constructor that ANSWERS to this spelling by declaration.
    pub(in crate::callbacks) fn record_declared(&mut self, fields: DeclaredFields) {
        self.push(fields);
    }

    /// A list already present is a no-op — the same constructor reached by two
    /// spellings, or two constructors that happen to declare the same fields
    /// in the same order, are indistinguishable to a pattern and need no
    /// second entry. A DISTINCT list that does not fit under the cap is not
    /// stored, and marks the entry capped rather than vanishing.
    fn push(&mut self, fields: DeclaredFields) {
        if self.lists.contains(&fields) {
            return;
        }
        if self.lists.len() >= MAX_CTOR_CANDIDATES {
            self.capped = true;
            return;
        }
        self.lists.push(fields);
    }

    /// The candidates kept. Sound to resolve against only while
    /// [`Self::is_capped`] is false.
    pub(in crate::callbacks) fn lists(&self) -> &[DeclaredFields] {
        &self.lists
    }

    /// True when a distinct field list was turned away by the cap, so these
    /// are not known to be all the constructors answering to the spelling.
    pub(in crate::callbacks) fn is_capped(&self) -> bool {
        self.capped
    }
}

thread_local! {
    /// The crate-wide half of the map, which does not vary per function.
    static CTOR_FIELD_ORDER_CACHE: std::cell::RefCell<
        Option<(rustc_span::def_id::StableCrateId, std::rc::Rc<CtorFieldOrder>)>,
    > = const { std::cell::RefCell::new(None) };
}

/// Record `variant`'s declaration-ordered field names under every spelling a
/// contract could use for it: the full path, each `::`-suffix of it, and the
/// `crate::`-qualified form.
fn record_ctor_field_order(tcx: TyCtxt<'_>, out: &mut CtorFieldOrder, ctor_def_id: DefId) {
    let Some(variant) = variant_of_ctor(tcx, ctor_def_id) else {
        return;
    };
    let Some(fields) = DeclaredFields::from_variant(variant) else {
        return;
    };
    let full = tcx.def_path_str(ctor_def_id);
    for spelling in path_spellings(&full) {
        out.entry(spelling)
            .or_default()
            .record_declared(fields.clone());
    }
}

/// Every spelling a contract may write for the path `full`: the whole path,
/// each `::`-suffix of it, and the `crate::`-qualified form.
fn path_spellings(full: &str) -> Vec<String> {
    let segments: Vec<&str> = full.split("::").collect();
    let mut spellings: Vec<String> = Vec::with_capacity(segments.len() + 1);
    for start in 0..segments.len() {
        spellings.push(segments[start..].join("::"));
    }
    spellings.push(format!("crate::{full}"));
    spellings
}

/// The `VariantDef` a struct/union/variant `DefId` denotes, if any.
fn variant_of_ctor(tcx: TyCtxt<'_>, def_id: DefId) -> Option<&rustc_middle::ty::VariantDef> {
    match tcx.def_kind(def_id) {
        rustc_hir::def::DefKind::Struct | rustc_hir::def::DefKind::Union => {
            tcx.adt_def(def_id).variants().iter().next()
        }
        rustc_hir::def::DefKind::Variant => {
            let enum_did = tcx.parent(def_id);
            tcx.adt_def(enum_did)
                .variants()
                .iter()
                .find(|v| v.def_id == def_id)
        }
        _ => None,
    }
}

// ── spellings that are NOT the type's canonical path ───────────────────────
//
// The canonical recording above keys a constructor by `def_path_str` and its
// suffixes. A contract may legitimately spell the SAME constructor a way that
// path never produces, and rustc has already resolved that spelling when it
// type-checked the clause:
//
//     use m::E as F;        // `F::C`    — a renamed import
//     type F = E;           // `F::C`    — a type alias
//     use m::E::C as D;     // `D`       — a renamed variant import
//     impl E { ... }        // `Self::C` — `Self` inside an impl
//     impl S { ... }        // `Self`    — ditto, for a braced struct
//
// Refusing those is not fail-closed caution, it is a refusal of ordinary
// declaration-ordered code: `Self::Variant { .. }` inside `impl Enum` is
// idiomatic specification text. So each alias records the constructors it
// reaches under the alias spelling as well.
//
// Only spellings that still CONTAIN the alias (or `Self`) segment are
// recorded. The bare `C` suffix is deliberately left alone: it belongs to the
// canonical recording, and adding a foreign constructor under it could turn
// an unambiguous local name into a refusal — trading one refusal of ordinary
// code for another.

/// Record every named-field constructor of `adt_def` under each TYPE path in
/// `type_paths` — an enum variant as `<path>::<Variant>`, a braced struct or
/// union as `<path>` itself.
fn record_ctor_field_order_under_type_paths(
    out: &mut CtorFieldOrder,
    adt_def: rustc_middle::ty::AdtDef<'_>,
    type_paths: &[String],
) {
    let is_enum = adt_def.is_enum();
    for variant in adt_def.variants() {
        let Some(fields) = DeclaredFields::from_variant(variant) else {
            continue;
        };
        for type_path in type_paths {
            let spelling = if is_enum {
                format!("{type_path}::{}", variant.name)
            } else {
                type_path.clone()
            };
            out.entry(spelling)
                .or_default()
                .record_declared(fields.clone());
        }
    }
}

/// The `AdtDef` a `type` alias ultimately names, if it names one.
fn ty_alias_adt(tcx: TyCtxt<'_>, alias_def_id: DefId) -> Option<rustc_middle::ty::AdtDef<'_>> {
    let ty = tcx
        .type_of(alias_def_id)
        .instantiate_identity()
        .skip_norm_wip();
    match ty.peel_refs().kind() {
        rustc_middle::ty::TyKind::Adt(adt_def, _) => Some(*adt_def),
        _ => None,
    }
}

/// The paths a local alias named `alias`, declared in module `parent`, can be
/// written as: the module-qualified path, every `::`-suffix of it down to the
/// alias itself, and the `crate::` form.
fn alias_path_spellings(tcx: TyCtxt<'_>, parent: Option<DefId>, alias: &str) -> Vec<String> {
    let prefix = parent.filter(|p| {
        *p != rustc_hir::def_id::CRATE_DEF_ID.to_def_id()
            && matches!(tcx.def_kind(*p), rustc_hir::def::DefKind::Mod)
    });
    match prefix {
        Some(p) => {
            let module = tcx.def_path_str(p);
            if module.is_empty() {
                path_spellings(alias)
            } else {
                path_spellings(&format!("{module}::{alias}"))
            }
        }
        None => path_spellings(alias),
    }
}

/// Record whatever constructors the resolution `res` of a renamed import
/// reaches, under the import's own alias spellings.
fn record_imported_ctor_field_order(
    tcx: TyCtxt<'_>,
    out: &mut CtorFieldOrder,
    res: rustc_hir::def::Res,
    alias_paths: &[String],
) {
    let rustc_hir::def::Res::Def(kind, did) = res else {
        return;
    };
    match kind {
        rustc_hir::def::DefKind::Struct
        | rustc_hir::def::DefKind::Union
        | rustc_hir::def::DefKind::Enum => {
            record_ctor_field_order_under_type_paths(out, tcx.adt_def(did), alias_paths);
        }
        rustc_hir::def::DefKind::TyAlias => {
            if let Some(adt_def) = ty_alias_adt(tcx, did) {
                record_ctor_field_order_under_type_paths(out, adt_def, alias_paths);
            }
        }
        rustc_hir::def::DefKind::Variant => {
            // `use m::E::C as D;` — the alias IS the constructor path.
            let Some(variant) = variant_of_ctor(tcx, did) else {
                return;
            };
            let Some(fields) = DeclaredFields::from_variant(variant) else {
                return;
            };
            for spelling in alias_paths {
                out.entry(spelling.clone())
                    .or_default()
                    .record_declared(fields.clone());
            }
        }
        _ => {}
    }
}

/// Record the constructors every single-name `use` item in the crate reaches,
/// under the name the import gives them.
///
/// A non-renaming `use` records exactly what the canonical path already did,
/// which `CtorCandidates::record` deduplicates, so there is no need to test
/// for a rename first.
fn record_use_alias_ctor_field_order(tcx: TyCtxt<'_>, out: &mut CtorFieldOrder) {
    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(item_id);
        let use_did = item.owner_id.to_def_id();
        for (path, kind) in crate::hir_use::item_use_leaves(item) {
            let rustc_hir::UseKind::Single(ident) = kind else {
                continue;
            };
            let alias_paths =
                alias_path_spellings(tcx, tcx.opt_parent(use_did), ident.name.as_str());
            for res in [path.res.type_ns, path.res.value_ns].into_iter().flatten() {
                record_imported_ctor_field_order(tcx, out, res, &alias_paths);
            }
        }
    }
}

/// The `impl` block a definition sits in, walking out through closures and
/// nested items. `None` for a free function, and for a trait's own default
/// body — where `Self` is a type parameter and genuinely cannot be resolved.
fn enclosing_impl(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    let mut current = def_id;
    loop {
        if matches!(tcx.def_kind(current), rustc_hir::def::DefKind::Impl { .. }) {
            return Some(current);
        }
        current = tcx.opt_parent(current)?;
    }
}

/// Record one `impl`'s self-type constructors under `Self` / `Self::V`.
fn record_impl_self_ctor_field_order(
    tcx: TyCtxt<'_>,
    out: &mut CtorFieldOrder,
    impl_did: DefId,
    self_spelling: &[String],
) {
    let self_ty = tcx.type_of(impl_did).instantiate_identity().skip_norm_wip();
    let rustc_middle::ty::TyKind::Adt(adt_def, _) = self_ty.peel_refs().kind() else {
        return;
    };
    record_ctor_field_order_under_type_paths(out, *adt_def, self_spelling);
}

/// The functions `def_id`'s body calls directly.
///
/// A CALLEE's contract does not stay with the callee: its `requires` becomes
/// an obligation and its `ensures` an assumption ON THIS FUNCTION, and the
/// whole merged contract is rewritten once, here, in THIS function's
/// environment. So `Self` in a callee's clause has to resolve here too — see
/// `record_self_ctor_field_order`.
fn direct_callees(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<DefId> {
    let Some(local_def_id) = def_id.as_local() else {
        return Vec::new();
    };
    if !tcx.is_mir_available(def_id) {
        return Vec::new();
    }
    // A bodyless trait method declaration reports MIR available (rustc makes an
    // unreachable shim) but has no HIR body, and asking for one panics.
    if let rustc_hir::Node::TraitItem(item) = tcx.hir_node_by_def_id(local_def_id) {
        if matches!(
            item.kind,
            rustc_hir::TraitItemKind::Fn(_, rustc_hir::TraitFn::Required(_))
        ) {
            return Vec::new();
        }
    }
    let Some(body_with_facts) = super::try_get_body_with_context(tcx, local_def_id) else {
        return Vec::new();
    };
    let body = crate::mir_analysis::get_mir_body(&body_with_facts);
    let mut callees = Vec::new();
    for bb_data in body.basic_blocks.iter() {
        if let rustc_middle::mir::TerminatorKind::Call { func, .. } = &bb_data.terminator().kind {
            if let rustc_middle::mir::Operand::Constant(deref!(constant)) = func {
                if let rustc_middle::ty::TyKind::FnDef(callee, _) = constant.const_.ty().kind() {
                    callees.push(*callee);
                }
            }
        }
    }
    callees
}

/// Record every `Self` a contract rewritten for `def_id` may legitimately
/// spell: the enclosing `impl`'s self type, and the self type of every impl
/// this function CALLS into.
///
/// The second half is not generosity. `#[requires]` on a method spelled with
/// `Self::C` reaches its callers as a call OBLIGATION, and the caller's
/// contract — callee clauses and all — is rewritten once in the caller's
/// environment. A free function that calls such a method has no enclosing
/// impl, so without the callees' `Self` the clause is refused and the caller
/// loses a row it could prove (s82v2_selfpath_callee_control.rs). This is the
/// same-code/same-environment hazard: a grant and the obligation it came from
/// must be read in the environment that WROTE them.
///
/// Several impls contributing a `Self::C` that place the fields differently
/// is a genuine ambiguity here — nothing in the merged contract says which
/// clause came from which callee — so it refuses, as any disagreement does.
fn record_self_ctor_field_order(tcx: TyCtxt<'_>, out: &mut CtorFieldOrder, def_id: DefId) {
    let self_spelling = ["Self".to_string()];
    if let Some(impl_did) = enclosing_impl(tcx, def_id) {
        record_impl_self_ctor_field_order(tcx, out, impl_did, &self_spelling);
    }
    for callee in direct_callees(tcx, def_id) {
        if let Some(impl_did) = tcx.impl_of_assoc(callee) {
            record_impl_self_ctor_field_order(tcx, out, impl_did, &self_spelling);
        }
    }
}

// ── the spelling rustc RESOLVED, instead of a spelling this file invented ──
//
// Everything above keys a constructor by a path THIS CODE constructs:
// `def_path_str` and its `::`-suffixes, `crate::`, alias spellings, `Self`.
// That is an enumeration, and an enumeration is only ever as complete as its
// last author. `self::E::C` and `super::E::C` are spellings rustc resolves
// that no rule here produces, and a spelling the table lacks must become a
// refusal, never a MISPLACEMENT: a lookup that misses and falls back to a flat
// field-name map places the fields by a guess (D-31). Adding the two missing
// spellings to the enumeration would only move the boundary to the next one.
//
// rustc has already done this work. `trust-wp-macros` puts every clause,
// lowered to Rust, inside a `__trust_wp_spec_tc` closure that rustc
// TYPE-CHECKS (see `callbacks::spec_typecheck`) — which is why a clause naming
// a field the variant does not declare is an E0027 before the driver ever
// runs. So for every named-field pattern and struct expression in a clause,
// the constructor is already resolved, with the author's own module, imports,
// aliases, re-exports and `Self` in scope, by the resolver rather than by a
// spelling table.
//
// This walks those type-checked clauses and records the variant RUSTC
// resolved, keyed by the spelling as written. The key is still text, and has
// to be: the contract the driver rewrites is parsed from the clause TEXT, so
// the two sides meet by name. But the key does not have to CARRY the answer —
// a spelling this file cannot construct still resolves, and a spelling it can
// construct is answered by the resolver rather than by the construction rule.
//
// Scope: this function's own clauses and those of the functions it calls
// directly. A callee's `requires` becomes an obligation ON THIS FUNCTION and
// its `ensures` an assumption here, and the merged contract is rewritten once,
// in this environment — so a callee's spelling has to resolve here too. That
// is the same scope `record_self_ctor_field_order` already needed, for the
// same reason.

/// The `VariantDef` that `res` denotes for a pattern or expression of type
/// `adt`, or `None` when the resolution is not one that names a constructor.
///
/// Deliberately total: an unexpected resolution declines to answer, where
/// rustc's own `AdtDef::variant_of_res` would ICE. Declining costs a
/// completeness note; guessing costs soundness.
fn variant_of_resolution<'tcx>(adt: AdtDef<'tcx>, res: Res) -> Option<&'tcx VariantDef> {
    match res {
        Res::Def(rustc_hir::def::DefKind::Variant, did) => {
            adt.variants().iter().find(|v| v.def_id == did)
        }
        Res::Def(rustc_hir::def::DefKind::Ctor(..), did) => {
            adt.variants().iter().find(|v| v.ctor_def_id() == Some(did))
        }
        Res::Def(
            rustc_hir::def::DefKind::Struct
            | rustc_hir::def::DefKind::Union
            | rustc_hir::def::DefKind::TyAlias
            | rustc_hir::def::DefKind::AssocTy,
            _,
        )
        | Res::SelfCtor(..)
        | Res::SelfTyParam { .. }
        | Res::SelfTyAlias { .. } => (!adt.is_enum()).then(|| adt.non_enum_variant()),
        _ => None,
    }
}

/// True when `text` has the shape the contract parser records for a
/// constructor name: `::`-separated plain identifiers.
///
/// Anything else — a qualified `<T as Tr>::A::C`, a turbofish `E::<u32>::C` —
/// the contract parser does not produce either, so there is no key to record
/// it under. (Both forms fail the contract parser outright and the function
/// is refused there, before placement is reached.)
fn is_plain_path(text: &str) -> bool {
    !text.is_empty()
        && text.split("::").all(|seg| {
            let mut chars = seg.chars();
            chars.next().is_some_and(|c| c.is_alphabetic() || c == '_')
                && chars.all(|c| c.is_alphanumeric() || c == '_')
        })
}

/// Every spelling of `qpath` that the contract parser could have recorded for
/// the same path: the written segments joined by `::`, and the source text
/// with whitespace removed (which is the only route for `Self::C` and other
/// type-relative forms, where the prefix is a type rather than a segment).
///
/// Both name the SAME resolved constructor, so recording under both cannot
/// introduce an ambiguity — this is not the spelling enumeration the section
/// header warns about, which guessed at the ANSWER.
///
/// A snippet is source text, so it can in principle be text the macros
/// synthesised at the attribute's own span rather than the path the author
/// wrote. That cannot misplace a field: a key nothing in the contract text
/// spells is never looked up, and a key something else spells only ADDS a
/// candidate to that spelling — and an added candidate can only move the
/// outcome toward a refusal (see `CtorCandidates`). It is the reason the
/// additive rule there is not merely tidy.
fn written_spellings(tcx: TyCtxt<'_>, qpath: &rustc_hir::QPath<'_>) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    if let rustc_hir::QPath::Resolved(None, path) = qpath {
        let joined = path
            .segments
            .iter()
            .map(|seg| seg.ident.as_str().to_string())
            .collect::<Vec<_>>()
            .join("::");
        if is_plain_path(&joined) {
            out.push(joined);
        }
    }
    if let Ok(text) = tcx.sess.source_map().span_to_snippet(qpath.span()) {
        let compact: String = text.chars().filter(|c| !c.is_whitespace()).collect();
        if is_plain_path(&compact) && !out.contains(&compact) {
            out.push(compact);
        }
    }
    out
}

/// Walks one body and records, for every named-field pattern and struct
/// expression INSIDE a specification type-check closure, the constructor
/// rustc resolved it to.
struct SpecTcCtorVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    out: &'a mut CtorFieldOrder,
    /// Nesting depth inside `__trust_wp_spec_tc` closures. Only specification
    /// text is harvested: the function's own body is program code, and the
    /// verifier reads its constructors from MIR, not from a spelling.
    in_spec: usize,
}

impl<'tcx> SpecTcCtorVisitor<'_, 'tcx> {
    fn record(&mut self, qpath: &rustc_hir::QPath<'_>, hir_id: rustc_hir::HirId) {
        if self.in_spec == 0 {
            return;
        }
        let Some(ty) = self.typeck.node_type_opt(hir_id) else {
            return;
        };
        let Some(adt) = ty.peel_refs().ty_adt_def() else {
            return;
        };
        let Some(variant) = variant_of_resolution(adt, self.typeck.qpath_res(qpath, hir_id)) else {
            return;
        };
        let Some(fields) = DeclaredFields::from_variant(variant) else {
            return;
        };
        for spelling in written_spellings(self.tcx, qpath) {
            self.out
                .entry(spelling)
                .or_default()
                .record_resolved(fields.clone());
        }
    }
}

impl<'tcx> Visitor<'tcx> for SpecTcCtorVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
        let is_spec = super::spec_typecheck::is_spec_tc_closure_expr(self.tcx, expr);
        if is_spec {
            self.in_spec += 1;
        }
        if let rustc_hir::ExprKind::Struct(qpath, ..) = expr.kind {
            self.record(qpath, expr.hir_id);
        }
        rustc_hir::intravisit::walk_expr(self, expr);
        if is_spec {
            self.in_spec -= 1;
        }
    }

    fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
        if let rustc_hir::PatKind::Struct(ref qpath, ..) = pat.kind {
            self.record(qpath, pat.hir_id);
        }
        rustc_hir::intravisit::walk_pat(self, pat);
    }
}

/// Harvest one typeck root's specification clauses.
fn harvest_spec_tc_ctors(tcx: TyCtxt<'_>, out: &mut CtorFieldOrder, root: LocalDefId) {
    let Some(body) = tcx.hir_maybe_body_owned_by(root) else {
        return;
    };
    let typeck = tcx.typeck(root);
    let mut visitor = SpecTcCtorVisitor {
        tcx,
        typeck,
        out,
        in_spec: 0,
    };
    rustc_hir::intravisit::walk_expr(&mut visitor, body.value);
}

/// Record every constructor rustc resolved in a specification clause that
/// reaches `def_id`'s contract: this function's own, and each direct callee's.
fn record_spec_tc_resolved_ctors(tcx: TyCtxt<'_>, out: &mut CtorFieldOrder, def_id: DefId) {
    let mut roots: Vec<LocalDefId> = Vec::new();
    let push_root = |roots: &mut Vec<LocalDefId>, candidate: DefId| {
        let Some(root) = tcx.typeck_root_def_id(candidate).as_local() else {
            return;
        };
        if !roots.contains(&root) {
            roots.push(root);
        }
    };
    push_root(&mut roots, def_id);
    for callee in direct_callees(tcx, def_id) {
        push_root(&mut roots, callee);
    }
    for root in roots {
        harvest_spec_tc_ctors(tcx, out, root);
    }
}

/// Every named-field constructor the LOCAL crate declares, keyed by spelling.
fn build_local_ctor_field_order(tcx: TyCtxt<'_>) -> CtorFieldOrder {
    let mut out = CtorFieldOrder::new();
    for local_def_id in tcx.hir_crate_items(()).definitions() {
        let def_id = local_def_id.to_def_id();
        match tcx.def_kind(def_id) {
            rustc_hir::def::DefKind::Struct | rustc_hir::def::DefKind::Union => {
                record_ctor_field_order(tcx, &mut out, def_id);
            }
            rustc_hir::def::DefKind::Enum => {
                for variant in tcx.adt_def(def_id).variants() {
                    record_ctor_field_order(tcx, &mut out, variant.def_id);
                }
            }
            rustc_hir::def::DefKind::Variant => {
                record_ctor_field_order(tcx, &mut out, def_id);
            }
            rustc_hir::def::DefKind::TyAlias => {
                if let Some(adt_def) = ty_alias_adt(tcx, def_id) {
                    let alias_paths = path_spellings(&tcx.def_path_str(def_id));
                    record_ctor_field_order_under_type_paths(&mut out, adt_def, &alias_paths);
                }
            }
            _ => {}
        }
    }
    record_use_alias_ctor_field_order(tcx, &mut out);
    out
}

/// Collect the ADTs reachable from `ty` (through references, tuples, slices,
/// fields and generic arguments) so a contract may also spell a FOREIGN
/// constructor that only appears in this signature.
fn collect_ctor_field_order_from_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    out: &mut CtorFieldOrder,
    visited: &mut HashSet<DefId>,
    depth: usize,
) {
    const MAX_DEPTH: usize = 6;
    if depth > MAX_DEPTH {
        return;
    }
    let inner_ty = ty.peel_refs();
    match inner_ty.kind() {
        rustc_middle::ty::TyKind::Adt(adt_def, substs) => {
            let adt_id = adt_def.did();
            if !visited.insert(adt_id) {
                return;
            }
            for variant in adt_def.variants() {
                record_ctor_field_order(tcx, out, variant.def_id);
                for field in &variant.fields {
                    let field_ty = field.ty(tcx, *substs).skip_norm_wip();
                    collect_ctor_field_order_from_ty(tcx, field_ty, out, visited, depth + 1);
                }
            }
            for arg in *substs {
                if let Some(arg_ty) = arg.as_type() {
                    collect_ctor_field_order_from_ty(tcx, arg_ty, out, visited, depth + 1);
                }
            }
            visited.remove(&adt_id);
        }
        rustc_middle::ty::TyKind::Tuple(fields) => {
            for field_ty in *fields {
                collect_ctor_field_order_from_ty(tcx, field_ty, out, visited, depth + 1);
            }
        }
        rustc_middle::ty::TyKind::Array(elem_ty, _) | rustc_middle::ty::TyKind::Slice(elem_ty) => {
            collect_ctor_field_order_from_ty(tcx, *elem_ty, out, visited, depth + 1);
        }
        _ => {}
    }
}

/// Every named-field constructor the LOCAL crate declares, keyed by spelling
/// (cached; the local crate does not change within a driver run).
pub(super) fn build_crate_ctor_field_order(tcx: TyCtxt<'_>) -> CtorFieldOrder {
    (*cached_local_ctor_field_order(tcx)).clone()
}

fn cached_local_ctor_field_order(tcx: TyCtxt<'_>) -> std::rc::Rc<CtorFieldOrder> {
    let crate_id = tcx.stable_crate_id(rustc_hir::def_id::LOCAL_CRATE);
    CTOR_FIELD_ORDER_CACHE.with(|cache| {
        let mut slot = cache.borrow_mut();
        if let Some((cached_id, map)) = slot.as_ref() {
            if *cached_id == crate_id {
                return std::rc::Rc::clone(map);
            }
        }
        let built = std::rc::Rc::new(build_local_ctor_field_order(tcx));
        *slot = Some((crate_id, std::rc::Rc::clone(&built)));
        built
    })
}

/// Declaration-ordered field names for every named-field constructor a
/// contract on `def_id` may spell: the whole local crate, plus whatever the
/// signature reaches into other crates.
pub(super) fn build_ctor_field_order(tcx: TyCtxt<'_>, def_id: DefId) -> CtorFieldOrder {
    let local = cached_local_ctor_field_order(tcx);
    let mut out = (*local).clone();
    // `Self` depends on the enclosing impl, so it cannot live in the cached
    // crate-wide half. Recorded BEFORE the early returns below: a
    // `proof_assert!` inside a closure in a method body may spell it too.
    record_self_ctor_field_order(tcx, &mut out, def_id);
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        record_spec_tc_resolved_ctors(tcx, &mut out, def_id);
        return out;
    }
    if !matches!(
        tcx.def_kind(def_id),
        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
    ) {
        record_spec_tc_resolved_ctors(tcx, &mut out, def_id);
        return out;
    }
    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_norm_wip();
    let sig = tcx.liberate_late_bound_regions(def_id, sig);
    let mut visited = HashSet::new();
    for ty in sig.inputs() {
        collect_ctor_field_order_from_ty(tcx, *ty, &mut out, &mut visited, 0);
    }
    collect_ctor_field_order_from_ty(tcx, sig.output(), &mut out, &mut visited, 0);
    // A spelling rustc resolved ADDS a candidate under that spelling; it does
    // not displace the declaration-derived ones recorded above (see
    // `CtorCandidates` for why the additive direction is the sound one).
    record_spec_tc_resolved_ctors(tcx, &mut out, def_id);
    out
}
