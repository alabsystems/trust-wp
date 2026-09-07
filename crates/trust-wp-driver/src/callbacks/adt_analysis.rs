// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ADT field range and declaration analysis from TyCtxt.
//!
//! Collects algebraic datatype declarations and per-field integer range
//! constraints by inspecting MIR locals. Extracted from `integer_range.rs`
//! to separate integer range constraint generation from ADT analysis (#2452).

use num_bigint::BigInt;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Mutability, Ty, TyCtxt};
use trust_wp_core::formula::{intern_sort_name, ExprSort};

use super::integer_range::{int_bit_width, uint_bit_width};

/// Collect ADT field range constraints for all enum types used in a function.
///
/// Scans the optimized MIR body for the given `DefId`, finds all local variables
/// with `TyKind::Adt` types that are enums, and builds per-constructor field
/// range entries for integer-typed fields.
///
/// The returned map is keyed by the simple ADT name (e.g., `"List"`), matching
/// the name that [`SwitchTarget::infer_adt_name`] derives from qualified
/// constructor paths in match patterns. Constructor names are the unqualified
/// variant names (e.g., `"Cons"`).
///
/// This enables the encoder's ground field-range assumptions to inject
/// constraints like `is_Cons(t) → cons_0(t) >= 0` for unsigned fields at
/// every ADT-sorted binding/scrutinee, preventing spurious counterexamples.
/// (#2097, RC1)
pub(super) fn build_adt_field_ranges(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> trust_wp_core::logic::AdtFieldRanges {
    let mut ranges = trust_wp_core::logic::AdtFieldRanges::new();
    let pointer_bits = u32::try_from(tcx.data_layout.pointer_size().bits()).unwrap_or(64);

    // Closures don't have optimized_mir; return empty.
    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return ranges;
    }

    // Collect all ADT types referenced in the function's MIR locals.
    let Ok(body) =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| tcx.optimized_mir(def_id)))
    else {
        return ranges;
    };
    let mut seen_adts = std::collections::HashSet::new();

    for local_decl in &body.local_decls {
        collect_adt_field_ranges_from_ty(
            tcx,
            local_decl.ty,
            pointer_bits,
            &mut seen_adts,
            &mut ranges,
        );
    }

    ranges
}

/// Collect rustc-backed ADT declarations for non-model structs/enums referenced
/// by a function's MIR locals. (#1982)
pub(super) fn build_adt_decls(tcx: TyCtxt<'_>, def_id: DefId) -> trust_wp_core::logic::AdtDecls {
    let mut decls = trust_wp_core::logic::AdtDecls::new();

    if tcx.def_kind(def_id) == rustc_hir::def::DefKind::Closure {
        return decls;
    }

    let Ok(body) =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| tcx.optimized_mir(def_id)))
    else {
        return decls;
    };
    let mut seen_adts = std::collections::HashSet::new();

    for local_decl in &body.local_decls {
        collect_adt_decls_from_ty(tcx, local_decl.ty, &mut seen_adts, &mut decls);
    }

    decls
}

/// Recursively inspect a type for enum ADTs and collect field ranges.
///
/// Handles references (`&T`, `&mut T`), `Box<T>`, and nested ADTs.
fn collect_adt_field_ranges_from_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    pointer_bits: u32,
    seen_adts: &mut std::collections::HashSet<rustc_hir::def_id::DefId>,
    ranges: &mut trust_wp_core::logic::AdtFieldRanges,
) {
    use rustc_middle::ty::TyKind;
    use trust_wp_core::logic::FieldRangeKind;

    match ty.kind() {
        TyKind::Ref(_, inner, _) => {
            collect_adt_field_ranges_from_ty(tcx, *inner, pointer_bits, seen_adts, ranges);
        }
        TyKind::Adt(adt_def, substs) => {
            let did = adt_def.did();
            if !seen_adts.insert(did) {
                return; // Already processed this ADT (prevents infinite recursion)
            }

            // Unions have no meaningful per-field integer ranges; only recurse
            // into their fields to discover nested ADTs.
            if adt_def.is_union() {
                for variant in adt_def.variants() {
                    for field in &variant.fields {
                        let field_ty = field.ty(tcx, substs).skip_norm_wip();
                        collect_adt_field_ranges_from_ty(
                            tcx,
                            field_ty,
                            pointer_bits,
                            seen_adts,
                            ranges,
                        );
                    }
                }
                return;
            }

            // Both enums and structs reach here. For a struct, the single
            // datatype constructor is the struct itself, so its unsigned/signed
            // fields get the same `field(x) >= 0` range axioms enums already
            // benefit from. Without this, loop VCs over a struct loop variant
            // (e.g. `CustomVariant(u32, u32)`) lack the field non-negativity
            // facts that postcondition / variant-nonneg obligations need (#2702).
            let adt_name = tcx.item_name(did).to_string();
            let mut ctor_ranges = Vec::new();

            for variant in adt_def.variants() {
                let ctor_name = variant.name.to_string();
                let mut field_ranges = Vec::new();

                for (field_idx, field) in variant.fields.iter().enumerate() {
                    let field_ty = field.ty(tcx, substs).skip_norm_wip();

                    // Peel through Box<T> to get inner type
                    let inner_ty = peel_box_ty(tcx, field_ty);

                    match inner_ty.kind() {
                        TyKind::Uint(uint_ty) => {
                            let bits = uint_bit_width(*uint_ty, pointer_bits);
                            field_ranges.push((field_idx, FieldRangeKind::Unsigned(bits)));
                        }
                        TyKind::Int(int_ty) => {
                            let bits = int_bit_width(*int_ty, pointer_bits);
                            field_ranges.push((field_idx, FieldRangeKind::Signed(bits)));
                        }
                        _ => {
                            // Recurse into ADT-typed fields (e.g., Box<List>)
                            collect_adt_field_ranges_from_ty(
                                tcx,
                                field_ty,
                                pointer_bits,
                                seen_adts,
                                ranges,
                            );
                        }
                    }
                }

                if !field_ranges.is_empty() {
                    ctor_ranges.push((ctor_name, field_ranges));
                }
            }

            if !ctor_ranges.is_empty() {
                // The encoder's SwitchTarget::infer_adt_name produces different
                // names depending on whether contracts use qualified or unqualified
                // constructor names:
                //   qualified   (List::Cons, List::Nil) → "List"
                //   unqualified (Cons, Nil)              → "Adt_Cons_Nil"
                //
                // Index under BOTH the Rust type name and the synthesized name
                // so the encoder finds the ranges regardless of naming style.
                // (#2097 RC1 name-mismatch fix)
                let mut variant_names: Vec<String> = adt_def
                    .variants()
                    .iter()
                    .map(|v| v.name.to_string())
                    .collect();
                variant_names.sort_unstable();
                let synthesized_name = format!("Adt_{}", variant_names.join("_"));

                if synthesized_name != adt_name {
                    ranges.insert(synthesized_name, ctor_ranges.clone());
                }
                ranges.insert(adt_name, ctor_ranges);
            }
        }
        _ => {}
    }
}

fn collect_adt_decls_from_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    seen_adts: &mut std::collections::HashSet<rustc_hir::def_id::DefId>,
    decls: &mut trust_wp_core::logic::AdtDecls,
) {
    use rustc_middle::ty::TyKind;

    match ty.kind() {
        TyKind::Ref(_, inner, _) => {
            collect_adt_decls_from_ty(tcx, *inner, seen_adts, decls);
        }
        TyKind::Adt(adt_def, substs) => {
            let did = adt_def.did();
            let path = tcx.def_path_str(did);

            // The type-directed `snapshot!` capture dispatch introduces the
            // zero-sized erased selector `SnapshotCaptureSelect<T>` (and its
            // `SnapshotCaptureFallback` trait carrier) as an intermediate local
            // (the `capture`'s `self`). These are pure ghost machinery with no
            // logical payload — their only field is `PhantomData<*const T>`.
            // Collecting them as ADT declarations makes `needs_custom_sorts`
            // fire, which escalates the obligation's encoder to the full
            // heap-array memory model (`try_new_all`). That declares
            // unconstrained `heap`/`domain`/`perms` arrays, which a direct
            // inline `Snapshot::capture(&expr)` never introduces, and whose
            // unconstrained SAT model then fails ay's DebugChecked base-SAT
            // model validation — a spurious false-reject of the ENCLOSING
            // function's contract. Skip them entirely so the dispatch produces
            // a byte-identical VC to a direct capture. (bug/869)
            if is_snapshot_capture_dispatch_helper(&path) {
                return;
            }

            // Ghost-identity tokens get NO datatype declaration: their sort
            // must stay an unconstrained uninterpreted carrier. (resfid)
            if is_ghost_identity_token(&path) {
                return;
            }

            if let Some(inner) = transparent_wrapper_inner_ty(&path, substs) {
                collect_adt_decls_from_ty(tcx, inner, seen_adts, decls);
                return;
            }

            // `Box`, `Rc` and `Arc` are TRANSPARENT pointer wrappers: their
            // `Deref`/`deep_model` is the payload, so the encoder models them
            // at the payload's sort (`is_int_model_type`, sort_mapping.rs —
            // `Rc<i32>@ : i32`, #976). Peel to the payload and declare NOTHING
            // for the wrapper itself. Declaring one is actively unsound-adjacent:
            // the decl-beats-canonical rule in `sort_from_expr_sort` would then
            // reinterpret every `Datatype("Rc")` annotation as the carrier
            // datatype sort instead of the canonical Int, `rc@ == 1` becomes
            // eq(Datatype, Int), and `coerce_ite_sorts` swaps the literal for a
            // fresh unconstrained constant — silently FABRICATING AWAY the
            // `#[ensures(*result == value)]` premise (false-reject direction,
            // plus weakened vacuity detection). (adtpa)
            if is_box_path(&path) || is_rc_or_arc_path(&path) {
                if let Some(inner) = substs.types().next() {
                    collect_adt_decls_from_ty(tcx, inner, seen_adts, decls);
                }
                return;
            }

            let adt_name = tcx.item_name(did).to_string();
            if builtin_adt_model_sort(&adt_name).is_some() {
                for inner in substs.types() {
                    collect_adt_decls_from_ty(tcx, inner, seen_adts, decls);
                }
                return;
            }

            if !seen_adts.insert(did) {
                return;
            }

            if !adt_def.is_struct() && !adt_def.is_enum() {
                return;
            }

            if let Some(decl) = build_single_adt_decl(tcx, *adt_def, substs) {
                decls.entry(decl.adt_name.clone()).or_insert(decl);
            }

            for variant in adt_def.variants() {
                for field in &variant.fields {
                    collect_adt_decls_from_ty(
                        tcx,
                        field.ty(tcx, substs).skip_norm_wip(),
                        seen_adts,
                        decls,
                    );
                }
            }
        }
        _ => {}
    }
}

fn build_single_adt_decl<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt_def: rustc_middle::ty::AdtDef<'tcx>,
    substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
) -> Option<trust_wp_core::logic::AdtDecl> {
    use trust_wp_core::logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind};

    let rust_path = tcx.def_path_str(adt_def.did());
    let adt_name = tcx.item_name(adt_def.did()).to_string();
    let kind = if adt_def.is_struct() {
        AdtKind::Struct
    } else if adt_def.is_enum() {
        AdtKind::Enum
    } else {
        return None;
    };

    // Collect actual discriminant values from rustc (#2631).
    // For standard enums these equal variant indices; for #[repr] enums
    // with explicit assignments (e.g., `Active = 10`) they differ.
    let discriminant_map: std::collections::HashMap<_, BigInt> = if adt_def.is_enum() {
        adt_def
            .discriminants(tcx)
            .map(|(variant_idx, discr)| (variant_idx, rustc_discriminant_to_bigint(tcx, discr)))
            .collect()
    } else {
        std::collections::HashMap::new()
    };

    let constructors = adt_def
        .variants()
        .iter_enumerated()
        .map(|(variant_idx, variant)| {
            let rust_name = if adt_def.is_struct() {
                adt_name.clone()
            } else {
                variant.name.to_string()
            };
            let fields = variant
                .fields
                .iter()
                .enumerate()
                .map(|(field_index, field)| {
                    let field_name = if field.name.as_str().is_empty() {
                        field_index.to_string()
                    } else {
                        field.name.to_string()
                    };
                    let field_sort =
                        ty_to_adt_decl_sort(tcx, field.ty(tcx, substs).skip_norm_wip())?;
                    Some(AdtFieldDecl::new(field_name, field_sort))
                })
                .collect::<Option<Vec<_>>>()?;
            let mut ctor = AdtConstructorDecl::new(rust_name.clone(), rust_name, fields);
            if let Some(discr_val) = discriminant_map.get(&variant_idx) {
                ctor = ctor.with_discriminant_value(discr_val.clone());
            }
            Some(ctor)
        })
        .collect::<Option<Vec<_>>>()?;

    Some(AdtDecl::new(rust_path, adt_name, kind, constructors))
}

fn rustc_discriminant_to_bigint<'tcx>(
    tcx: TyCtxt<'tcx>,
    discr: rustc_middle::ty::util::Discr<'tcx>,
) -> BigInt {
    use rustc_middle::ty::TyKind;

    match discr.ty.kind() {
        TyKind::Int(int_ty) => {
            let pointer_bits = u32::try_from(tcx.data_layout.pointer_size().bits()).unwrap_or(64);
            let bits = int_bit_width(*int_ty, pointer_bits);
            BigInt::from(sign_extend_discriminant_bits(discr.val, bits))
        }
        _ => BigInt::from(discr.val),
    }
}

fn sign_extend_discriminant_bits(raw: u128, bits: u32) -> i128 {
    debug_assert!((1..=128).contains(&bits));
    let shift = 128_u32 - bits;
    (raw << shift).cast_signed() >> shift
}

#[allow(clippy::cast_possible_truncation)] // tuple arity always fits u8
fn ty_to_adt_decl_sort<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<ExprSort> {
    use rustc_middle::ty::TyKind;

    match ty.kind() {
        TyKind::Bool => Some(ExprSort::Bool),
        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Char => Some(ExprSort::Int),
        TyKind::Tuple(fields) if fields.is_empty() => Some(ExprSort::Unit),
        TyKind::Tuple(fields) => Some(ExprSort::Tuple(fields.len() as u8)),
        // #prophecy-slots (Fix B M1, blueprint C1): decl-level mutability
        // fidelity. `&mut T` fields lower to `ExprSort::MutRef` so (a) the
        // encoder declares the field at the mutref record sort instead of the
        // peeled Int, and (b) `sort_embeds_mut_ref`'s decl-field `Ref` arm can
        // recurse instead of failing closed (an erased `&mut` can no longer
        // hide under a decl-level `Ref`).
        TyKind::Ref(_, inner, mutability) => {
            ty_to_adt_decl_sort(tcx, *inner).map(|sort| match mutability {
                Mutability::Mut => ExprSort::MutRef(Box::new(sort)),
                Mutability::Not => ExprSort::Ref(Box::new(sort)),
            })
        }
        TyKind::Param(param) => Some(ExprSort::TypeParam(intern_sort_name(param.name.as_str()))),
        TyKind::Float(_) => Some(ExprSort::Float),
        TyKind::Adt(adt_def, substs) => {
            let path = tcx.def_path_str(adt_def.did());
            if let Some(inner) = transparent_wrapper_inner_ty(&path, substs) {
                return ty_to_adt_decl_sort(tcx, inner);
            }
            if is_box_path(&path) {
                // Peel through Box<T> to get the inner type's sort.
                // This enables recursive datatype declarations where variants
                // contain Box<Self> (e.g., Cons(T, Box<List<T>>)). The SMT
                // encoding treats Box as transparent. (#2675)
                return substs
                    .types()
                    .next()
                    .and_then(|inner| ty_to_adt_decl_sort(tcx, inner));
            }

            let adt_name = tcx.item_name(adt_def.did()).to_string();
            if let Some(sort) = builtin_adt_model_sort(&adt_name) {
                return Some(sort);
            }

            Some(ExprSort::Datatype(intern_sort_name(&path)))
        }
        _ => None,
    }
}

fn builtin_adt_model_sort(name: &str) -> Option<ExprSort> {
    if matches!(name, "Vec" | "VecDeque" | "Seq") {
        Some(ExprSort::Seq)
    } else if matches!(name, "FMap" | "HashMap" | "GhostMap") {
        Some(ExprSort::FMap)
    } else if name == "Mapping" {
        Some(ExprSort::Datatype(intern_sort_name("Mapping")))
    } else if is_builtin_adt_model_name(name) {
        Some(ExprSort::Int)
    } else {
        None
    }
}

#[allow(clippy::items_after_test_module)] // helper functions follow test module for locality
#[cfg(test)]
mod tests {
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    use num_bigint::BigInt;
    use rustc_driver::{run_compiler, Callbacks, Compilation};
    use rustc_interface::interface::Compiler;
    use rustc_middle::ty::TyCtxt;

    use super::{
        build_adt_decls, is_ghost_identity_token, is_rc_or_arc_path, sign_extend_discriminant_bits,
    };

    const TEST_CRATE_NAME: &str = "trust_wp_adt_analysis_test";
    static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

    #[derive(Default)]
    struct AdtDeclCallbacks {
        fn_name: String,
        decls: Option<trust_wp_core::logic::AdtDecls>,
        ran: bool,
    }

    impl Callbacks for AdtDeclCallbacks {
        #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            let suffix = format!("::{}", self.fn_name);
            for local_def_id in tcx.hir_body_owners() {
                let def_id = local_def_id.to_def_id();
                let def_path = tcx.def_path_str(def_id);
                if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                    continue;
                }

                self.decls = Some(build_adt_decls(tcx, def_id));
                self.ran = true;
                break;
            }
            Compilation::Stop
        }
    }

    fn collect_adt_decls(source: &str, fn_name: &str) -> trust_wp_core::logic::AdtDecls {
        let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_adt_analysis_{}_{}",
            std::process::id(),
            unique
        ));
        fs::create_dir_all(&temp_dir).expect("create test temp dir");

        let source_path = temp_dir.join("test.rs");
        fs::write(&source_path, source).expect("write test source");

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

        let mut callbacks = AdtDeclCallbacks {
            fn_name: fn_name.to_string(),
            decls: None,
            ran: false,
        };
        run_compiler(&args, &mut callbacks);

        let _ = fs::remove_file(&source_path);
        let _ = fs::remove_dir_all(&temp_dir);

        assert!(callbacks.ran, "failed to locate function `{fn_name}`");
        callbacks
            .decls
            .expect("adt declarations should be collected")
    }

    #[test]
    fn test_sign_extend_discriminant_bits_preserves_negative_i8() {
        assert_eq!(sign_extend_discriminant_bits(0xff, 8), -1);
        assert_eq!(sign_extend_discriminant_bits(0x80, 8), -128);
    }

    #[test]
    fn test_sign_extend_discriminant_bits_preserves_i128_min() {
        assert_eq!(sign_extend_discriminant_bits(1_u128 << 127, 128), i128::MIN);
    }

    #[test]
    fn test_build_adt_decls_preserves_large_u128_discriminants() {
        let source = r#"
#[repr(u128)]
pub enum Huge {
    A = 1u128 << 127,
    B = (1u128 << 127) + 5,
}

pub fn touch(x: Huge) {
    let _ = x;
    let _ = Huge::A;
    let _ = Huge::B;
}
"#;

        let decls = collect_adt_decls(source, "touch");
        let huge = decls.get("Huge").expect("Huge declaration");
        let huge_base: BigInt = BigInt::from(1_u128) << 127_u32;
        let expected_a = huge_base.clone();
        let expected_b = huge_base + BigInt::from(5_u8);

        let variant_a = huge
            .constructors
            .iter()
            .find(|ctor| ctor.rust_name == "A")
            .expect("Huge::A constructor");
        let variant_b = huge
            .constructors
            .iter()
            .find(|ctor| ctor.rust_name == "B")
            .expect("Huge::B constructor");

        assert_eq!(variant_a.discriminant_value.as_ref(), Some(&expected_a));
        assert_eq!(variant_b.discriminant_value.as_ref(), Some(&expected_b));
    }

    #[test]
    fn test_is_ghost_identity_token_positive_all_tokens_both_crates() {
        // (resfid) Every gated token under both std crate aliases, with the
        // module paths the real defs live at (ghost.rs / sync_view.rs /
        // std::sync::atomic_*), plus a shortened re-export path.
        const TOKENS: [&str; 8] = [
            "Resource",
            "Perm",
            "NonAtomicInvariant",
            "Tokens",
            "AtView",
            "LoadCommitter",
            "StoreCommitter",
            "UpdateCommitter",
        ];
        for krate in ["trust_wp_std", "creusot_std"] {
            for token in TOKENS {
                assert!(
                    is_ghost_identity_token(&format!("{krate}::ghost::resource::{token}")),
                    "{krate} deep path {token} should be gated"
                );
                assert!(
                    is_ghost_identity_token(&format!("{krate}::{token}")),
                    "{krate} re-export path {token} should be gated"
                );
            }
        }
        assert!(is_ghost_identity_token(
            "trust_wp_std::std::sync::atomic_relacq::LoadCommitter"
        ));
        assert!(is_ghost_identity_token("trust_wp_std::sync_view::AtView"));
    }

    #[test]
    fn test_is_ghost_identity_token_negative() {
        // User-crate collision: a user's own `Resource` must keep its decl.
        assert!(!is_ghost_identity_token("my_crate::Resource"));
        assert!(!is_ghost_identity_token("Resource"));
        // PhantomData itself and genuine unit structs stay faithful.
        assert!(!is_ghost_identity_token("std::marker::PhantomData"));
        // Wrappers with a real Resource field are fixed transitively, not gated.
        assert!(!is_ghost_identity_token(
            "trust_wp_std::ghost::resource::Authority"
        ));
        assert!(!is_ghost_identity_token(
            "trust_wp_std::ghost::resource::Fragment"
        ));
        // Id is a genuine `(Id (id_0 Int))` datatype and must stay declared.
        assert!(!is_ghost_identity_token("trust_wp_std::logic::ra::Id"));
        assert!(!is_ghost_identity_token("creusot_std::logic::ra::Id"));
        // Substring crate names must not match.
        assert!(!is_ghost_identity_token("not_trust_wp_std::Resource"));
        assert!(!is_ghost_identity_token(""));
    }

    #[test]
    fn test_user_defined_resource_keeps_its_adt_decl() {
        // (resfid) Anti-collision pin: a USER struct named `Resource` whose
        // only field is PhantomData is NOT std-pathed, so it must still
        // produce a datatype declaration (a faithful singleton for the user's
        // genuine unit struct).
        let source = r#"
use std::marker::PhantomData;

pub struct Resource(PhantomData<u8>);

pub fn touch(x: Resource) {
    let _ = x;
}
"#;

        let decls = collect_adt_decls(source, "touch");
        assert!(
            decls.get("Resource").is_some(),
            "user-defined Resource must keep its AdtDecl; got keys: {:?}",
            decls.keys().collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_is_rc_or_arc_path_positive_and_negative() {
        // (adtpa) Both the `alloc`-rooted def path rustc normally prints and
        // the `std` re-export path must be recognized.
        for path in [
            "alloc::rc::Rc",
            "std::rc::Rc",
            "alloc::sync::Arc",
            "std::sync::Arc",
        ] {
            assert!(is_rc_or_arc_path(path), "{path} should be peeled like Box");
        }
        // Neighbours that are NOT transparent wrappers keep their decls.
        assert!(!is_rc_or_arc_path("alloc::rc::Weak"));
        assert!(!is_rc_or_arc_path("std::sync::Mutex"));
        assert!(!is_rc_or_arc_path("std::sync::RwLock"));
        assert!(!is_rc_or_arc_path("my_crate::Rc"));
        assert!(!is_rc_or_arc_path("my_crate::Arc"));
        assert!(!is_rc_or_arc_path(""));
    }

    #[test]
    fn test_rc_and_arc_emit_no_wrapper_decl_but_keep_the_payload() {
        // (adtpa) The wrapper itself must produce NO datatype declaration —
        // a registered `Rc {..}` decl hijacks the canonical Int view sort in
        // `sort_from_expr_sort` and fabricates `rc@ == 1` premises away. Its
        // payload type must still be declared, exactly like `Box<T>`.
        let source = r#"
use std::rc::Rc;
use std::sync::Arc;

pub struct RcPayload { pub v: i32 }
pub struct ArcPayload { pub w: i32 }

pub fn touch(a: Rc<RcPayload>, b: Arc<ArcPayload>) {
    let _ = a;
    let _ = b;
}
"#;

        let decls = collect_adt_decls(source, "touch");
        let keys: Vec<_> = decls.keys().collect();
        assert!(
            decls.get("Rc").is_none(),
            "Rc must NOT produce a wrapper AdtDecl; got keys: {keys:?}"
        );
        assert!(
            decls.get("Arc").is_none(),
            "Arc must NOT produce a wrapper AdtDecl; got keys: {keys:?}"
        );
        assert!(
            decls.get("RcPayload").is_some(),
            "the Rc payload type must still be declared; got keys: {keys:?}"
        );
        assert!(
            decls.get("ArcPayload").is_some(),
            "the Arc payload type must still be declared; got keys: {keys:?}"
        );
    }

    #[test]
    fn test_model_carrier_types_emit_no_decl_but_keep_the_payload() {
        // The seven names in `builtin_adt_model_sort` are modelled on a
        // canonical CARRIER sort (Seq / FMap / Mapping), not on a datatype
        // built from their private fields. Emitting an `AdtDecl` for one is
        // never useful — `sort_from_expr_sort` refuses to consult it for these
        // names (`is_primary_model_name`, resolution.rs) — and for the
        // single-field wrappers it is actively fatal: `FMap { map: HashMap }`
        // maps its one field back to the FMap carrier, producing the
        // self-referential `FMap ::= FMap(fmap_map: FMap)` with no base case,
        // which ay's renderer correctly refuses. The whole obligation is then
        // poisoned ("total selector definitions withheld") and the test can
        // only report Unknown(Incomplete). `Seq { elements: Vec }` has the
        // identical shape.
        //
        // Skipping them also stops the descent through their PRIVATE fields
        // into allocator/hashbrown internals (RawVec, RawVecInner, Unique,
        // PhantomData, RawTable, ...) which carry zero logical content, while
        // the generic ARGUMENTS are still walked so real payload types keep
        // their declarations.
        let source = r#"
use std::collections::HashMap;

pub struct Elem { pub v: i32 }
pub struct Key { pub k: i32 }

pub fn touch(a: Vec<Elem>, b: HashMap<Key, Elem>) {
    let _ = a;
    let _ = b;
}
"#;

        let decls = collect_adt_decls(source, "touch");
        let keys: Vec<_> = decls.keys().collect();

        for carrier in ["Vec", "HashMap", "Seq", "FMap"] {
            assert!(
                decls.get(carrier).is_none(),
                "{carrier} is a canonical model carrier and must NOT produce an \
                 AdtDecl; got keys: {keys:?}"
            );
        }
        for internal in ["RawVec", "RawVecInner", "Unique", "PhantomData"] {
            assert!(
                decls.get(internal).is_none(),
                "{internal} is an allocator internal reached only through a model \
                 carrier's private fields and must NOT be declared; got keys: {keys:?}"
            );
        }

        assert!(
            decls.get("Elem").is_some(),
            "the element payload must still be declared; got keys: {keys:?}"
        );
        assert!(
            decls.get("Key").is_some(),
            "the key payload must still be declared; got keys: {keys:?}"
        );
    }

    #[test]
    fn test_mut_ref_field_decl_preserves_mutability() {
        // #prophecy-slots (Fix B M1, blueprint C1): `&mut T` fields must
        // lower to `ExprSort::MutRef` (previously both mutabilities erased to
        // `Ref`, forcing the encoder's decl-field guard to fail closed on
        // EVERY reference-typed field).
        let source = r#"
pub struct Holder<'a> {
    pub m: &'a mut i32,
    pub s: &'a i32,
}

pub fn touch(x: Holder<'_>) {
    let _ = x;
}
"#;

        let decls = collect_adt_decls(source, "touch");
        let holder = decls.get("Holder").expect("Holder decl");
        let ctor = &holder.constructors[0];
        assert_eq!(
            ctor.fields[0].sort,
            trust_wp_core::formula::ExprSort::MutRef(Box::new(
                trust_wp_core::formula::ExprSort::Int
            )),
            "`&mut i32` field must preserve mutability at decl level"
        );
        assert_eq!(
            ctor.fields[1].sort,
            trust_wp_core::formula::ExprSort::Ref(Box::new(trust_wp_core::formula::ExprSort::Int)),
            "`&i32` field must stay a shared Ref"
        );
    }

    #[test]
    fn test_std_pathed_resource_emits_no_adt_decl() {
        // (resfid) Absence pin: rustc prints LOCAL def paths without the
        // crate-name prefix, so a local module named `trust_wp_std` yields
        // exactly the std-shaped path `trust_wp_std::ghost::resource::Resource`
        // the gate matches on. This pins that a std-pathed ghost-identity
        // token produces NO datatype declaration (opaque uninterpreted sort).
        let source = r#"
pub mod trust_wp_std {
    pub mod ghost {
        pub mod resource {
            use std::marker::PhantomData;
            pub struct Resource(pub PhantomData<u8>);
        }
    }
}

pub fn touch(x: trust_wp_std::ghost::resource::Resource) {
    let _ = x;
}
"#;

        let decls = collect_adt_decls(source, "touch");
        assert!(
            decls.get("Resource").is_none(),
            "std-pathed Resource must NOT produce an AdtDecl; got keys: {:?}",
            decls.keys().collect::<Vec<_>>()
        );
    }
}

fn is_builtin_adt_model_name(name: &str) -> bool {
    matches!(
        name,
        "Option"
            | "Result"
            | "Int"
            | "Duration"
            | "Instant"
            | "HashSet"
            | "GhostSet"
            | "FSet"
            | "NonNeg"
            | "RangeInclusive"
            | "NonZeroU8"
            | "NonZeroU16"
            | "NonZeroU32"
            | "NonZeroU64"
            | "NonZeroU128"
            | "NonZeroUsize"
            | "NonZeroI8"
            | "NonZeroI16"
            | "NonZeroI32"
            | "NonZeroI64"
            | "NonZeroI128"
            | "NonZeroIsize"
    )
}

fn transparent_wrapper_inner_ty<'tcx>(
    path: &str,
    substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
) -> Option<Ty<'tcx>> {
    let is_wrapper = matches!(
        path,
        "trust_wp_std::ghost::Ghost"
            | "trust_wp_std::ghost::Snapshot"
            | "trust_wp_std::Ghost"
            | "trust_wp_std::Snapshot"
            | "creusot_std::ghost::Ghost"
            | "creusot_std::ghost::Snapshot"
            | "creusot_std::Ghost"
            | "creusot_std::Snapshot"
            | "ghost::Ghost"
            | "ghost::Snapshot"
            | "trust_wp::Ghost"
            | "trust_wp::Snapshot"
            | "Ghost"
            | "Snapshot"
            | "creusot_contracts::Ghost"
            | "creusot_contracts::Snapshot"
            | "creusot_contracts::ghost::Ghost"
            | "creusot_contracts::ghost::Snapshot"
    );
    if is_wrapper {
        substs.types().next()
    } else {
        None
    }
}

fn is_box_path(path: &str) -> bool {
    matches!(path, "alloc::boxed::Box" | "std::boxed::Box")
}

/// Whether `path` names a reference-counted transparent pointer (`Rc`/`Arc`).
///
/// Same category as [`is_box_path`]: the encoder's `is_int_model_type`
/// (sort_mapping.rs, #976) lists `Rc`/`Arc`/`Box` together precisely because
/// their view/deep-model is the payload, so their canonical sort is the
/// payload's — never a datatype carrier of their own private fields
/// (`rc_ptr`/`rc_phantom`/`rc_alloc`). Matched by full path and by the
/// `::rc::Rc` / `::sync::Arc` suffix so both the `alloc`-rooted def path rustc
/// normally prints and any `std`-rooted re-export path are covered. (adtpa)
fn is_rc_or_arc_path(path: &str) -> bool {
    matches!(
        path,
        "alloc::rc::Rc" | "std::rc::Rc" | "alloc::sync::Arc" | "std::sync::Arc"
    ) || path.ends_with("::rc::Rc")
        || path.ends_with("::sync::Arc")
}

/// Whether `path` names a type-directed `snapshot!` capture dispatch helper
/// (`SnapshotCaptureSelect` / `SnapshotCaptureFallback`). These zero-sized
/// erased selectors carry no logical payload; excluding them from ADT
/// declaration collection keeps a `snapshot!` of a place byte-identical to a
/// direct `Snapshot::capture(&expr)` and avoids escalating the obligation to
/// the heap-array memory model. Matched by the trailing path segment so it is
/// robust to the `trust_wp_std` / `creusot_std` (and `ghost::`) re-export
/// aliases. (bug/869)
fn is_snapshot_capture_dispatch_helper(path: &str) -> bool {
    path.ends_with("::SnapshotCaptureSelect") || path.ends_with("::SnapshotCaptureFallback")
}

/// Ghost-identity token types: their only payload is `PhantomData`, so a
/// datatype declaration makes them SMT singletons and forces x = y for all
/// terms — contradicting the contract-level identity laws (id() as UF).
/// Creusot ships these to Why3 as abstract types; the faithful encoding is
/// the opaque uninterpreted sort, reached by emitting NO AdtDecl (the
/// encoder's Datatype→Uninterpreted fallthrough does the rest). (resfid)
///
/// Unlike the bug/869 suffix-only match above, this predicate requires a
/// `trust_wp_std`/`creusot_std` crate prefix: `Resource`/`Tokens` are
/// plausible USER type names, and a user's genuine unit struct must keep its
/// faithful (singleton) datatype declaration.
fn is_ghost_identity_token(path: &str) -> bool {
    let mut segs = path.split("::");
    let crate_seg = segs.next().unwrap_or("");
    if !matches!(crate_seg, "trust_wp_std" | "creusot_std") {
        return false;
    }
    matches!(
        path.rsplit("::").next().unwrap_or(""),
        "Resource"
            | "Perm"
            | "NonAtomicInvariant"
            | "Tokens"
            | "AtView"
            | "LoadCommitter"
            | "StoreCommitter"
            | "UpdateCommitter"
    )
}

/// Peel `Box<T>` to get the inner type `T`.
///
/// In the MIR, `Box<List>` fields store the recursive ADT pointer. The field
/// type itself is `Box<T>`, but the SMT encoding treats it as `Sort::Int`
/// (the ADT sort). We don't want to generate range constraints for Box fields
/// themselves — only for scalar integer fields.
fn peel_box_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
    use rustc_middle::ty::TyKind;
    if let TyKind::Adt(adt_def, substs) = ty.kind() {
        let path = tcx.def_path_str(adt_def.did());
        if path == "alloc::boxed::Box" || path == "std::boxed::Box" {
            if let Some(inner) = substs.types().next() {
                return inner;
            }
        }
    }
    ty
}
