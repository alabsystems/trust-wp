// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-parameter final-value bindings for mutable-borrow verification.

use std::collections::{HashMap, HashSet};

use ay_dpll::api::{Sort, Term};
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_arity},
    ExprSort, FinalPinTarget, PinStep, ProjectedFinalPin, PureExpr,
};

use crate::{
    encoder::{
        extract_inner_var_annotation,
        match_enc::{
            datatype_constructor_matches, datatype_constructor_name, short_constructor_name,
        },
        sort_context::{
            ay_sort_to_expr_sort, reference_like_inner_sort, resolve_nameable_expr,
            resolve_view_var_name, select_structural_sort_target, DerivedKind,
        },
        AYEncoder, MutRefVarNames,
    },
    error::EncodingError,
};

pub(super) fn bind_final_values(
    encoder: &mut AYEncoder,
    final_values: &HashMap<String, PureExpr>,
    mutation_continued_params: Option<&HashSet<String>>,
) -> Result<(), EncodingError> {
    for (var_name, final_expr) in final_values {
        let is_mutation_continued =
            mutation_continued_params.is_some_and(|params| params.contains(var_name));
        bind_single_final_value(encoder, var_name, final_expr, is_mutation_continued)?;
    }
    Ok(())
}

fn bind_single_final_value(
    encoder: &mut AYEncoder,
    var_name: &str,
    final_expr: &PureExpr,
    is_mutation_continued: bool,
) -> Result<(), EncodingError> {
    let names = MutRefVarNames::new(var_name);
    let current_sort = infer_current_sort(encoder, var_name, &names, final_expr);
    if is_mutation_continued
        && is_bare_seq_identity_final_value(encoder, var_name, final_expr, &current_sort)
    {
        return Ok(());
    }
    let final_var = encoder.get_or_declare_var(&names.final_val, current_sort.clone())?;
    let current_var = encoder.get_or_declare_var(&names.current, current_sort.clone())?;
    let old_current_name = DerivedKind::Old.format_name(&names.current);
    let old_current_term = encoder.get_or_declare_var(&old_current_name, current_sort.clone())?;
    encoder.assert_eq(old_current_term, current_var);
    bind_same_sort_base_current_alias(encoder, var_name, &current_sort, current_var);
    let preserved_whole_carrier =
        encoder
            .var_sort(var_name)
            .cloned()
            .and_then(|sort| match ay_sort_to_expr_sort(&sort) {
                Some(ExprSort::MutRef(_)) => encoder.var_term(var_name).map(|term| (term, sort)),
                _ => None,
            });
    // Predeclare the inner current/final vars before encoding the final
    // expression so Deref(Var("v")) reuses the referent sort instead of
    // first fixing `v_current` to the whole carrier sort. (#2141, #2517)
    let final_term = encoder.encode_pure(final_expr)?;
    if let Some((base_term, base_sort)) = preserved_whole_carrier {
        // Encoding the referent expression may request an Int-typed view of the
        // base symbol. Preserve any predeclared whole MutRef carrier so the
        // later alias gate can still see the whole-borrow sort. (#2141, #2517)
        encoder.rebind_var(var_name, base_term, base_sort);
    }
    let current_final_name =
        DerivedKind::format_chain(var_name, &[DerivedKind::Current, DerivedKind::Final]);

    if is_mutation_continued {
        // #2124 Phase 5c: connect the deref-form final alias to the final
        // borrow-state variable without constraining it back to the entry term.
        let current_final_var =
            encoder.get_or_declare_var(&current_final_name, current_sort.clone())?;
        encoder.assert_eq(current_final_var, final_var);
    } else {
        encoder.assert_eq(final_var, final_term);
        encoder.propagate_seq_value(final_term, final_var);

        // Whole-struct field reconstruction bridge for &mut struct params over a
        // partially-opaque (generic) field. When the body writes individual
        // fields of a `&mut S<..>` parameter, the driver synthesizes a
        // whole-struct final value `__trust_wp_tupleN(f0, f1, ...)`. If the
        // carrier sort (`current_sort`) is a *named struct datatype* (e.g.
        // `S<i32, B>`) rather than a native `TupleN` sort, the reconstruction
        // term encodes at the synthetic tuple sort, so the `final_var == tuple`
        // equality above is cross-sort and `harmonize_eq_or_ite_terms` discards
        // it via a fresh constant — leaving the struct carrier's fields free.
        // That disconnects the field write (`x.0_final = 34`) from the type
        // invariant postcondition `(^x).invariant()`, which reads
        // `tuple_get_0(x_final)`. Re-establish the link by asserting per-field
        // equalities `tuple_get_i(x_final) == f_i` directly on the struct-sorted
        // carrier; `tuple_get_i` resolves to the native `S` field-i selector,
        // keeping each field (incl. the opaque `TypeParam` one) at its own sort.
        //
        // SOUND: post-mutation the struct genuinely IS `S(f0, f1, ...)`, so each
        // added equality already holds semantically. It only adds constraints
        // (never weakens an obligation), and is gated on a struct datatype
        // carrier so it cannot fire for native tuples handled elsewhere. (#2683)
        bind_struct_field_reconstruction(encoder, final_expr, final_var, &current_sort)?;

        // Restore _current_final alias (#2190, #858): Final(Deref(Var("v")))
        // resolves to "v_current_final" which must equal final_term.
        let current_final_var =
            encoder.get_or_declare_var(&current_final_name, current_sort.clone())?;
        encoder.assert_eq(current_final_var, final_term);

        // Bind _final_final alias for identity final values (#2190, #2673):
        // When v_final == v_current (identity), applying Final to both sides
        // gives Final(v_final) == Final(v_current), i.e.,
        // v_final_final == v_current_final. Without this, nested borrow
        // patterns like `unnest` (^*x == ^^x, i.e., x_current_final == x_final_final)
        // cannot be proven because x_final_final is unconstrained.
        if super::resolve::is_identity_final_value(var_name, final_expr) {
            let final_final_name =
                DerivedKind::format_chain(var_name, &[DerivedKind::Final, DerivedKind::Final]);
            let final_final_var =
                encoder.get_or_declare_var(&final_final_name, current_sort.clone())?;
            encoder.assert_eq(final_final_var, current_final_var);
            bind_identity_nested_current_alias(encoder, var_name, &current_sort)?;
        }
    }

    bind_whole_borrow_aliases(encoder, var_name, &current_sort, current_var, final_var)?;

    bind_view_aliases(
        encoder,
        var_name,
        &names,
        final_expr,
        final_term,
        &current_sort,
        is_mutation_continued,
    )
}

/// Bridge a whole-struct final-value reconstruction to its named-struct carrier
/// by asserting per-field equalities `tuple_get_i(final_var) == f_i`.
///
/// The driver synthesizes the final value of a `&mut S<..>` parameter whose
/// fields were written individually as `__trust_wp_tupleN(f0, f1, ...)`. When
/// the carrier (`carrier_sort`) is a named struct *datatype* (not a native
/// `TupleN`), encoding that reconstruction yields a synthetic-tuple-sorted term,
/// so the whole-value equality `final_var == reconstruction` is cross-sort and
/// gets dropped (a fresh constant replaces the reconstruction), leaving the
/// struct carrier's fields unconstrained. This re-attaches each field write to
/// the struct carrier directly: `tuple_get_i` resolves to the native field-i
/// selector of `S`, so the equality is well-sorted per field — including the
/// partially-opaque generic field, which keeps its `TypeParam` sort.
///
/// SOUND: post-mutation the struct genuinely is `S(f0, f1, ...)`, so each
/// equality already holds semantically. It only ADDS constraints (never weakens
/// an obligation). Gated on a single-constructor, N-field struct datatype carrier
/// (excluding native `TupleN`) so it never fires for tuples handled elsewhere
/// and never asserts an ill-sorted or spurious equality. (#2683)
fn bind_struct_field_reconstruction(
    encoder: &mut AYEncoder,
    final_expr: &PureExpr,
    final_var: Term,
    carrier_sort: &Sort,
) -> Result<(), EncodingError> {
    let PureExpr::LogicFnCall { name, args } = final_expr else {
        return Ok(());
    };
    let Some(arity) = tuple_logic_fn_arity(name) else {
        return Ok(());
    };
    if arity != args.len() {
        return Ok(());
    }

    // Resolve the carrier datatype declaration. Accept both the inline
    // `Datatype(..)` form and the `Uninterpreted("<name>")` form that ay-dpll
    // exposes for declared datatypes on term reads (#2257). Require a SINGLE
    // constructor (struct, not enum) with exactly `arity` fields, and exclude
    // the synthetic native tuple sorts (`TupleN`), which are handled by their
    // own decomposition paths and must not be re-bridged here.
    let dt = match carrier_sort {
        Sort::Datatype(dt) => Some(dt.clone()),
        Sort::Uninterpreted(name) => encoder.lookup_datatype_decl(name).cloned(),
        _ => None,
    };
    let Some(dt) = dt else {
        return Ok(());
    };
    if dt.name.starts_with("Tuple") {
        return Ok(());
    }
    let [ctor] = dt.constructors.as_slice() else {
        return Ok(());
    };
    if ctor.fields.len() != arity {
        return Ok(());
    }

    // Bind a temporary carrier alias to the already-bound `final_var` term so the
    // field selectors encode natively over the struct sort while constraining the
    // actual `final_var` (via congruence), not a fresh variable.
    let carrier_expr_sort = ay_sort_to_expr_sort(carrier_sort);
    let tmp_name = "__trust_wp_struct_recon_carrier";
    let tmp_var = encoder.get_or_declare_var(tmp_name, carrier_sort.clone())?;
    encoder.assert_eq(tmp_var, final_var);

    for (index, field_expr) in args.iter().enumerate() {
        // `tuple_get_i(tmp)` resolves to the native field-i selector of the
        // struct datatype, so each equality is well-sorted at the field's own
        // sort (including the partially-opaque `TypeParam` field).
        let field_access = PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(index),
            args: vec![PureExpr::Var(
                tmp_name.to_string(),
                carrier_expr_sort.clone(),
            )],
        };
        let selector_term = encoder.encode_pure(&field_access)?;
        let field_term = encoder.encode_pure(field_expr)?;
        let equality = encoder.eq_term(selector_term, field_term);
        encoder.assert_term(equality);
    }

    Ok(())
}

/// Bind one PROJECTED final value: the caller-side expiry pin for a `&mut`
/// that lives inside a call result. (#prophecy-slots M5)
///
/// Emits, for `Projection { root, path }` and death value `e`:
///
/// ```text
/// is-<Ctor₁>(root) ∧ … ∧ is-<Ctorₙ>(…) ==> mut_ref_final(<carrier>) == enc(e)
/// ```
///
/// and, for `Local(name)`, the unguarded `mut_ref_final(name) == enc(e)`.
///
/// ## Why the walk uses the definitional accessors and nothing else
///
/// `mut_ref_final` IS `^` by construction (`bind_whole_mut_ref` asserts the
/// constructor/selector identities), so the equation says exactly what the
/// driver proved: at the borrow's death, its prophecy equals the last value
/// written through it. Nothing here approximates.
///
/// ## ★Fail-closed: every route that cannot be completed EXACTLY emits nothing
///
/// * a path step whose receiver sort does not resolve to a declared datatype;
/// * a constructor or field the declaration does not carry;
/// * a tester or selector the solver refuses to build;
/// * **a reached term that is not `MutRef`-sorted.** This is the load-bearing
///   one. Pinning `^` on a non-carrier is precisely the collapse Fix A refuses
///   (`final_collapse_guard`): with no prophecy slot, `^p` and `*p` are the
///   same symbol, so the pin would silently assert `*p == e` — the take_first_mut
///   false-accept shape. If M1/M2 did not give this payload a carrier, there is
///   nothing to pin and we say so instead of guessing.
///
/// Refusing only ever REMOVES a premise, so it can never turn a rejected
/// obligation into an accepted one.
pub(super) fn bind_projected_final_values(
    encoder: &mut AYEncoder,
    pins: &[ProjectedFinalPin],
) -> Result<(), EncodingError> {
    for pin in pins {
        match bind_projected_final_value(encoder, pin) {
            Ok(true) => tracing::debug!(
                "prophecy-slots M5: emitted projected expiry pin {} ({:?})",
                pin.provenance,
                pin.target
            ),
            Ok(false) => tracing::debug!(
                "prophecy-slots M5: REFUSED projected expiry pin {} ({:?}) — \
                 the walk could not be completed exactly",
                pin.provenance,
                pin.target
            ),
            Err(err) => return Err(err),
        }
    }
    Ok(())
}

/// Returns `Ok(true)` when the pin was emitted, `Ok(false)` on a fail-closed
/// refusal.
pub(super) fn bind_projected_final_value(
    encoder: &mut AYEncoder,
    pin: &ProjectedFinalPin,
) -> Result<bool, EncodingError> {
    let (root_name, root_sort, path) = match &pin.target {
        FinalPinTarget::Local(name) => (name.as_str(), None, &[][..]),
        FinalPinTarget::Projection {
            root,
            root_sort,
            path,
        } => (root.as_str(), root_sort.clone(), path.as_slice()),
    };

    let Some(mut term) = encoder.var_term(root_name) else {
        // The root is not a symbol this VC mentions. A pin on a name nothing
        // else constrains is noise at best and a name collision at worst.
        return Ok(false);
    };
    let _ = root_sort;

    let mut guards: Vec<Term> = Vec::new();
    for step in path {
        let Some(next) = walk_pin_step(encoder, term, step, &mut guards)? else {
            return Ok(false);
        };
        term = next;
    }

    // ★The carrier requirement. See the doc comment: without a real carrier
    // there is no prophecy slot, and the "pin" would be an assertion about the
    // CURRENT value wearing a `^`.
    if !encoder.is_mut_ref_sorted(term) {
        return Ok(false);
    }
    let Some(final_term) = encoder.mut_ref_component_projection(term, true)? else {
        return Ok(false);
    };

    let value_term = encoder.encode_pure(&pin.value)?;
    if encoder.solver().get_sort(final_term) != encoder.solver().get_sort(value_term) {
        // A cross-sort equality would be harmonized away into a fresh constant
        // (or worse, routed through a coercion that mints a carrier-sorted
        // element — the route the restore-route audit closed). Refuse.
        return Ok(false);
    }
    let equality = encoder.eq_term(final_term, value_term);
    let guarded = guards.into_iter().fold(equality, |acc, guard| {
        encoder.solver_mut().implies(guard, acc)
    });
    encoder.assert_term(guarded);
    Ok(true)
}

/// A fresh alias name per positional-getter application.
///
/// Fresh-per-application is deliberate: two pin walks over different receivers
/// must never share an alias symbol, or the two definitional equalities would
/// fuse two unrelated carriers (the id-collapse shape the restore-route audit
/// closed on the Seq-element route).
fn next_projected_pin_alias_name() -> String {
    static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let id = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    format!("__trust_wp_pin_alias_{id}")
}

/// Apply one [`PinStep`], accumulating the variant tester when there is one.
fn walk_pin_step(
    encoder: &mut AYEncoder,
    receiver: Term,
    step: &PinStep,
    guards: &mut Vec<Term>,
) -> Result<Option<Term>, EncodingError> {
    let receiver_sort = encoder.solver().get_sort(receiver);
    let dt = match &receiver_sort {
        Sort::Datatype(dt) => Some(dt.clone()),
        Sort::Uninterpreted(name) => encoder.lookup_datatype_decl(name).cloned(),
        _ => None,
    };

    match step {
        PinStep::Variant { ctor, field } => {
            // A variant step without a declared datatype has no tester, and an
            // UNGUARDED enum-payload pin is the `optmut_none_branch_pin` shape.
            let Some(dt) = dt else {
                return Ok(None);
            };
            let ctor_name = datatype_constructor_name(&dt, ctor);
            let Some(ctor_decl) = dt
                .constructors
                .iter()
                .find(|candidate| datatype_constructor_matches(&dt, &candidate.name, &ctor_name))
            else {
                return Ok(None);
            };
            let Some(field_decl) = ctor_decl.fields.get(*field).cloned() else {
                return Ok(None);
            };
            let short = short_constructor_name(&ctor_name).to_string();
            let Ok(tester) = encoder.solver_mut().try_datatype_tester(&short, receiver) else {
                return Ok(None);
            };
            let Ok(projected) = encoder.solver_mut().try_datatype_selector(
                &field_decl.name,
                receiver,
                field_decl.sort.clone(),
            ) else {
                return Ok(None);
            };
            guards.push(tester);
            Ok(Some(projected))
        }
        PinStep::Field(index) => {
            // Prefer the NATIVE selector when the receiver is a declared
            // single-constructor datatype (a struct or a carrier tuple): that
            // is the symbol the rest of the encoding uses.
            if let Some(dt) = dt {
                if let [ctor_decl] = dt.constructors.as_slice() {
                    if let Some(field_decl) = ctor_decl.fields.get(*index).cloned() {
                        if let Ok(projected) = encoder.solver_mut().try_datatype_selector(
                            &field_decl.name,
                            receiver,
                            field_decl.sort.clone(),
                        ) {
                            return Ok(Some(projected));
                        }
                    }
                }
            }
            // Otherwise go through the positional getter, binding a temporary
            // alias so the getter machinery (which knows the M1/M2 carrier
            // families) sees a named receiver. The alias equality is
            // definitional — the same device `bind_struct_field_reconstruction`
            // uses. Fresh per application so two walks never meet.
            let alias_name = next_projected_pin_alias_name();
            let alias = encoder.get_or_declare_var(&alias_name, receiver_sort.clone())?;
            if encoder.solver().get_sort(alias) != receiver_sort {
                return Ok(None);
            }
            encoder.assert_eq(alias, receiver);
            let access = PureExpr::LogicFnCall {
                name: tuple_field_logic_fn_name(*index),
                args: vec![PureExpr::Var(
                    alias_name,
                    ay_sort_to_expr_sort(&receiver_sort),
                )],
            };
            Ok(Some(encoder.encode_pure(&access)?))
        }
    }
}

fn is_bare_seq_identity_final_value(
    encoder: &AYEncoder,
    var_name: &str,
    final_expr: &PureExpr,
    current_sort: &Sort,
) -> bool {
    (current_sort.is_seq()
        || encoder.var_sort(var_name).is_some_and(|sort| sort.is_seq())
        || matches!(final_expr, PureExpr::Var(_, Some(ExprSort::Seq))))
        && matches!(
            final_expr,
            PureExpr::Var(name, sort)
                if name == var_name && matches!(sort, None | Some(ExprSort::Seq))
        )
}

fn bind_identity_nested_current_alias(
    encoder: &mut AYEncoder,
    var_name: &str,
    current_sort: &Sort,
) -> Result<(), EncodingError> {
    let Some(current_expr_sort) = ay_sort_to_expr_sort(current_sort) else {
        return Ok(());
    };
    let Some(inner_sort) = reference_like_inner_sort(&current_expr_sort) else {
        return Ok(());
    };

    let inner_sort = encoder.sort_from_expr_sort(inner_sort.clone());
    let current_current_name =
        DerivedKind::format_chain(var_name, &[DerivedKind::Current, DerivedKind::Current]);
    let final_current_name =
        DerivedKind::format_chain(var_name, &[DerivedKind::Final, DerivedKind::Current]);
    let current_current = encoder.get_or_declare_var(&current_current_name, inner_sort.clone())?;
    let final_current = encoder.get_or_declare_var(&final_current_name, inner_sort)?;
    encoder.assert_eq(final_current, current_current);
    Ok(())
}

fn infer_current_sort(
    encoder: &mut AYEncoder,
    var_name: &str,
    names: &MutRefVarNames,
    final_expr: &PureExpr,
) -> Sort {
    // MIR ExprSort annotation: authoritative for non-Int sorts. (#994 Phase 2d)
    let final_ann = extract_inner_var_annotation(final_expr)
        .map(|sort| reference_like_inner_sort(sort).unwrap_or(sort));
    if let Some(sort) = final_ann {
        return encoder.sort_from_expr_sort(sort.clone());
    }

    let mut current_sort = {
        let resolved = encoder.resolve_var_sort_or_int_with_annotation(&names.current, final_ann);
        let resolved = project_reference_like_ay_sort(encoder, resolved);
        (resolved != Sort::Int).then_some(resolved)
    };
    if current_sort.is_none() {
        if let Some(name) = resolve_nameable_expr(final_expr, None) {
            let resolved = encoder.resolve_var_sort_or_int_with_annotation(&name, final_ann);
            let resolved = project_reference_like_ay_sort(encoder, resolved);
            if resolved != Sort::Int {
                current_sort = Some(resolved);
            }
        }
    }
    if current_sort.is_none() {
        if let Some(view_name) = resolve_view_var_name(final_expr, None) {
            let resolved = encoder.resolve_var_sort_or_int(&view_name);
            let resolved = project_reference_like_ay_sort(encoder, resolved);
            if resolved != Sort::Int {
                current_sort = Some(resolved);
            }
        }
    }
    if current_sort.is_none() {
        let resolved = encoder.resolve_var_sort_or_int_with_annotation(var_name, final_ann);
        let resolved = project_reference_like_ay_sort(encoder, resolved);
        if resolved != Sort::Int {
            current_sort = Some(resolved);
        }
    }

    // Context-aware inference for final sort fallback. (#1965)
    current_sort.unwrap_or_else(|| encoder.infer_expr_sort_with_context(final_expr, None))
}

fn bind_same_sort_base_current_alias(
    encoder: &mut AYEncoder,
    var_name: &str,
    current_sort: &Sort,
    current_var: Term,
) {
    let Some(existing_sort) = encoder.var_sort(var_name).cloned() else {
        return;
    };
    if existing_sort != *current_sort {
        return;
    }

    let Ok(base_term) = encoder.get_or_declare_var(var_name, current_sort.clone()) else {
        return;
    };
    encoder.assert_eq(base_term, current_var);
    encoder.propagate_seq_value(base_term, current_var);
}

fn project_reference_like_ay_sort(encoder: &mut AYEncoder, sort: Sort) -> Sort {
    ay_sort_to_expr_sort(&sort)
        .and_then(|expr_sort| reference_like_inner_sort(&expr_sort).cloned())
        .map(|inner| encoder.sort_from_expr_sort(inner))
        .unwrap_or(sort)
}

fn current_sort_to_expr_sort(sort: &Sort) -> Option<ExprSort> {
    match sort {
        Sort::Int => Some(ExprSort::Int),
        Sort::Bool => Some(ExprSort::Bool),
        Sort::Real => Some(ExprSort::Float),
        other => ay_sort_to_expr_sort(other),
    }
}

fn bind_whole_borrow_aliases(
    encoder: &mut AYEncoder,
    var_name: &str,
    current_sort: &Sort,
    current_var: Term,
    final_var: Term,
) -> Result<(), EncodingError> {
    let Some(inner_sort) = current_sort_to_expr_sort(current_sort) else {
        return Ok(());
    };
    let whole_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(inner_sort)));
    // Keep legacy scalar-only callers on the `_current`/`_final` path.
    // Whole-borrow aliasing is only sound once setup has already established
    // the base variable as a true MutRef carrier.
    let Some(existing_sort) = encoder.var_sort(var_name).cloned() else {
        return Ok(());
    };
    if existing_sort != whole_sort {
        return Ok(());
    }
    let id_var = encoder.get_or_declare_var(&MutRefVarNames::new(var_name).id, Sort::Int)?;
    let whole_var = encoder.get_or_declare_var(var_name, whole_sort.clone())?;
    encoder.bind_whole_mut_ref(
        &whole_sort,
        current_sort,
        whole_var,
        current_var,
        final_var,
        id_var,
    )?;

    // Nested mut-ref: decompose the *inner* reference carrier too
    // (#nested-mutref reborrow arg). When `x: &mut &mut T`, the referent
    // `*x` (= `x_current`) is itself a `&mut T`. Bind its definitional
    // `(current, final, id)` components to the scalar leaf carriers
    // `x_current_current` (= `**x`), `x_current_final` (= `^*x`), and
    // `x_current_id`. Without this, the inner reference's accessor UF
    // (`mut_ref_current(x_current)`) is disconnected from the precondition
    // carrier `x_current_current`, breaking the proof chain for nested
    // postconditions such as `^*x == 1` (inferred_invariants::nested_borrows).
    //
    // SOUND: this is the definitional decomposition of an existing carrier —
    // `mut_ref_current(r)`/`mut_ref_final(r)` ARE `*r`/`^r` by construction
    // (see `bind_whole_mut_ref`). It only relates carriers that already denote
    // the same values, never an over-approximation.
    bind_inner_mut_ref_components(encoder, var_name, current_sort)?;
    Ok(())
}

/// Decompose a nested inner mutable-reference carrier into its scalar leaf
/// components when the referent sort is itself a `MutRef`. See
/// `bind_whole_borrow_aliases`. (#nested-mutref reborrow arg)
fn bind_inner_mut_ref_components(
    encoder: &mut AYEncoder,
    var_name: &str,
    current_sort: &Sort,
) -> Result<(), EncodingError> {
    // `current_sort` is the sort of `*var_name` (= `var_name_current`). Only
    // act when that referent is itself a mutable reference.
    let Some(ExprSort::MutRef(inner_inner)) = ay_sort_to_expr_sort(current_sort) else {
        return Ok(());
    };
    let inner_inner_sort = encoder.sort_from_expr_sort((*inner_inner).clone());

    let current_name = DerivedKind::Current.format_name(var_name); // var_name_current
    let Some(inner_ref_term) = encoder.var_term(&current_name) else {
        return Ok(());
    };
    // Confirm the inner ref carrier really is MutRef-sorted before decomposing.
    if !encoder.is_mut_ref_sorted(inner_ref_term) {
        return Ok(());
    }

    let cc_name =
        DerivedKind::format_chain(var_name, &[DerivedKind::Current, DerivedKind::Current]);
    let cf_name = DerivedKind::format_chain(var_name, &[DerivedKind::Current, DerivedKind::Final]);
    let cid_name = format!("{current_name}_id");

    let cc_var = encoder.get_or_declare_var(&cc_name, inner_inner_sort.clone())?;
    let cf_var = encoder.get_or_declare_var(&cf_name, inner_inner_sort.clone())?;
    let cid_var = encoder.get_or_declare_var(&cid_name, Sort::Int)?;

    // Only bind when the scalar carriers are the inner leaf sort; otherwise a
    // pre-existing mismatched declaration would make the projector equalities
    // ill-sorted. (Defensive: declarations above set the right sort for fresh
    // vars; an existing wrong-sorted carrier is left alone.)
    if encoder.var_sort(&cc_name) != Some(&inner_inner_sort)
        || encoder.var_sort(&cf_name) != Some(&inner_inner_sort)
    {
        return Ok(());
    }

    let inner_whole_sort = encoder.solver().get_sort(inner_ref_term);
    encoder.bind_whole_mut_ref(
        &inner_whole_sort,
        &inner_inner_sort,
        inner_ref_term,
        cc_var,
        cf_var,
        cid_var,
    )
}

fn bind_view_aliases(
    encoder: &mut AYEncoder,
    var_name: &str,
    names: &MutRefVarNames,
    final_expr: &PureExpr,
    final_term: Term,
    current_sort: &Sort,
    is_mutation_continued: bool,
) -> Result<(), EncodingError> {
    let current_sort_hint = ay_sort_to_expr_sort(current_sort);
    let current_view_name = DerivedKind::View.format_name(&names.current);
    let old_current_view_name = DerivedKind::Old.format_name(&current_view_name);
    let current_view_term =
        encoder.encode_pure(&PureExpr::Var(current_view_name.clone(), current_sort_hint))?;
    let view_sort = encoder
        .var_sort(&current_view_name)
        .cloned()
        .unwrap_or_else(|| current_sort.clone());

    let base_view_name = DerivedKind::View.format_name(var_name);
    // Resolve the effective sort for view aliasing. When the base view was
    // predeclared with a different sort (e.g., Int from sort_fallback or a
    // user-defined Datatype while view_sort is Seq), attempt to bridge the
    // gap. Strategies:
    //   1. Sorts match exactly — use view_sort (common case).
    //   2. Existing is Int (sort_fallback) — use view_sort; get_or_declare_var
    //      handles Int→non-Int upgrades transparently.
    //   3. Structurally compatible (same family via select_structural_sort_target)
    //      — use the structurally stronger sort.
    //   4. Incompatible non-Int sorts — skip aliasing to avoid unsound coercion.
    let (base_sort_matches, effective_view_sort) = match encoder.var_sort(&base_view_name).cloned()
    {
        None => (true, view_sort.clone()),
        Some(existing) if existing == view_sort => (true, view_sort.clone()),
        // Int→non-Int: sort_fallback produced Int, real sort is known now.
        Some(Sort::Int) if view_sort != Sort::Int => (true, view_sort.clone()),
        // non-Int→Int: view_sort fell back to Int but base has real sort. Use base.
        Some(ref existing) if view_sort == Sort::Int && *existing != Sort::Int => {
            (true, existing.clone())
        }
        // Both non-Int, different: check structural compatibility.
        Some(ref existing) => {
            if let Some(target) = select_structural_sort_target(existing, &view_sort) {
                (true, target)
            } else {
                (false, view_sort.clone())
            }
        }
    };
    if base_sort_matches {
        let base_view_term =
            encoder.get_or_declare_var(&base_view_name, effective_view_sort.clone())?;

        // Phase 6 (#2124): IndexMut `.set()` final expressions advance the base
        // view to the post-write state so legacy call assumptions that name the
        // post-call state as the bare view (`v_view`) observe the update.
        let has_indexed_writes =
            matches!(final_expr, PureExpr::MethodCall { method, .. } if method == "set");

        // Entry-pinned guard for the Phase 6 advancement (slices/range vacuity).
        //
        // When the base parameter is itself view-sorted (a `&mut [T]` slice whose
        // carrier collapsed to the Seq view), every encode of `v@` asserts the
        // definitional identity `v == v_view` (`declare_view_var` →
        // `assert_view_identity`), so the bare view symbol IS the entry state:
        // preconditions such as `a@ == seq![0, 0, 0, 0]` pin its elements.
        // Asserting `v_view == final_v_view` on top equates the ENTRY state with
        // the POST-write state — semantically false whenever the `.set()` chain
        // changes an element — which makes the base premises UNSAT and trips the
        // vacuity guard (base-UNSAT → everything demoted). Skip the advancement
        // in that case: it is a pure premise REMOVAL of an equality that is
        // false in every model where the write changes a pinned element, so it
        // can only shrink the premise set toward the true semantics (never
        // admits a previously-refutable model on the goal side). The entry
        // connectivity needed by postconditions survives through the
        // definitional bridges (`v == v_view`, `v == v_current`,
        // `v_current == v_current_view`), and post-write lookups already
        // resolve through `View(Final(v))` → `final_v_view`, which stays bound
        // to the `.set()` chain below — the driver performs the SSA re-point at
        // the PureExpr level, so no encoder-side renaming is needed (renaming
        // the shared symbol would be UNSOUND: later `v@` encodes re-assert the
        // `v == v_view` identity against whatever term the name maps to, which
        // would manufacture `v == final_v_view`, recreating the collapse).
        //
        // When the base is a true reference carrier (e.g. `&mut Vec<T>`), no
        // `v == v_view` identity exists; the bare view is only consumed by
        // legacy Pipeline A call assumptions as the post-call state, so the
        // Phase 6 advancement remains the sole (and intended) definition of
        // that symbol. Keep it. (Mirrors the #2663 pattern in `resolve.rs`:
        // skip an identity that would contradict a non-identity final value.)
        let base_view_is_entry_pinned = encoder.has_view_identity(var_name);

        let old_base_view_source = if has_indexed_writes {
            if !base_view_is_entry_pinned {
                let final_view_name = DerivedKind::format_chain(
                    var_name,
                    &[DerivedKind::FinalPrefix, DerivedKind::View],
                );
                if let Some(final_view_term) = encoder.var_term(&final_view_name) {
                    encoder.assert_eq(base_view_term, final_view_term);
                    encoder.propagate_seq_value(final_view_term, base_view_term);
                } else {
                    encoder.assert_eq(base_view_term, final_term);
                    encoder.propagate_seq_value(final_term, base_view_term);
                }
            }
            current_view_term
        } else {
            encoder.assert_eq(base_view_term, current_view_term);
            base_view_term
        };

        let old_base_view_name = DerivedKind::Old.format_name(&base_view_name);
        let old_base_sort_ok = match encoder.var_sort(&old_base_view_name).cloned() {
            None => true,
            Some(ref existing) if *existing == effective_view_sort => true,
            Some(Sort::Int) if effective_view_sort != Sort::Int => true,
            Some(ref existing) if effective_view_sort == Sort::Int && *existing != Sort::Int => {
                true
            }
            Some(ref existing) => {
                select_structural_sort_target(existing, &effective_view_sort).is_some()
            }
        };
        if old_base_sort_ok {
            let old_base_view_term =
                encoder.get_or_declare_var(&old_base_view_name, effective_view_sort.clone())?;
            encoder.assert_eq(old_base_view_term, old_base_view_source);
        }
    }

    let old_current_view_term =
        encoder.get_or_declare_var(&old_current_view_name, view_sort.clone())?;
    encoder.assert_eq(old_current_view_term, current_view_term);

    // Phase 5c (#2124): bridge final_v_current_view == final_v_view for
    // mutation-continued params. Non-mutation-continued cases get this
    // transitively through the final expression binding.
    if is_mutation_continued {
        let final_base_view_name =
            DerivedKind::format_chain(var_name, &[DerivedKind::FinalPrefix, DerivedKind::View]);
        let final_current_view_name = DerivedKind::format_chain(
            &names.current,
            &[DerivedKind::FinalPrefix, DerivedKind::View],
        );
        let final_base_view =
            encoder.get_or_declare_var(&final_base_view_name, view_sort.clone())?;
        let final_current_view =
            encoder.get_or_declare_var(&final_current_view_name, view_sort.clone())?;
        encoder.assert_eq(final_base_view, final_current_view);
    } else if final_value_view_is_identity(current_sort) {
        let suffix_final_view_name =
            DerivedKind::format_chain(var_name, &[DerivedKind::Final, DerivedKind::View]);
        let prefix_final_view_name =
            DerivedKind::format_chain(var_name, &[DerivedKind::FinalPrefix, DerivedKind::View]);

        for final_view_name in [suffix_final_view_name, prefix_final_view_name] {
            let final_view_term =
                encoder.get_or_declare_var(&final_view_name, current_sort.clone())?;
            encoder.assert_eq(final_view_term, final_term);
            encoder.propagate_seq_value(final_term, final_view_term);
        }
    }

    Ok(())
}

fn final_value_view_is_identity(sort: &Sort) -> bool {
    matches!(sort, Sort::Int | Sort::Bool)
        || sort.is_seq()
        || matches!(sort, Sort::Uninterpreted(name) if name == "FMap")
}
