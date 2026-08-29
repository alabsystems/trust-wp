// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Datatype variable pre-declaration for verification setup.
//!
//! Scans contract expressions for match scrutinee patterns with user-defined
//! constructors and pre-declares variables with the correct `DatatypeSort`
//! before any other encoding path can lock them in as `Sort::Int`.
//!
//! Extracted from `setup.rs` to keep both files under the 500-line guideline.
//! See #2002 and #1965 for the sort-inference context.

use std::collections::{HashMap, HashSet};

use ay_dpll::api::DatatypeSort;
use trust_wp_core::{
    formula::{resolve_sort_name, BinOp, ExprSort, MatchArm, Pattern, PureExpr},
    logic::{AdtDecls, LogicFnDef},
};

use crate::encoder::{
    match_enc::{short_constructor_name, stdlib_constructor_target, SwitchTarget},
    sort_context::DerivedKind,
};

#[cfg(test)]
mod test_support;

#[cfg(test)]
pub(in crate::verify) use test_support::{adt_decl_to_datatype_sort, predeclare_datatype_vars};

/// Collect planned Datatype-sorted names from the bootstrap expression set.
///
/// This is the pure-data counterpart to the old pre-declaration pass: it
/// discovers Datatype evidence from match scrutinees and logic-function call
/// sites without mutating the encoder. (#2020)
pub(in crate::verify) fn collect_bootstrap_datatype_var_sorts(
    input_exprs: &[&PureExpr],
    postcondition_exprs: Option<&[PureExpr]>,
    logic_fns: Option<&[LogicFnDef]>,
    registered_datatypes: &[DatatypeSort],
) -> HashMap<String, DatatypeSort> {
    let mut dt_vars: HashMap<String, DatatypeSort> = HashMap::new();

    // Pass 1: Scan all expression sources for match scrutinees with user-defined
    // constructor patterns. This catches variables that appear directly in match
    // expressions within requires/ensures/context_exprs and logic function bodies.
    for expr in input_exprs {
        collect_datatype_scrutinee_vars(expr, registered_datatypes, &mut dt_vars);
    }
    // Do not directly export scrutinee variable names from logic-function bodies.
    // Those names are local to the logic function (`self`, `k`, `v`, etc.) and
    // can collide with the function currently being verified. Pass 2 below uses
    // the same bodies to infer formal parameter datatype sorts, then propagates
    // them only to concrete call-site arguments.

    // Pass 2: Propagate Datatype sorts from logic function parameter inference
    // to call-site argument variables. When a logic function like `sum(self)` has
    // a Datatype-sorted parameter (inferred from match expressions in its body),
    // and the requires/ensures contain `l.sum()`, the call-site variable `l` must
    // also be predeclared with Datatype sort. Without this, `l` gets locked as
    // Int by the precondition encoding before the logic function call encoding
    // can propagate the sort hint. (#994, #2002)
    if let Some(fns) = logic_fns {
        let param_dt_map = build_logic_fn_param_dt_map(fns, registered_datatypes);
        if !param_dt_map.is_empty() {
            for expr in input_exprs {
                collect_call_site_dt_vars(expr, &param_dt_map, &mut dt_vars);
            }
        }
    }

    // Pass 3: Scan postconditions for constructor equality patterns (#1296).
    //
    // Postconditions like `forall<t> self == Ok(t) ==> result == Ok(t)` contain
    // constructor equalities where a variable (self, result) is compared to a
    // constructor call (LogicFnCall). When the constructor name matches a
    // registered datatype, pre-declare the variable with Datatype sort.
    //
    // Without this, identity-body functions (where body is `var("self")`) lock
    // `self` and `result` as Int during body encoding. The quantifier ctor
    // elimination then fails because it cannot apply datatype testers to
    // Int-sorted terms, and the PhantomVariableUpgrade creates a `self__upgraded`
    // variable that is disconnected from the body's `result = self(Int)` assertion.
    //
    // Only scans postconditions (not requires) to avoid spuriously pre-declaring
    // variables that appear in constructor equalities within preconditions.
    // Preconditions may contain formula-local variables named `result` that
    // should not be treated as the postcondition return binder.
    if let Some(post_exprs) = postcondition_exprs {
        for expr in post_exprs {
            collect_constructor_eq_dt_vars(expr, registered_datatypes, &mut dt_vars);
        }
    }

    dt_vars
}

/// Build a map from logic function name → Vec<(param_index, DatatypeSort)>.
///
/// For each logic function, scans the body for match expressions on parameters
/// with user-defined constructor patterns, recording which parameter positions
/// have Datatype sorts. Used by `collect_call_site_dt_vars` to map call-site
/// arguments to Datatype sorts.
// Visible to parent (setup) for test re-exports.
pub(super) fn build_logic_fn_param_dt_map(
    logic_fns: &[LogicFnDef],
    registered_datatypes: &[DatatypeSort],
) -> HashMap<String, Vec<(usize, DatatypeSort)>> {
    let mut map: HashMap<String, Vec<(usize, DatatypeSort)>> = HashMap::new();

    for logic_fn in logic_fns {
        let param_set: HashSet<&str> = logic_fn.params().iter().map(String::as_str).collect();
        let mut param_dts: HashMap<&str, DatatypeSort> = HashMap::new();

        // Scan body, requires, ensures for match scrutinees that are parameters
        collect_param_match_datatypes(
            logic_fn.body(),
            &param_set,
            registered_datatypes,
            &mut param_dts,
        );
        for expr in logic_fn.requires() {
            collect_param_match_datatypes(expr, &param_set, registered_datatypes, &mut param_dts);
        }
        for expr in logic_fn.ensures() {
            collect_param_match_datatypes(expr, &param_set, registered_datatypes, &mut param_dts);
        }

        if !param_dts.is_empty() {
            let mut indexed: Vec<(usize, DatatypeSort)> = Vec::new();
            for (param_name, dt) in param_dts {
                if let Some(idx) = logic_fn.params().iter().position(|p| p == param_name) {
                    indexed.push((idx, dt));
                }
            }
            if !indexed.is_empty() {
                // Register under the short method name (e.g., "sum") used by
                // MethodCall dispatch. Also register under the full_path for
                // LogicFnCall references that use qualified names.
                extend_param_dt_entries(&mut map, logic_fn.name().to_owned(), &indexed);
                if logic_fn.full_path() != logic_fn.name() {
                    extend_param_dt_entries(&mut map, logic_fn.full_path().to_owned(), &indexed);
                }
            }
        }
    }

    map
}

fn extend_param_dt_entries(
    map: &mut HashMap<String, Vec<(usize, DatatypeSort)>>,
    key: String,
    entries: &[(usize, DatatypeSort)],
) {
    let existing = map.entry(key).or_default();
    for (idx, dt) in entries {
        if existing
            .iter()
            .any(|(existing_idx, existing_dt)| existing_idx == idx && existing_dt.name == dt.name)
        {
            continue;
        }
        existing.push((*idx, dt.clone()));
    }
}

/// Scan a match expression for scrutinees that are logic function parameters,
/// extracting user-defined Datatype sorts. Similar to `collect_param_datatypes`
/// in logic_fn.rs but returns DatatypeSort directly.
fn collect_param_match_datatypes<'a>(
    expr: &PureExpr,
    param_names: &HashSet<&'a str>,
    registered_datatypes: &[DatatypeSort],
    out: &mut HashMap<&'a str, DatatypeSort>,
) {
    fn match_scrutinee_param_ref<'a>(
        scrutinee: &PureExpr,
        param_names: &HashSet<&'a str>,
    ) -> Option<&'a str> {
        match scrutinee {
            PureExpr::Var(name, _) => param_names.get(name.as_str()).copied(),
            PureExpr::Deref(inner) => {
                if let PureExpr::Var(name, _) = inner.as_ref() {
                    param_names.get(name.as_str()).copied()
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    expr.for_each_recursive(|node| {
        let PureExpr::Match { scrutinee, arms } = node else {
            return;
        };
        let Some(name) = match_scrutinee_param_ref(scrutinee, param_names) else {
            return;
        };
        if out.contains_key(name) {
            return;
        }
        if let Some(target) = registered_datatype_for_arms(registered_datatypes, arms) {
            out.insert(name, target);
        } else if let Some(target) = SwitchTarget::from_arms(arms) {
            if matches!(target, SwitchTarget::UserDefined { .. }) {
                out.insert(name, target.datatype());
            }
        }
    });
}

/// Recursively scan an expression for MethodCall/LogicFnCall references to logic
/// functions with Datatype-sorted parameters, mapping call-site argument variables
/// to the corresponding Datatype sorts.
///
/// For `MethodCall { receiver: Var("l"), method: "sum", args: [] }` where `sum`
/// has param[0] ("self") as Datatype, this maps `"l"` → DatatypeSort.
pub(super) fn collect_call_site_dt_vars(
    expr: &PureExpr,
    param_dt_map: &HashMap<String, Vec<(usize, DatatypeSort)>>,
    out: &mut HashMap<String, DatatypeSort>,
) {
    expr.for_each_recursive(|node| match node {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            // MethodCall dispatch prepends receiver as arg[0] when calling logic fns
            let Some(param_dts) = param_dt_map.get(method.as_str()) else {
                return;
            };
            let mut all_args: Vec<&PureExpr> = vec![receiver.as_ref()];
            all_args.extend(args.iter());
            for (param_idx, arg) in all_args.iter().enumerate() {
                if let Some(dt) = unique_matching_call_site_datatype(arg, param_idx, param_dts) {
                    if let Some(var_name) = resolve_call_site_var_name(arg) {
                        if let std::collections::hash_map::Entry::Vacant(e) = out.entry(var_name) {
                            e.insert(dt.clone());
                        }
                    }
                }
            }
        }
        PureExpr::LogicFnCall { name, args } => {
            let Some(param_dts) = param_dt_map.get(name.as_str()) else {
                return;
            };
            for (param_idx, arg) in args.iter().enumerate() {
                if let Some(dt) = unique_matching_call_site_datatype(arg, param_idx, param_dts) {
                    if let Some(var_name) = resolve_call_site_var_name(arg) {
                        if let std::collections::hash_map::Entry::Vacant(e) = out.entry(var_name) {
                            e.insert(dt.clone());
                        }
                    }
                }
            }
        }
        _ => {}
    });
}

fn unique_matching_call_site_datatype<'a>(
    arg: &PureExpr,
    param_idx: usize,
    param_dts: &'a [(usize, DatatypeSort)],
) -> Option<&'a DatatypeSort> {
    let mut matched: Option<&DatatypeSort> = None;
    for (candidate_idx, dt) in param_dts {
        if *candidate_idx != param_idx || !call_site_arg_compatible_with_datatype(arg, dt) {
            continue;
        }
        if matched.is_some_and(|existing| existing.name == dt.name) {
            continue;
        }
        if matched.is_some() {
            return None;
        }
        matched = Some(dt);
    }
    matched
}

fn call_site_arg_compatible_with_datatype(arg: &PureExpr, dt: &DatatypeSort) -> bool {
    let Some(annotation) = effective_call_site_annotation(arg) else {
        return true;
    };
    annotation_matches_datatype(annotation, dt)
}

fn effective_call_site_annotation(expr: &PureExpr) -> Option<&ExprSort> {
    match expr {
        PureExpr::Var(_, annotation) => annotation.as_ref(),
        PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            effective_call_site_annotation(inner).and_then(reference_like_inner_sort)
        }
        PureExpr::Old(inner) | PureExpr::View(inner) => effective_call_site_annotation(inner),
        _ => None,
    }
}

fn reference_like_inner_sort(sort: &ExprSort) -> Option<&ExprSort> {
    match sort {
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => Some(inner.as_ref()),
        _ => None,
    }
}

fn annotation_matches_datatype(annotation: &ExprSort, dt: &DatatypeSort) -> bool {
    match annotation {
        ExprSort::Datatype(id) => datatype_names_match(&resolve_sort_name(*id), &dt.name),
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => annotation_matches_datatype(inner, dt),
        _ => false,
    }
}

fn datatype_names_match(annotation_name: &str, datatype_name: &str) -> bool {
    annotation_name == datatype_name
        || annotation_name.rsplit("::").next() == Some(datatype_name)
        || datatype_name.rsplit("::").next() == Some(annotation_name)
}

/// Resolve the variable name that will be used by the encoder for a call-site
/// argument expression. Matches the encoder's naming convention:
/// - `Var("l")` → `"l"`
/// - `Deref(Var("self"))` → `"self_current"`
/// - `Final(Var("self"))` → `"self_final"`
/// - `View(Var("v"))` → `"v_view"` (not a Datatype case, but handled for completeness)
pub(super) fn resolve_call_site_var_name(expr: &PureExpr) -> Option<String> {
    if let PureExpr::Var(name, _) = expr {
        Some(name.clone())
    } else if let PureExpr::Deref(inner) = expr {
        if let PureExpr::Var(name, _) = inner.as_ref() {
            Some(DerivedKind::Current.format_name(name))
        } else {
            None
        }
    } else if let PureExpr::Final(inner) = expr {
        if let PureExpr::Var(name, _) = inner.as_ref() {
            Some(DerivedKind::Final.format_name(name))
        } else {
            None
        }
    } else {
        None
    }
}

/// Recursively scan an expression for match scrutinees that are Var or Deref(Var)
/// with user-defined constructor patterns, collecting the variable name → DatatypeSort
/// mapping.
pub(super) fn collect_datatype_scrutinee_vars(
    expr: &PureExpr,
    registered_datatypes: &[DatatypeSort],
    out: &mut HashMap<String, DatatypeSort>,
) {
    fn match_scrutinee_var_name(scrutinee: &PureExpr) -> Option<String> {
        match scrutinee {
            PureExpr::Var(name, _) => Some(name.clone()),
            PureExpr::Deref(inner) => {
                if let PureExpr::Var(name, _) = inner.as_ref() {
                    // For Deref(Var("self")), the encoded name is "self_current"
                    Some(DerivedKind::Current.format_name(name))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    expr.for_each_recursive(|node| {
        let PureExpr::Match { scrutinee, arms } = node else {
            return;
        };
        let Some(name) = match_scrutinee_var_name(scrutinee) else {
            return;
        };
        let std::collections::hash_map::Entry::Vacant(entry) = out.entry(name) else {
            return;
        };
        if let Some(target) = registered_datatype_for_arms(registered_datatypes, arms) {
            entry.insert(target);
        } else if let Some(target) = SwitchTarget::from_arms(arms) {
            if matches!(target, SwitchTarget::UserDefined { .. }) {
                entry.insert(target.datatype());
            }
        }
    });
}

/// Scan an expression for constructor equality patterns (`x == Ctor(args)`)
/// where the constructor belongs to a registered datatype, collecting the
/// variable name -> DatatypeSort mapping. (#1296)
///
/// This catches variables like `self` and `result` that appear in quantified
/// postconditions (`forall<t> self == Ok(t) ==> ...`) but never appear as
/// match scrutinees. Without pre-declaring these as Datatype-sorted, the body
/// encoding locks them as Int, and the quantifier ctor elimination cannot
/// apply datatype testers.
pub(super) fn collect_constructor_eq_dt_vars(
    expr: &PureExpr,
    registered_datatypes: &[DatatypeSort],
    out: &mut HashMap<String, DatatypeSort>,
) {
    use crate::encoder::match_enc::{short_constructor_name, stdlib_constructor_target};

    expr.for_each_recursive(|node| {
        // Look for Eq(lhs, rhs) where one side is a variable and the other
        // is a constructor call (LogicFnCall) matching a registered datatype.
        // PureExpr::BinOp fields are (Arc<lhs>, BinOp, Arc<rhs>).
        let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = node else {
            return;
        };

        // Try both orientations: var == Ctor(args) and Ctor(args) == var
        let pairs: [(&PureExpr, &PureExpr); 2] =
            [(lhs.as_ref(), rhs.as_ref()), (rhs.as_ref(), lhs.as_ref())];
        for (var_side, ctor_side) in &pairs {
            let PureExpr::LogicFnCall { name, .. } = ctor_side else {
                continue;
            };
            let Some(var_name) = extract_eq_var_name(var_side) else {
                continue;
            };
            if out.contains_key(&var_name) {
                continue;
            }
            // First check registered (user-defined) datatypes.
            let short = short_constructor_name(name);
            if let Some(dt) = registered_datatypes
                .iter()
                .find(|dt| dt.constructors.iter().any(|ctor| ctor.name == short))
            {
                out.insert(var_name, dt.clone());
                continue;
            }
            // Fall back to stdlib constructor recognition (Some, None, Ok, Err).
            // These may not be in registered_datatypes if no match expression
            // or ADT declaration triggered their registration.
            if let Some(target) = stdlib_constructor_target(name) {
                out.insert(var_name, target.datatype());
            }
        }
    });
}

/// Extract the variable name from one side of a constructor equality.
///
/// Handles `Var("x")`, `Deref(Var("x"))` (encoded as "x_current"), and
/// `Final(Var("x"))` (encoded as "x_final").
fn extract_eq_var_name(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::Var(name, _) => Some(name.clone()),
        PureExpr::Deref(inner) => {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                Some(DerivedKind::Current.format_name(name))
            } else {
                None
            }
        }
        PureExpr::Final(inner) => {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                Some(DerivedKind::Final.format_name(name))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Upgrade ADT field sorts based on nested constructor patterns in
/// expressions. (#1296)
///
/// When match arms like `OwnResult::Ok(Some(x))` or `OwnResult::Ok(None)`
/// appear in the body/postconditions, the `Ok` field sort should be
/// `Datatype("OptionInt")` rather than the default `Int` (from TypeParam).
/// Without this upgrade, the native OwnResult datatype declares `Ok(Int)`,
/// causing a sort mismatch when `Some(sk_t)` (OptionInt-sorted) is passed
/// as an `Ok` argument in Skolemized postconditions.
///
/// Scans all expressions recursively for match arms with nested stdlib
/// constructor patterns (Some/None → OptionInt, Ok/Err → ResultIntInt)
/// inside user-defined ADT constructor arms, upgrading the corresponding
/// field sort in the AdtDecls.
pub(in crate::verify) fn upgrade_adt_field_sorts_from_patterns(
    adt_decls: &mut AdtDecls,
    exprs: &[&PureExpr],
) {
    // Collect evidence: (adt_name, ctor_smt_name, field_index) → target stdlib datatype name
    let mut upgrades: HashMap<(String, String, usize), &'static str> = HashMap::new();

    for expr in exprs {
        collect_nested_stdlib_pattern_evidence(expr, adt_decls, &mut upgrades);
    }

    if crate::trust_wp_debug_enabled() {
        eprintln!("  [adt-field-upgrade] found {} upgrade(s)", upgrades.len());
        for ((adt_name, ctor_smt, field_idx), target_name) in &upgrades {
            eprintln!("    upgrade: {adt_name}.{ctor_smt}[{field_idx}] -> {target_name}");
        }
    }

    // Apply upgrades to the AdtDecls
    //
    // Collect registered ADT names up-front so we can reject upgrades that
    // would overwrite a concrete user-defined datatype field with a stdlib
    // target. Registered ADT names are genuine sorts — never a generic
    // placeholder — so we must not rewrite them. (#2699)
    let registered_adt_names: HashSet<String> = adt_decls.keys().cloned().collect();
    for ((adt_name, ctor_smt, field_idx), target_name) in &upgrades {
        if let Some(decl) = adt_decls.get_mut(adt_name) {
            if let Some(ctor) = decl
                .constructors
                .iter_mut()
                .find(|c| &c.smt_name == ctor_smt)
            {
                if let Some(field) = ctor.fields.get_mut(*field_idx) {
                    if is_upgradable_placeholder_sort(
                        &field.sort,
                        target_name,
                        &registered_adt_names,
                    ) {
                        field.sort = trust_wp_core::formula::ExprSort::Datatype(
                            trust_wp_core::formula::intern_sort_name(target_name),
                        );
                    }
                }
            }
        }
    }
}

/// Return `true` when the current field sort is a placeholder that should be
/// upgraded to `Datatype(target_name)` given pattern evidence.
///
/// Upgradable sorts:
/// - `Int` / `TypeParam(_)` — default placeholder sorts.
/// - `Datatype(name)` where `name` is NOT one of: (a) the target itself
///   (already upgraded, no-op), (b) a known stdlib concrete datatype such as
///   `OptionInt` or `ResultIntInt`, (c) a registered user-defined ADT name.
///   This catches tests/drivers that supply `ExprSort::Datatype("T")` as a
///   generic-parameter placeholder (#2699) without permitting rewrites of
///   concrete datatype field sorts.
///
/// Never upgradable:
/// - `Datatype(name)` where `name` matches the target (already correct) or
///   identifies a concrete stdlib datatype / registered ADT (preserves
///   intentional, specific sorts).
/// - Structural sorts (Bool, Seq, Unit, FMap, Tuple, Ref, MutRef, Float):
///   these are genuine concrete sorts, not placeholders.
fn is_upgradable_placeholder_sort(
    current: &trust_wp_core::formula::ExprSort,
    target_name: &str,
    registered_adt_names: &HashSet<String>,
) -> bool {
    use trust_wp_core::formula::{resolve_sort_name, ExprSort};
    match current {
        ExprSort::Int | ExprSort::TypeParam(_) => true,
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            if name == target_name {
                return false; // idempotent
            }
            if is_concrete_stdlib_datatype_name(&name) {
                return false; // preserve stdlib concrete sort
            }
            if registered_adt_names.contains(&name) {
                return false; // preserve user-declared concrete ADT
            }
            // Placeholder-ish datatype name (e.g., "T", "E", "K", "V") — upgrade.
            true
        }
        _ => false,
    }
}

/// Return `true` when `name` is a concrete stdlib datatype name that must not
/// be overwritten by the pattern-evidence upgrade pass.
fn is_concrete_stdlib_datatype_name(name: &str) -> bool {
    matches!(name, "OptionInt" | "ResultIntInt")
}

/// Recursively scan for match expressions with nested stdlib constructor
/// patterns inside user-defined ADT constructor arms.
fn collect_nested_stdlib_pattern_evidence(
    expr: &PureExpr,
    adt_decls: &AdtDecls,
    out: &mut HashMap<(String, String, usize), &'static str>,
) {
    expr.for_each_recursive(|node| {
        let PureExpr::Match { arms, .. } = node else {
            return;
        };
        for arm in arms {
            let Pattern::Constructor { name, inner } = &arm.pattern else {
                continue;
            };
            // Only process user-defined ADT constructors (not stdlib)
            if stdlib_constructor_target(name).is_some() {
                continue;
            }
            let Some(inner_pattern) = inner else {
                continue;
            };
            // Check if inner pattern uses stdlib constructors
            let stdlib_target = match inner_pattern.as_ref() {
                Pattern::Constructor {
                    name: inner_name, ..
                } => stdlib_constructor_target(inner_name),
                _ => None,
            };
            let Some(target) = stdlib_target else {
                continue;
            };
            let target_name = match target {
                SwitchTarget::OptionInt => "OptionInt",
                SwitchTarget::ResultIntInt => "ResultIntInt",
                _ => continue,
            };
            // Find the ADT declaration that owns this constructor
            let short = short_constructor_name(name);
            for (adt_name, decl) in adt_decls.iter() {
                if let Some(ctor) = decl
                    .constructors
                    .iter()
                    .find(|c| short_constructor_name(&c.rust_name) == short)
                {
                    // Single-field constructors: the nested pattern corresponds
                    // to field 0. Multi-field constructors are not supported for
                    // this upgrade path.
                    if ctor.fields.len() == 1 {
                        out.entry((adt_name.clone(), ctor.smt_name.clone(), 0))
                            .or_insert(target_name);
                    }
                }
            }
        }
    });
}

fn registered_datatype_for_arms(
    registered_datatypes: &[DatatypeSort],
    arms: &[MatchArm],
) -> Option<DatatypeSort> {
    let ctor_names = arms
        .iter()
        .filter_map(|arm| match &arm.pattern {
            Pattern::Constructor { name, .. } => {
                Some(crate::encoder::match_enc::short_constructor_name(name))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    if ctor_names.is_empty() {
        return None;
    }

    let mut matches = registered_datatypes.iter().filter(|dt| {
        ctor_names.iter().all(|ctor_name| {
            dt.constructors
                .iter()
                .any(|constructor| constructor.name == *ctor_name)
        })
    });
    let first = matches.next()?.clone();
    if matches.next().is_some() {
        return None;
    }
    Some(first)
}
