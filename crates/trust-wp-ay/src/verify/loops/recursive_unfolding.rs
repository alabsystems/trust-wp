// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive function one-step unfolding for loop preservation.
//!
//! When a recursive logic function `f(x')` appears in primed loop invariants,
//! ay-dpll needs the one-step unfolding `f(x') = body[x'/param]` as a ground
//! fact. Without it, the UF+LIA theory combination cannot bridge the primed/
//! unprimed argument chain. Extracted from `preservation.rs` per #2591.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use ay_dpll::api::Sort;
use tracing::trace;
use trust_wp_core::{
    formula::{
        expr_has_free_occurrence, internal::tuple_lowering::tuple_field_logic_fn_name,
        resolve_sort_name, BinOp, CaptureAvoidingSubstOptions, ExprSort, MatchArm, Pattern,
        PureExpr,
    },
    logic::LogicFnDef,
};

use crate::{
    encoder::{
        match_enc::short_constructor_name, sort_context::DerivedKind, unsoundness, AYEncoder,
    },
    error::EncodingError,
};

/// A canonical map from a scrutinee term (`format!("{:?}")`) to a KNOWN
/// constructor shape `(short ctor name, field terms)`. Built ONLY from genuine
/// asserted equalities `scrut == Ctor(f0, f1, ...)` so the shape used to reduce a
/// `match` can never disagree with what the solver is told. See
/// `collect_cons_shapes`. (#994 layer-3 prophecy-aware bounded unfold)
type ConsShapes = HashMap<String, (String, Vec<PureExpr>)>;

/// A constructor VALUE at the `PureExpr` level is `LogicFnCall{name, args}` whose
/// name resolves to a datatype constructor. Constructors are Uppercase-initial
/// (`Cons`, `Some`, `Ok`, `Nil`); recursive logic fns are lowercase (`get`,
/// `len`, `sum`). This coarse test only GATES which equalities become shapes; the
/// reducer additionally requires the target `match` arm's `Pattern::Constructor`
/// name to agree, so a misclassification is inert, never unsound.
fn looks_like_constructor_name(name: &str) -> bool {
    short_constructor_name(name)
        .chars()
        .next()
        .is_some_and(char::is_uppercase)
}

/// Sort-INSENSITIVE canonical key for a scrutinee term. `Var` sort annotations
/// differ between the asserted structure fact (`Var("loop_l", None)`) and the
/// invariant occurrence (`Var("loop_l", Some(sort))`), so a raw `{:?}` would miss.
/// The scrutinees we reduce are shallow (`Final(Var)`, `Deref(Var)`, `Var`).
fn canonical_scrut_key(e: &PureExpr) -> String {
    match e {
        PureExpr::Var(n, _) => format!("Var({n})"),
        PureExpr::Final(inner) => format!("Final[{}]", canonical_scrut_key(inner)),
        PureExpr::Deref(inner) => format!("Deref[{}]", canonical_scrut_key(inner)),
        PureExpr::View(inner) => format!("View[{}]", canonical_scrut_key(inner)),
        other => format!("{other:?}"),
    }
}

/// Build the constructor-shape map from asserted structure equalities. Only
/// `scrut == Ctor(fields...)` (either orientation) contributes.
fn collect_cons_shapes(facts: &[PureExpr]) -> ConsShapes {
    let mut shapes = ConsShapes::new();
    for f in facts {
        let PureExpr::BinOp(l, BinOp::Eq, r) = f else {
            continue;
        };
        for (scrut, val) in [(l, r), (r, l)] {
            if let PureExpr::LogicFnCall { name, args } = val.as_ref() {
                if looks_like_constructor_name(name) {
                    let shape = (short_constructor_name(name).to_string(), args.clone());
                    shapes.insert(canonical_scrut_key(scrut.as_ref()), shape.clone());
                    // A recursive logic fn called on a `&mut List` receiver
                    // auto-derefs its argument, so `len(loop_l)`/`get(loop_l,i)`
                    // reach `len`/`get` with the BARE `Var(loop_l)` as the match
                    // scrutinee, not `Deref(loop_l)`. Register the `*loop_l == Cons`
                    // current-value shape under the bare-var key too, so the
                    // current-value match reduces (the prophecy `^loop_l` form is
                    // already bare-keyed via `Final`). SOUND: same asserted shape.
                    if let PureExpr::Deref(inner) = scrut.as_ref() {
                        shapes.insert(canonical_scrut_key(inner.as_ref()), shape);
                    }
                }
            }
        }
    }
    shapes
}

/// Zip a constructor pattern's field bindings against the shape's field terms,
/// e.g. `Cons(x, ls)` against `[^value, ^next]` -> `{x: ^value, ls: ^next}`.
fn collect_field_bindings(
    inner: Option<&Pattern>,
    terms: &[PureExpr],
    out: &mut HashMap<String, PureExpr>,
) -> Option<()> {
    match inner {
        None => terms.is_empty().then_some(()),
        Some(Pattern::Binding(v)) => {
            out.insert(v.clone(), terms.first()?.clone());
            Some(())
        }
        Some(Pattern::Tuple(parts)) => {
            if parts.len() != terms.len() {
                return None;
            }
            for (p, t) in parts.iter().zip(terms) {
                if let Pattern::Binding(v) = p {
                    out.insert(v.clone(), t.clone());
                }
            }
            Some(())
        }
        _ => None,
    }
}

/// If `body` is `match scrut { .. }` and `scrut` has a KNOWN constructor shape,
/// select the matching `Constructor` arm, bind its field pattern-vars to the
/// shape's field terms, and return the reduced arm body. `None` otherwise, so the
/// caller keeps today's unreduced body (no behavior change when no shape is
/// known). SOUND: equivalent to `match` semantics on a value the solver is
/// separately told equals `Ctor(fields...)`, so the reduced equality is entailed
/// by {defining axiom, that asserted equality}.
fn reduce_match_against_known_shapes(
    body: &PureExpr,
    cons_shapes: &ConsShapes,
) -> Option<PureExpr> {
    let PureExpr::Match { scrutinee, arms } = body else {
        return None;
    };
    let key = canonical_scrut_key(scrutinee.as_ref());
    let Some((ctor, field_terms)) = cons_shapes.get(&key) else {
        return None;
    };
    for arm in arms {
        let Pattern::Constructor { name, inner } = &arm.pattern else {
            continue;
        };
        if short_constructor_name(name) != short_constructor_name(ctor) {
            continue;
        }
        let mut binds = HashMap::new();
        collect_field_bindings(inner.as_deref(), field_terms, &mut binds)?;
        return Some(
            arm.body
                .substitute_capture_avoiding(&binds, &capture_options()),
        );
    }
    None
}

/// Assert one-step unfoldings of recursive logic functions at primed arguments.
///
/// For each `f(x_prime)` in the primed invariants where `f` is recursive and
/// `x_prime` maps to a modified variable with body effect `x_prime = x + c`:
///
/// 1. Substitute `x_prime` into the definition body
/// 2. Pre-simplify recursive call arguments using the body effect inverse
///    (e.g., `f(x_prime - 1)` becomes `f(x)` when `x_prime = x + 1`)
/// 3. Assert the simplified definition as a ground fact
///
/// This gives ay the complete one-step unfolding without requiring UF+LIA
/// theory combination to bridge primed/unprimed chains. (#994)
pub(super) fn assert_recursive_fn_unfoldings(
    encoder: &mut AYEncoder,
    primed_invariants: &[PureExpr],
    context_invariants: &[PureExpr],
    structure_facts: &[PureExpr],
    modified_vars: &[&str],
    effects: &HashMap<String, PureExpr>,
    logic_fns: &[LogicFnDef],
) -> Result<(), EncodingError> {
    // Layer-3: constructor shapes from the asserted bridge/structure equalities
    // (e.g. `^loop_l == Cons(^value, ^next)`), used to reduce `match ^loop_l {..}`
    // in the symbolic unfold to a bounded, triggerless ground fact. (#994)
    let cons_shapes = collect_cons_shapes(structure_facts);
    let mut unfoldings = Vec::new();
    for inv in primed_invariants {
        collect_recursive_unfoldings(inv, modified_vars, effects, logic_fns, &mut unfoldings);
    }
    collect_recursive_datatype_unfoldings(
        context_invariants,
        primed_invariants,
        modified_vars,
        logic_fns,
        &mut unfoldings,
    );

    // Fuel-bounded SYMBOLIC unfolding (R bucket): the specialized
    // primed/datatype unfoldings above only fire for recursive calls whose
    // argument is a primed-modified variable (linear body effect) or a
    // datatype value. They miss the general case where a recursive call's
    // argument is an arbitrary SYMBOLIC term — e.g. `loop_l.len()`,
    // `(^loop_l).get(i)`, `sum_of_odd(produced.len())` — for which the
    // suppressed global axiom + literal-only ground evaluation leave `f`
    // uninterpreted, spuriously SAT. Emit the genuine ground instance of the
    // registered defining equation `requires(t) => f(t) == body[t]` at each
    // such symbolic argument term, descending fuel-bounded into nested
    // recursive calls. SOUND (Lean-proven): each emitted instance is a genuine
    // instance of `f`'s true definition, so the batch is equisatisfiable and
    // can never false-accept.
    let mut seen = HashSet::new();
    for inv in context_invariants.iter().chain(primed_invariants.iter()) {
        collect_recursive_fn_symbolic_unfoldings(
            inv,
            logic_fns,
            RECURSIVE_SYMBOLIC_UNFOLD_FUEL,
            &cons_shapes,
            &mut unfoldings,
            &mut seen,
        );
    }

    if unfoldings.is_empty() {
        return Ok(());
    }

    trace!(
        "[#994] assert_recursive_fn_unfoldings: {} bridge(s)",
        unfoldings.len()
    );
    for u in &unfoldings {
        trace!("[#994]   {u:?}");
    }

    encoder.register_sort_hints(&unfoldings);
    encoder.register_formula_sort_hints(&unfoldings);
    for fact in &unfoldings {
        let fact_term = encoder.encode_pure(fact)?;
        encoder.assert_term(fact_term);
    }
    Ok(())
}

/// Off-loop general bounded recursive-logic-fn defining-equation unfolder.
/// (#recursive-unfolder)
///
/// For every recursive, non-opaque logic-fn application `f(t)` occurring in
/// `exprs` (obligation premises and/or negated goal), assert exactly one
/// fuel-1 instance of `f`'s own defining equation `requires(t) => f(t)==body[t]`,
/// reusing the loop-path symbolic core (`collect_recursive_fn_symbolic_unfoldings`)
/// with an EMPTY `ConsShapes` (no loop data / no bridge facts needed off-loop).
/// This supplies the structural facts (e.g. `len(l)==1+match l.1{..}`,
/// `get(l,i)==..`) that recursive-datatype cluster obligations need but which
/// are otherwise absent because recursive fns get NO global defining axiom
/// (registration.rs `skip_global_defining_axiom`).
///
/// COERCION-DROP: a candidate fact whose encoding triggers a
/// `SortCoercionBridge` increment (the recursive self-call argument had to be
/// replaced by a fresh unconstrained constant — severing the recursion
/// relation) is SKIPPED, not asserted. This keeps the coercion-free base/None
/// arm facts (e.g. `¬is_some(l.1) => len(l)==1`) while dropping the boxed
/// recursive arm. Dropping affects only COMPLETENESS.
///
/// SOUND (the hard invariant): every asserted fact is a genuine instance of
/// `f`'s verbatim defining equation (`build_definition_equality` /
/// `emit_symbolic_unfolding_facts` substitute args into `def.body()`, folding
/// `def.requires()` as antecedent — requires-guarding preserved), hence a true
/// logical consequence of the definition the theory already trusts. Adding a
/// true fact can only prune spurious models; it can NEVER turn a genuinely-SAT
/// (real-counterexample) obligation UNSAT. This is the identical invariant the
/// loop path (`assert_recursive_fn_unfoldings`) already relies on.
pub(crate) fn assert_offloop_recursive_defining_unfoldings(
    encoder: &mut AYEncoder,
    exprs: &[PureExpr],
    logic_fns: Option<&[LogicFnDef]>,
) -> Result<(), EncodingError> {
    let Some(logic_fns) = logic_fns else {
        return Ok(());
    };
    let mut unfoldings = Vec::new();
    let mut seen = HashSet::new();
    for e in exprs {
        collect_offloop_case_lifted_unfoldings(e, logic_fns, &mut unfoldings, &mut seen);
    }
    if unfoldings.is_empty() {
        return Ok(());
    }
    encoder.register_sort_hints(&unfoldings);
    encoder.register_formula_sort_hints(&unfoldings);

    let dbg_path = std::env::var_os("TRUST_WP_OFFLOOP_DBG");
    for fact in &unfoldings {
        let before = unsoundness::snapshot();
        let term = encoder.encode_pure(fact)?;
        let after = unsoundness::snapshot();
        let coerced = unsoundness::delta(&before, &after)
            .get(&unsoundness::UnsoundnessCategory::SortCoercionBridge)
            .is_some_and(|&c| c > 0);
        if let Some(ref p) = dbg_path {
            use std::io::Write as _;
            if let Ok(mut f) = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(p)
            {
                let _ = writeln!(f, "[offloop] coerced={coerced} {:.300?}", fact);
            }
        }
        if coerced {
            // DROP the coercing fact (do not assert): its recursion relation was
            // severed, so it is no longer a faithful definition. Keeps the
            // coercion-free sibling facts.
            continue;
        }
        encoder.assert_term(term);
    }
    Ok(())
}

/// Assert local quantified one-step definitions for recursive datatype logic
/// functions reachable from the provided formulas.
///
/// Recursive datatype definitions are not emitted as global foralls because
/// they create expensive and sometimes inconclusive model validation paths.
/// Function/proof-assert obligations still need local definitions when a goal
/// quantifies through a fixed datatype value, such as
/// `forall k. list.get(k) == ...`.
pub(crate) fn assert_recursive_datatype_local_unfoldings(
    encoder: &mut AYEncoder,
    exprs: &[PureExpr],
    logic_fns: &[LogicFnDef],
) -> Result<(), EncodingError> {
    let mut unfoldings = Vec::new();
    let var_sorts = collect_local_var_sorts(encoder, exprs);
    let logic_fns_by_name: HashMap<&str, &LogicFnDef> =
        logic_fns.iter().map(|def| (def.name(), def)).collect();
    let mut binders = Vec::new();
    for expr in exprs {
        collect_recursive_datatype_unfoldings_inner(
            expr,
            None,
            Some(&var_sorts),
            &logic_fns_by_name,
            &mut binders,
            &mut unfoldings,
            0,
        );
    }
    unfoldings.retain(|fact| matches!(fact, PureExpr::Forall { .. }));
    if unfoldings.is_empty() {
        return Ok(());
    }

    trace!(
        "[#994] assert_recursive_datatype_local_unfoldings: {} bridge(s)",
        unfoldings.len()
    );
    for u in &unfoldings {
        trace!("[#994] local unfolding bridge: {u:?}");
    }
    encoder.register_sort_hints(&unfoldings);
    encoder.register_formula_sort_hints(&unfoldings);
    for fact in &unfoldings {
        let fact_term = encoder.encode_pure(fact)?;
        encoder.assert_term(fact_term);
    }
    Ok(())
}

/// For asserted formula contexts, expose a direct quantified body for positive
/// predicate calls whose body delegates to a recursive datatype helper.
///
/// This avoids the hard solver shape `p(args) == forall ...` plus `p(args)`,
/// which can leave the useful quantified fact hidden behind a Boolean equality.
/// We only collect through formula-preserving positive contexts so the emitted
/// body is a consequence of the asserted expression and the defining axiom.
fn collect_positive_quantified_logic_body_unfoldings(
    expr: &PureExpr,
    logic_fns: &HashMap<&str, &LogicFnDef>,
    binders: &mut Vec<ForallBinder>,
    out: &mut Vec<PureExpr>,
) {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            let Some(def) = logic_fns.get(name.as_str()) else {
                return;
            };
            emit_positive_quantified_logic_body(def, args, expr, logic_fns, binders, out);
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let Some(def) = logic_fns.get(method.as_str()) else {
                return;
            };
            let mut call_args = Vec::with_capacity(args.len() + 1);
            call_args.push((**receiver).clone());
            call_args.extend(args.iter().cloned());
            emit_positive_quantified_logic_body(def, &call_args, expr, logic_fns, binders, out);
        }
        PureExpr::BinOp(lhs, BinOp::And, rhs) => {
            collect_positive_quantified_logic_body_unfoldings(lhs, logic_fns, binders, out);
            collect_positive_quantified_logic_body_unfoldings(rhs, logic_fns, binders, out);
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            ..
        } => {
            binders.push(ForallBinder {
                var: var.clone(),
                var_sort: var_sort.clone(),
            });
            collect_positive_quantified_logic_body_unfoldings(body, logic_fns, binders, out);
            binders.pop();
        }
        _ => {}
    }
}

fn emit_positive_quantified_logic_body(
    def: &LogicFnDef,
    args: &[PureExpr],
    trigger: &PureExpr,
    logic_fns: &HashMap<&str, &LogicFnDef>,
    binders: &[ForallBinder],
    out: &mut Vec<PureExpr>,
) {
    let Some(body) = build_positive_quantified_logic_body(def, args, logic_fns) else {
        return;
    };
    let wrapped = wrap_with_relevant_forall_binders(body, binders, trigger);
    if !out.contains(&wrapped) {
        out.push(wrapped);
    }
}

fn build_positive_quantified_logic_body(
    def: &LogicFnDef,
    args: &[PureExpr],
    _logic_fns: &HashMap<&str, &LogicFnDef>,
) -> Option<PureExpr> {
    if def.params().len() != args.len() || !def.requires().is_empty() {
        return None;
    }
    let substitutions: HashMap<String, PureExpr> = def
        .params()
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    let body = def
        .body()
        .substitute_capture_avoiding(&substitutions, &capture_options());
    matches!(body, PureExpr::Forall { .. }).then_some(body)
}

/// Walk a `PureExpr` to find recursive `LogicFnCall` nodes with primed args
/// and build pre-simplified one-step unfoldings.
///
/// Uses `for_each_recursive` for exhaustive variant coverage (#2577).
fn collect_recursive_unfoldings(
    expr: &PureExpr,
    modified_vars: &[&str],
    effects: &HashMap<String, PureExpr>,
    logic_fns: &[LogicFnDef],
    out: &mut Vec<PureExpr>,
) {
    expr.for_each_recursive(|node| {
        let PureExpr::LogicFnCall { name, args } = node else {
            return;
        };
        for (i, arg) in args.iter().enumerate() {
            if let PureExpr::Var(var_name, _) = arg {
                if let Some((DerivedKind::Prime, base)) = DerivedKind::strip_from(var_name) {
                    if !modified_vars.contains(&base) {
                        continue;
                    }
                    let Some(effect) = effects.get(base) else {
                        continue;
                    };
                    let Some(offset) = extract_linear_offset(effect, base) else {
                        continue;
                    };
                    let Some(def) = logic_fns.iter().find(|d| d.name() == name) else {
                        continue;
                    };
                    if !def.is_recursive() || def.params().len() != args.len() {
                        continue;
                    }
                    let param = &def.params()[i];
                    if let Some(simplified_body) = simplify_recursive_body(
                        def.body(),
                        def.name(),
                        def.params(),
                        args,
                        i,
                        param,
                        var_name,
                        base,
                        offset,
                    ) {
                        let primed_call = PureExpr::LogicFnCall {
                            name: name.clone(),
                            args: args.clone(),
                        };
                        emit_unfolding_equality(&primed_call, &simplified_body, out);
                        emit_guarded_positive_branch_unfolding(
                            &primed_call,
                            &simplified_body,
                            var_name,
                            base,
                            offset,
                            out,
                        );
                    }
                }
            }
        }
    });
}

/// Fuel bound for fuel-bounded SYMBOLIC unfolding of recursive logic fns in
/// loop obligations. One unit is spent each time we descend from `f(t)` into
/// the nested recursive applications surfaced by its substituted body.
///
/// Kept LOW (1 level) for the loop path: loop VCs already carry the primed
/// invariant, the negated postcondition, and the specialized primed/datatype
/// unfoldings, so deep symbolic unfolding (fuel 5) bloated `compute_sum_of_odd`
/// / `all_zero` loop obligations into solver timeouts (#R-bucket tuning). One
/// level supplies the missing `f(t) == body[t]` defining equation at the
/// symbolic argument without the combinatorial blowup; deeper levels are left
/// uninterpreted (incompleteness, never unsoundness).
const RECURSIVE_SYMBOLIC_UNFOLD_FUEL: usize = 1;

/// Collect fuel-bounded SYMBOLIC unfolding facts for recursive logic-fn
/// applications reachable from `expr`, regardless of whether their arguments
/// are primed/modified or even constant.
///
/// For each recursive logic-fn application `f(t)` (or method-syntax
/// `recv.f(..)`) occurring in `expr`, emit the genuine ground instance of the
/// REGISTERED defining equation `requires(t) => f(t) == body[t]`, substituting
/// `t` uniformly into both the head and the verbatim body/requires of the
/// `LogicFnDef`. Nested recursive applications surfaced by `body[t]` are
/// unfolded in turn, bounded by `fuel` and deduplicated via `seen`.
///
/// SOUND (Lean-proven, `recursive_logic_fn_bounded_unfolding_soundness`): every
/// emitted instance is a genuine instance of `f`'s true definition, so the
/// batch is equisatisfiable with the bare VC — completeness-only, never
/// false-accept.
fn collect_recursive_fn_symbolic_unfoldings(
    expr: &PureExpr,
    logic_fns: &[LogicFnDef],
    fuel: usize,
    cons_shapes: &ConsShapes,
    out: &mut Vec<PureExpr>,
    seen: &mut HashSet<String>,
) {
    expr.for_each_recursive(|node| {
        let (name, args): (&str, Vec<PureExpr>) = match node {
            PureExpr::LogicFnCall { name, args } => (name.as_str(), args.clone()),
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let mut call_args = Vec::with_capacity(args.len() + 1);
                call_args.push((**receiver).clone());
                call_args.extend(args.iter().cloned());
                (method.as_str(), call_args)
            }
            _ => return,
        };
        let Some(def) = logic_fns
            .iter()
            .find(|d| d.name() == name && d.params().len() == args.len())
        else {
            return;
        };
        // Only recursive, non-opaque, Open fns. Opaque/abstract fns must stay
        // uninterpreted; non-recursive fns already get their global defining
        // axiom and need no fuel.
        if !def.is_recursive() || def.is_opaque() {
            return;
        }

        let substitutions: HashMap<String, PureExpr> = def
            .params()
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        let body = def
            .body()
            .substitute_capture_avoiding(&substitutions, &capture_options());

        // Layer-3 reduction: when the recursive call's argument is a value with a
        // KNOWN constructor shape (e.g. `^loop_l == Cons(^value, ^next)` from the
        // while-let-Cons loop), reduce `match ^loop_l {..}` to the selected arm so
        // the emitted fact is the concrete, bounded one-step unfold
        // `get(^loop_l,i) == ite(i==0, Some(^value), get(^next,i-1))` rather than an
        // inert `get(^loop_l,i) == match ^loop_l {..}`. Triggerless ground form, so
        // no `get(L,i)` E-matching tower is armed. (#994 all_zero_list)
        let reduced = reduce_match_against_known_shapes(&body, cons_shapes);
        let reduction_fired = reduced.is_some();
        let body = reduced.unwrap_or(body);

        // Blowup gate: skip arithmetic-heavy bodies (those introducing
        // multiplication) on the LOOP path. Loop VCs already carry the primed
        // invariant + negated postcondition; injecting a recursive defining
        // equation whose body multiplies a symbolic argument (e.g.
        // `sum_of_odd(x) == sum_of_odd(x-1) + 2*x - 1` at `x = produced.len()`)
        // pushed `compute_sum_of_odd` loop preservation into a solver timeout.
        // The `len`/`get`-style structural bodies (no multiplication) are kept,
        // where the unfolding speeds up preservation without blowup. Gating
        // affects only COMPLETENESS — every skipped instance was a true fact,
        // so dropping it can never cause a false-accept.
        if body_contains_multiplication(&body) {
            return;
        }

        let call = PureExpr::LogicFnCall {
            name: name.to_string(),
            args: args.clone(),
        };
        let requires: Vec<PureExpr> = def
            .requires()
            .iter()
            .map(|req| req.substitute_capture_avoiding(&substitutions, &capture_options()))
            .collect();

        // Layer-5 UNIVERSAL unfold: when the reduction fired against a known
        // constructor shape AND the call's index argument is a bare bound
        // variable (`get(^loop_l, i)` for the invariant's `i`), emit the reduced
        // defining equation as bounded, `[[get(^loop_l,i)]]`-TRIGGERED foralls,
        // split per `ite` branch: `forall i. i==0 => get==Some(^value)` and
        // `forall i. i!=0 => get==get(^scrut_prime,i-1)`. A backward-conditional
        // invariant `P(^loop_l) => P(^old_l)` skolemizes on `get(^old_l,·)` (no
        // shape) and needs the solver to PROVE the universal lemma `P(^loop_l)`,
        // which requires the reduced equation for ALL `i`. SOUND: `get`'s verbatim
        // defining equation specialized to the asserted `^loop_l == Cons(..)`.
        //
        // In this reduced case emit ONLY the foralls: the constant-`i` unfold is
        // subsumed by them, and descending the fuel-recursion into the reduced
        // body would add stuck `get(^scrut_prime,·)` facts that the loop invariant
        // `P` already discharges — both just add quantified/uninterpreted facts
        // that slow E-matching convergence on the lemma. (#994 all_zero_list)
        if reduction_fired {
            if let Some(PureExpr::Var(idx_name, _)) = args.get(1) {
                let idx_name = idx_name.clone();
                emit_forall_unfolding_facts(
                    &call,
                    &body,
                    &idx_name,
                    &requires,
                    &mut Vec::new(),
                    out,
                    seen,
                );
                return;
            }
        }

        let emitted_any =
            emit_symbolic_unfolding_facts(&call, &body, &requires, &mut Vec::new(), out, seen);
        if emitted_any && fuel > 0 {
            collect_recursive_fn_symbolic_unfoldings(
                &body,
                logic_fns,
                fuel - 1,
                cons_shapes,
                out,
                seen,
            );
        }
    });
}

/// Layer-5 analogue of [`emit_symbolic_unfolding_facts`] that emits the UNIVERSAL
/// (forall-quantified, `[[call]]`-triggered) defining-equation fact(s) for
/// `call == body`, splitting an `Ite` body into per-branch guarded foralls. Each
/// leaf becomes `forall idx. (requires && guards) => call == branch` with primary
/// trigger `call`. Used only when the body reduced against a known constructor
/// shape and `call`'s index argument is a bare bound variable, so the emitted
/// foralls are genuine instances of the recursive fn's defining equation at the
/// asserted shape — sound for every `idx`.
fn emit_forall_unfolding_facts(
    call: &PureExpr,
    body: &PureExpr,
    idx_name: &str,
    requires: &[PureExpr],
    guards: &mut Vec<PureExpr>,
    out: &mut Vec<PureExpr>,
    seen: &mut HashSet<String>,
) {
    match body {
        PureExpr::Ite(cond, then_branch, else_branch) => {
            guards.push(cond.as_ref().clone());
            emit_forall_unfolding_facts(call, then_branch, idx_name, requires, guards, out, seen);
            guards.pop();
            guards.push(PureExpr::UnOp(
                trust_wp_core::formula::UnOp::Not,
                Arc::clone(cond),
            ));
            emit_forall_unfolding_facts(call, else_branch, idx_name, requires, guards, out, seen);
            guards.pop();
        }
        _ => {
            let equality =
                PureExpr::BinOp(Arc::new(call.clone()), BinOp::Eq, Arc::new(body.clone()));
            let mut antecedents: Vec<PureExpr> = requires.to_vec();
            antecedents.extend(guards.iter().cloned());
            let inner = if antecedents.is_empty() {
                equality
            } else {
                let antecedent = antecedents
                    .into_iter()
                    .reduce(|lhs, rhs| PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs)))
                    .expect("non-empty antecedents");
                PureExpr::BinOp(Arc::new(antecedent), BinOp::Implies, Arc::new(equality))
            };
            let forall = PureExpr::Forall {
                var: idx_name.to_string(),
                var_sort: None,
                body: Arc::new(inner),
                triggers: vec![vec![call.clone()]],
            };
            if seen.insert(format!("{forall:?}")) {
                out.push(forall);
            }
        }
    }
}

/// Emit the guarded defining-equation fact(s) for `call == body`, splitting an
/// `Ite` body into per-branch guarded equalities and prepending the
/// (substituted) `requires` clauses as guards. Returns `true` if at least one
/// NEW (not previously `seen`) fact was emitted.
fn emit_symbolic_unfolding_facts(
    call: &PureExpr,
    body: &PureExpr,
    requires: &[PureExpr],
    guards: &mut Vec<PureExpr>,
    out: &mut Vec<PureExpr>,
    seen: &mut HashSet<String>,
) -> bool {
    match body {
        PureExpr::Ite(cond, then_branch, else_branch) => {
            guards.push(cond.as_ref().clone());
            let then_emitted =
                emit_symbolic_unfolding_facts(call, then_branch, requires, guards, out, seen);
            guards.pop();

            guards.push(PureExpr::UnOp(
                trust_wp_core::formula::UnOp::Not,
                Arc::clone(cond),
            ));
            let else_emitted =
                emit_symbolic_unfolding_facts(call, else_branch, requires, guards, out, seen);
            guards.pop();

            then_emitted || else_emitted
        }
        _ => {
            let equality =
                PureExpr::BinOp(Arc::new(call.clone()), BinOp::Eq, Arc::new(body.clone()));
            let mut antecedents: Vec<PureExpr> = requires.to_vec();
            antecedents.extend(guards.iter().cloned());
            let fact = if antecedents.is_empty() {
                equality
            } else {
                let antecedent = antecedents
                    .into_iter()
                    .reduce(|lhs, rhs| PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs)))
                    .expect("non-empty antecedents");
                PureExpr::BinOp(Arc::new(antecedent), BinOp::Implies, Arc::new(equality))
            };
            if seen.insert(format!("{fact:?}")) {
                out.push(fact);
                true
            } else {
                false
            }
        }
    }
}

/// Whether `expr` contains a multiplication anywhere (used as a loop-path
/// blowup gate for symbolic recursive unfolding — see
/// `collect_recursive_fn_symbolic_unfoldings`).
fn body_contains_multiplication(expr: &PureExpr) -> bool {
    let mut found = false;
    expr.for_each_recursive(|node| {
        if let PureExpr::BinOp(_, BinOp::Mul, _) = node {
            found = true;
        }
    });
    found
}

// ============================================================================
// Case-lift: split a recursive logic-fn defining equation `call == body` into
// PER-BRANCH guarded facts, so a coercion-bearing arm (e.g. the boxed recursive
// self-call) can be dropped INDEPENDENTLY of a coercion-free base arm. This is
// the decisive off-loop enhancement over `emit_symbolic_unfolding_facts` (which
// only splits `Ite`): it also β-reduces `Let`, splits `Match` (Constructor /
// Bool-Literal arms with first-match guards), and distributes an enclosing
// single-hole arithmetic/logic context (e.g. `1 + match l.1 {..}`) into each
// branch. (#recursive-unfolder)
// ============================================================================

const CASE_LIFT_MAX_DEPTH: usize = 12;

enum ArmTest {
    /// Wildcard/binding arm — always matches (no guard).
    Always,
    /// Positive constructor/literal test for this arm.
    Test(PureExpr),
    /// Unrepresentable pattern — bail (caller falls back to the whole match).
    Unknown,
}

/// Split `call == body` into per-branch guarded defining-equation facts.
pub(crate) fn case_lift_defining_equation(call: &PureExpr, body: &PureExpr) -> Vec<PureExpr> {
    case_lift_guarded_leaves(body, CASE_LIFT_MAX_DEPTH)
        .into_iter()
        .map(|(guards, leaf)| build_guarded_equation(call, &guards, &leaf))
        .collect()
}

/// Reduce `expr` to a list of `(guards, leaf)` where each leaf is branch-free
/// and `guards` are the conditions selecting that branch.
fn case_lift_guarded_leaves(expr: &PureExpr, depth: usize) -> Vec<(Vec<PureExpr>, PureExpr)> {
    if depth == 0 {
        return vec![(Vec::new(), expr.clone())];
    }
    match expr {
        PureExpr::Let { var, value, body } => {
            let mut subs: HashMap<String, PureExpr> = HashMap::new();
            subs.insert(var.clone(), value.as_ref().clone());
            let reduced = body.substitute_capture_avoiding(&subs, &capture_options());
            case_lift_guarded_leaves(&reduced, depth - 1)
        }
        PureExpr::Ite(cond, then_b, else_b) => {
            let mut out = Vec::new();
            for (mut g, v) in case_lift_guarded_leaves(then_b, depth - 1) {
                let mut guards = vec![cond.as_ref().clone()];
                guards.append(&mut g);
                out.push((guards, v));
            }
            for (mut g, v) in case_lift_guarded_leaves(else_b, depth - 1) {
                let mut guards = vec![negate(cond)];
                guards.append(&mut g);
                out.push((guards, v));
            }
            out
        }
        PureExpr::Match { scrutinee, arms } => case_lift_match(scrutinee, arms, depth)
            .unwrap_or_else(|| vec![(Vec::new(), expr.clone())]),
        PureExpr::BinOp(l, op, r) => {
            let lhs = case_lift_guarded_leaves(l, depth - 1);
            let rhs = case_lift_guarded_leaves(r, depth - 1);
            let mut out = Vec::with_capacity(lhs.len() * rhs.len());
            for (lg, lv) in &lhs {
                for (rg, rv) in &rhs {
                    let mut guards = lg.clone();
                    guards.extend(rg.iter().cloned());
                    out.push((
                        guards,
                        PureExpr::BinOp(Arc::new(lv.clone()), *op, Arc::new(rv.clone())),
                    ));
                }
            }
            out
        }
        PureExpr::UnOp(op, inner) => case_lift_guarded_leaves(inner, depth - 1)
            .into_iter()
            .map(|(g, v)| (g, PureExpr::UnOp(*op, Arc::new(v))))
            .collect(),
        _ => vec![(Vec::new(), expr.clone())],
    }
}

/// First-match split of a `Match`: arm `i` fires under
/// `¬test₀ ∧ … ∧ ¬test_{i-1} ∧ testᵢ`; the exhaustive last arm is carried by the
/// accumulated negations alone. Returns `None` on any unrepresentable pattern
/// (caller keeps the whole match as one sound leaf).
fn case_lift_match(
    scrutinee: &PureExpr,
    arms: &[MatchArm],
    depth: usize,
) -> Option<Vec<(Vec<PureExpr>, PureExpr)>> {
    let mut out = Vec::new();
    let mut prior_neg: Vec<PureExpr> = Vec::new();
    for (idx, arm) in arms.iter().enumerate() {
        let is_last = idx + 1 == arms.len();
        let bound_body = bind_arm_body(scrutinee, arm)?;
        if is_last {
            for (mut g, v) in case_lift_guarded_leaves(&bound_body, depth - 1) {
                let mut guards = prior_neg.clone();
                guards.append(&mut g);
                out.push((guards, v));
            }
            break;
        }
        match arm_positive_test(scrutinee, &arm.pattern) {
            ArmTest::Always => {
                for (mut g, v) in case_lift_guarded_leaves(&bound_body, depth - 1) {
                    let mut guards = prior_neg.clone();
                    guards.append(&mut g);
                    out.push((guards, v));
                }
                return Some(out);
            }
            ArmTest::Test(t) => {
                let mut arm_guards = prior_neg.clone();
                arm_guards.push(t.clone());
                for (mut g, v) in case_lift_guarded_leaves(&bound_body, depth - 1) {
                    let mut guards = arm_guards.clone();
                    guards.append(&mut g);
                    out.push((guards, v));
                }
                prior_neg.push(negate(&t));
            }
            ArmTest::Unknown => return None,
        }
    }
    Some(out)
}

/// The positive constructor/literal test that selects `pattern`.
fn arm_positive_test(scrutinee: &PureExpr, pattern: &Pattern) -> ArmTest {
    match pattern {
        Pattern::Wildcard | Pattern::Binding(_) => ArmTest::Always,
        Pattern::Alias { pattern, .. } => arm_positive_test(scrutinee, pattern),
        Pattern::Literal(lit) => match lit {
            PureExpr::Bool(true) => ArmTest::Test(scrutinee.clone()),
            PureExpr::Bool(false) => ArmTest::Test(negate(scrutinee)),
            other => ArmTest::Test(PureExpr::BinOp(
                Arc::new(scrutinee.clone()),
                BinOp::Eq,
                Arc::new(other.clone()),
            )),
        },
        Pattern::Constructor { name, .. } => match constructor_tester_method(name) {
            Some(method) => ArmTest::Test(PureExpr::MethodCall {
                receiver: Arc::new(scrutinee.clone()),
                method: method.to_string(),
                args: Vec::new(),
            }),
            None => ArmTest::Unknown,
        },
        _ => ArmTest::Unknown,
    }
}

/// Substitute the arm's pattern bindings (payload projections of the scrutinee)
/// into the arm body. Returns `None` on an unrepresentable inner pattern.
fn bind_arm_body(scrutinee: &PureExpr, arm: &MatchArm) -> Option<PureExpr> {
    let mut binds: HashMap<String, PureExpr> = HashMap::new();
    collect_arm_bindings(scrutinee, &arm.pattern, &mut binds)?;
    if binds.is_empty() {
        return Some(arm.body.clone());
    }
    Some(
        arm.body
            .substitute_capture_avoiding(&binds, &capture_options()),
    )
}

fn collect_arm_bindings(
    scrutinee: &PureExpr,
    pattern: &Pattern,
    out: &mut HashMap<String, PureExpr>,
) -> Option<()> {
    match pattern {
        Pattern::Wildcard | Pattern::Literal(_) => Some(()),
        Pattern::Binding(v) => {
            out.insert(v.clone(), scrutinee.clone());
            Some(())
        }
        Pattern::Alias { alias, pattern } => {
            out.insert(alias.clone(), scrutinee.clone());
            collect_arm_bindings(scrutinee, pattern, out)
        }
        Pattern::Constructor { name, inner } => {
            let Some(inner) = inner.as_deref() else {
                return Some(());
            };
            match inner {
                Pattern::Binding(v) => {
                    out.insert(v.clone(), constructor_payload_accessor(scrutinee, name)?);
                    Some(())
                }
                Pattern::Wildcard => Some(()),
                Pattern::Tuple(parts) => {
                    for (i, part) in parts.iter().enumerate() {
                        let field = PureExpr::LogicFnCall {
                            name: tuple_field_logic_fn_name(i),
                            args: vec![scrutinee.clone()],
                        };
                        collect_arm_bindings(&field, part, out)?;
                    }
                    Some(())
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The payload accessor for a single-field constructor arm (`Some(x)` → `x =
/// scrut.unwrap()`), matching the encoder's datatype-spec method lowering.
fn constructor_payload_accessor(scrutinee: &PureExpr, ctor_name: &str) -> Option<PureExpr> {
    let method = match short_constructor_name(ctor_name) {
        "Some" | "Ok" => "unwrap",
        "Err" => "unwrap_err",
        _ => return None,
    };
    Some(PureExpr::MethodCall {
        receiver: Arc::new(scrutinee.clone()),
        method: method.to_string(),
        args: Vec::new(),
    })
}

/// The constructor-test method (`Some` → `is_some`) — lowers to the same
/// `is_some__dom_…` tester symbol the negated goal uses.
fn constructor_tester_method(ctor_name: &str) -> Option<&'static str> {
    match short_constructor_name(ctor_name) {
        "Some" => Some("is_some"),
        "None" => Some("is_none"),
        "Ok" => Some("is_ok"),
        "Err" => Some("is_err"),
        _ => None,
    }
}

fn negate(expr: &PureExpr) -> PureExpr {
    if let PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, inner) = expr {
        inner.as_ref().clone()
    } else {
        PureExpr::UnOp(trust_wp_core::formula::UnOp::Not, Arc::new(expr.clone()))
    }
}

fn build_guarded_equation(call: &PureExpr, guards: &[PureExpr], leaf: &PureExpr) -> PureExpr {
    let equality = PureExpr::BinOp(Arc::new(call.clone()), BinOp::Eq, Arc::new(leaf.clone()));
    if guards.is_empty() {
        return equality;
    }
    let antecedent = guards
        .iter()
        .cloned()
        .reduce(|lhs, rhs| PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs)))
        .expect("non-empty guards");
    PureExpr::BinOp(Arc::new(antecedent), BinOp::Implies, Arc::new(equality))
}

/// Off-loop collector: like `collect_recursive_fn_symbolic_unfoldings` but emits
/// PER-BRANCH case-lifted facts (via [`case_lift_defining_equation`]) so a
/// coercion-bearing recursive arm can be dropped without losing the coercion-free
/// base arm. No `ConsShapes` / loop data.
fn collect_offloop_case_lifted_unfoldings(
    expr: &PureExpr,
    logic_fns: &[LogicFnDef],
    out: &mut Vec<PureExpr>,
    seen: &mut HashSet<String>,
) {
    expr.for_each_recursive(|node| {
        let (name, args): (&str, Vec<PureExpr>) = match node {
            PureExpr::LogicFnCall { name, args } => (name.as_str(), args.clone()),
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                let mut call_args = Vec::with_capacity(args.len() + 1);
                call_args.push((**receiver).clone());
                call_args.extend(args.iter().cloned());
                (method.as_str(), call_args)
            }
            _ => return,
        };
        let Some(def) = logic_fns
            .iter()
            .find(|d| d.name() == name && d.params().len() == args.len())
        else {
            return;
        };
        if !def.is_recursive() || def.is_opaque() {
            return;
        }

        let substitutions: HashMap<String, PureExpr> = def
            .params()
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        let body = def
            .body()
            .substitute_capture_avoiding(&substitutions, &capture_options());
        let requires: Vec<PureExpr> = def
            .requires()
            .iter()
            .map(|req| req.substitute_capture_avoiding(&substitutions, &capture_options()))
            .collect();
        let call = PureExpr::LogicFnCall {
            name: name.to_string(),
            args: args.clone(),
        };

        for (mut guards, leaf) in case_lift_guarded_leaves(&body, CASE_LIFT_MAX_DEPTH) {
            // Per-LEAF blowup gate (completeness-only): a base leaf like `1 + 0`
            // survives even if a sibling recursive leaf multiplies.
            if body_contains_multiplication(&leaf) {
                continue;
            }
            let mut all_guards = requires.clone();
            all_guards.append(&mut guards);
            let fact = build_guarded_equation(&call, &all_guards, &leaf);
            if seen.insert(format!("{fact:?}")) {
                out.push(fact);
            }
        }
    });
}

#[derive(Clone, Debug)]
struct ForallBinder {
    var: String,
    var_sort: Option<ExprSort>,
}

const MAX_LOGIC_BODY_EXPANSION_DEPTH: usize = 4;

/// Recursive datatype logic functions intentionally avoid global quantified
/// defining axioms. Loop preservation still needs local one-step definitions
/// when an invariant quantifies through a fixed list/tree value, e.g.
/// `good_bucket(l')` expands to `forall k. get(l', k) ...`.
fn collect_recursive_datatype_unfoldings(
    context_invariants: &[PureExpr],
    primed_invariants: &[PureExpr],
    modified_vars: &[&str],
    logic_fns: &[LogicFnDef],
    out: &mut Vec<PureExpr>,
) {
    let logic_fns_by_name: HashMap<&str, &LogicFnDef> =
        logic_fns.iter().map(|def| (def.name(), def)).collect();
    let modified: HashSet<&str> = modified_vars.iter().copied().collect();
    let mut binders = Vec::new();

    for inv in context_invariants {
        collect_positive_quantified_logic_body_unfoldings(
            inv,
            &logic_fns_by_name,
            &mut binders,
            out,
        );
        collect_recursive_datatype_unfoldings_inner(
            inv,
            Some(&modified),
            None,
            &logic_fns_by_name,
            &mut binders,
            out,
            0,
        );
    }
    for inv in primed_invariants {
        collect_recursive_datatype_unfoldings_inner(
            inv,
            Some(&modified),
            None,
            &logic_fns_by_name,
            &mut binders,
            out,
            0,
        );
    }
}

fn collect_recursive_datatype_unfoldings_inner(
    expr: &PureExpr,
    modified_vars: Option<&HashSet<&str>>,
    var_sorts: Option<&HashMap<String, Sort>>,
    logic_fns: &HashMap<&str, &LogicFnDef>,
    binders: &mut Vec<ForallBinder>,
    out: &mut Vec<PureExpr>,
    expansion_depth: usize,
) {
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            if let Some(def) = logic_fns.get(name.as_str()) {
                if def.is_recursive() {
                    emit_recursive_datatype_call_unfoldings(
                        def,
                        args,
                        binders,
                        modified_vars,
                        var_sorts,
                        out,
                    );
                } else if expansion_depth < MAX_LOGIC_BODY_EXPANSION_DEPTH
                    && def.params().len() == args.len()
                    && body_contains_recursive_logic_call(def.body(), logic_fns)
                {
                    let substitutions: HashMap<String, PureExpr> = def
                        .params()
                        .iter()
                        .cloned()
                        .zip(args.iter().cloned())
                        .collect();
                    let expanded_body = def
                        .body()
                        .substitute_capture_avoiding(&substitutions, &capture_options());
                    collect_recursive_datatype_unfoldings_inner(
                        &expanded_body,
                        modified_vars,
                        var_sorts,
                        logic_fns,
                        binders,
                        out,
                        expansion_depth + 1,
                    );
                }
            }
            for arg in args {
                collect_recursive_datatype_unfoldings_inner(
                    arg,
                    modified_vars,
                    var_sorts,
                    logic_fns,
                    binders,
                    out,
                    expansion_depth,
                );
            }
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        } => {
            binders.push(ForallBinder {
                var: var.clone(),
                var_sort: var_sort.clone(),
            });
            collect_recursive_datatype_unfoldings_inner(
                body,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
            binders.pop();
            for trigger_group in triggers {
                for trigger in trigger_group {
                    collect_recursive_datatype_unfoldings_inner(
                        trigger,
                        modified_vars,
                        var_sorts,
                        logic_fns,
                        binders,
                        out,
                        expansion_depth,
                    );
                }
            }
        }
        PureExpr::Exists { body, triggers, .. } => {
            collect_recursive_datatype_unfoldings_inner(
                body,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
            for trigger_group in triggers {
                for trigger in trigger_group {
                    collect_recursive_datatype_unfoldings_inner(
                        trigger,
                        modified_vars,
                        var_sorts,
                        logic_fns,
                        binders,
                        out,
                        expansion_depth,
                    );
                }
            }
        }
        PureExpr::BinOp(lhs, _, rhs) => {
            collect_recursive_datatype_unfoldings_inner(
                lhs,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
            collect_recursive_datatype_unfoldings_inner(
                rhs,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => collect_recursive_datatype_unfoldings_inner(
            inner,
            modified_vars,
            var_sorts,
            logic_fns,
            binders,
            out,
            expansion_depth,
        ),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_recursive_datatype_unfoldings_inner(
                cond,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
            collect_recursive_datatype_unfoldings_inner(
                then_expr,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
            collect_recursive_datatype_unfoldings_inner(
                else_expr,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            if let Some(def) = logic_fns.get(method.as_str()) {
                let mut call_args = Vec::with_capacity(args.len() + 1);
                call_args.push((**receiver).clone());
                call_args.extend(args.iter().cloned());
                if def.is_recursive() {
                    emit_recursive_datatype_call_unfoldings(
                        def,
                        &call_args,
                        binders,
                        modified_vars,
                        var_sorts,
                        out,
                    );
                } else if expansion_depth < MAX_LOGIC_BODY_EXPANSION_DEPTH
                    && def.params().len() == call_args.len()
                    && body_contains_recursive_logic_call(def.body(), logic_fns)
                {
                    let substitutions: HashMap<String, PureExpr> =
                        def.params().iter().cloned().zip(call_args).collect();
                    let expanded_body = def
                        .body()
                        .substitute_capture_avoiding(&substitutions, &capture_options());
                    collect_recursive_datatype_unfoldings_inner(
                        &expanded_body,
                        modified_vars,
                        var_sorts,
                        logic_fns,
                        binders,
                        out,
                        expansion_depth + 1,
                    );
                }
            }
            collect_recursive_datatype_unfoldings_inner(
                receiver,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
            for arg in args {
                collect_recursive_datatype_unfoldings_inner(
                    arg,
                    modified_vars,
                    var_sorts,
                    logic_fns,
                    binders,
                    out,
                    expansion_depth,
                );
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_recursive_datatype_unfoldings_inner(
                scrutinee,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
            for arm in arms {
                collect_pattern_exprs(
                    &arm.pattern,
                    modified_vars,
                    var_sorts,
                    logic_fns,
                    binders,
                    out,
                );
                collect_recursive_datatype_unfoldings_inner(
                    &arm.body,
                    modified_vars,
                    var_sorts,
                    logic_fns,
                    binders,
                    out,
                    expansion_depth,
                );
            }
        }
        PureExpr::Let { value, body, .. } => {
            collect_recursive_datatype_unfoldings_inner(
                value,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
            collect_recursive_datatype_unfoldings_inner(
                body,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
        }
        PureExpr::LetAssume { assumption, body }
        | PureExpr::LetObligation {
            obligation: assumption,
            body,
        } => {
            collect_recursive_datatype_unfoldings_inner(
                assumption,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
            collect_recursive_datatype_unfoldings_inner(
                body,
                modified_vars,
                var_sorts,
                logic_fns,
                binders,
                out,
                expansion_depth,
            );
        }
        PureExpr::Closure { body, .. } => collect_recursive_datatype_unfoldings_inner(
            body,
            modified_vars,
            var_sorts,
            logic_fns,
            binders,
            out,
            expansion_depth,
        ),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {}
        _ => {}
    }
}

fn collect_pattern_exprs(
    pattern: &Pattern,
    modified_vars: Option<&HashSet<&str>>,
    var_sorts: Option<&HashMap<String, Sort>>,
    logic_fns: &HashMap<&str, &LogicFnDef>,
    binders: &mut Vec<ForallBinder>,
    out: &mut Vec<PureExpr>,
) {
    match pattern {
        Pattern::Literal(expr) => collect_recursive_datatype_unfoldings_inner(
            expr,
            modified_vars,
            var_sorts,
            logic_fns,
            binders,
            out,
            0,
        ),
        Pattern::Constructor {
            inner: Some(inner), ..
        }
        | Pattern::Alias { pattern: inner, .. } => {
            collect_pattern_exprs(inner, modified_vars, var_sorts, logic_fns, binders, out);
        }
        Pattern::Tuple(parts) => {
            for part in parts {
                collect_pattern_exprs(part, modified_vars, var_sorts, logic_fns, binders, out);
            }
        }
        Pattern::Wildcard | Pattern::Binding(_) | Pattern::Constructor { inner: None, .. } => {}
        _ => {}
    }
}

fn body_contains_recursive_logic_call(
    body: &PureExpr,
    logic_fns: &HashMap<&str, &LogicFnDef>,
) -> bool {
    let mut found = false;
    body.for_each_recursive(|node| {
        if found {
            return;
        }
        match node {
            PureExpr::LogicFnCall { name, .. } => {
                found = logic_fns
                    .get(name.as_str())
                    .is_some_and(|def| def.is_recursive());
            }
            PureExpr::MethodCall { method, .. } => {
                found = logic_fns
                    .get(method.as_str())
                    .is_some_and(|def| def.is_recursive());
            }
            _ => {}
        }
    });
    found
}

fn emit_recursive_datatype_call_unfoldings(
    def: &LogicFnDef,
    args: &[PureExpr],
    binders: &[ForallBinder],
    modified_vars: Option<&HashSet<&str>>,
    var_sorts: Option<&HashMap<String, Sort>>,
    out: &mut Vec<PureExpr>,
) {
    if def.params().len() != args.len()
        || !has_relevant_datatype_arg(def, args, modified_vars, var_sorts)
    {
        return;
    }

    emit_one_step_definition(def, args, binders, out);

    let source_args = replace_relevant_prime_args_with_source(args, modified_vars);
    if source_args != args {
        emit_one_step_definition(def, &source_args, binders, out);
    }
}

fn has_relevant_datatype_arg(
    def: &LogicFnDef,
    args: &[PureExpr],
    modified_vars: Option<&HashSet<&str>>,
    var_sorts: Option<&HashMap<String, Sort>>,
) -> bool {
    args.iter().enumerate().any(|(idx, arg)| {
        is_datatype_argument(def, idx, arg, var_sorts) && relevant_datatype_arg(arg, modified_vars)
    })
}

fn is_datatype_argument(
    def: &LogicFnDef,
    idx: usize,
    arg: &PureExpr,
    var_sorts: Option<&HashMap<String, Sort>>,
) -> bool {
    let expected = def.param_sorts().get(idx).and_then(Option::as_ref);
    let Some(ExprSort::Datatype(expected_id)) = expected else {
        return matches!(arg, PureExpr::Var(_, Some(ExprSort::Datatype(_))));
    };
    datatype_arg_matches_expected(arg, *expected_id, var_sorts)
}

fn datatype_arg_matches_expected(
    arg: &PureExpr,
    expected_id: u32,
    var_sorts: Option<&HashMap<String, Sort>>,
) -> bool {
    let PureExpr::Var(name, annotation) = arg else {
        return false;
    };
    if matches!(annotation, Some(ExprSort::Datatype(actual_id)) if *actual_id == expected_id) {
        return true;
    }
    let Some(var_sorts) = var_sorts else {
        return true;
    };
    var_sorts
        .get(name)
        .is_some_and(|sort| sort_matches_datatype(sort, expected_id))
}

fn sort_matches_datatype(sort: &Sort, expected_id: u32) -> bool {
    let expected = resolve_sort_name(expected_id);
    match sort {
        Sort::Datatype(dt) => datatype_names_match(&dt.name, &expected),
        Sort::Uninterpreted(name) => datatype_names_match(name, &expected),
        _ => false,
    }
}

fn datatype_names_match(actual: &str, expected: &str) -> bool {
    actual == expected || actual.rsplit("::").next() == expected.rsplit("::").next()
}

fn collect_local_var_sorts(encoder: &mut AYEncoder, exprs: &[PureExpr]) -> HashMap<String, Sort> {
    let mut vars = HashMap::new();
    for expr in exprs {
        expr.for_each_recursive(|node| {
            if let PureExpr::Var(name, sort) = node {
                vars.entry(name.clone())
                    .or_insert_with(|| PureExpr::Var(name.clone(), sort.clone()));
            }
        });
    }
    vars.into_iter()
        .map(|(name, expr)| {
            let sort = encoder.infer_expr_sort_with_context(&expr, None);
            (name, sort)
        })
        .collect()
}

fn relevant_datatype_arg(arg: &PureExpr, modified_vars: Option<&HashSet<&str>>) -> bool {
    let PureExpr::Var(name, _) = arg else {
        return false;
    };
    let Some(modified_vars) = modified_vars else {
        return true;
    };
    if modified_vars.contains(name.as_str()) {
        return true;
    }
    matches!(
        DerivedKind::strip_from(name),
        Some((DerivedKind::Prime, base)) if modified_vars.contains(base)
    )
}

fn replace_relevant_prime_args_with_source(
    args: &[PureExpr],
    modified_vars: Option<&HashSet<&str>>,
) -> Vec<PureExpr> {
    let Some(modified_vars) = modified_vars else {
        return args.to_vec();
    };
    args.iter()
        .map(|arg| match arg {
            PureExpr::Var(name, sort) => {
                if let Some((DerivedKind::Prime, base)) = DerivedKind::strip_from(name) {
                    if modified_vars.contains(base) {
                        return PureExpr::Var(base.to_string(), sort.clone());
                    }
                }
                arg.clone()
            }
            _ => arg.clone(),
        })
        .collect()
}

fn emit_one_step_definition(
    def: &LogicFnDef,
    args: &[PureExpr],
    binders: &[ForallBinder],
    out: &mut Vec<PureExpr>,
) {
    let args = annotate_args_with_param_sorts(def, args);
    let call = PureExpr::LogicFnCall {
        name: def.name().to_string(),
        args: args.clone(),
    };
    let Some(equality) = build_definition_equality(def, &args, &call) else {
        return;
    };
    let wrapped = wrap_with_relevant_forall_binders(equality, binders, &call);
    if !out.contains(&wrapped) {
        out.push(wrapped);
    }
}

fn annotate_args_with_param_sorts(def: &LogicFnDef, args: &[PureExpr]) -> Vec<PureExpr> {
    args.iter()
        .enumerate()
        .map(
            |(idx, arg)| match (arg, def.param_sorts().get(idx).and_then(Option::as_ref)) {
                (PureExpr::Var(name, None), Some(sort)) => {
                    PureExpr::Var(name.clone(), Some(sort.clone()))
                }
                _ => arg.clone(),
            },
        )
        .collect()
}

fn build_definition_equality(
    def: &LogicFnDef,
    args: &[PureExpr],
    call: &PureExpr,
) -> Option<PureExpr> {
    if def.params().len() != args.len() {
        return None;
    }
    let substitutions: HashMap<String, PureExpr> = def
        .params()
        .iter()
        .cloned()
        .zip(args.iter().cloned())
        .collect();
    let body = def
        .body()
        .substitute_capture_avoiding(&substitutions, &capture_options());
    let equality = PureExpr::BinOp(Arc::new(call.clone()), BinOp::Eq, Arc::new(body));
    if def.requires().is_empty() {
        return Some(equality);
    }

    let requires = def
        .requires()
        .iter()
        .map(|req| req.substitute_capture_avoiding(&substitutions, &capture_options()))
        .reduce(|lhs, rhs| PureExpr::BinOp(Arc::new(lhs), BinOp::And, Arc::new(rhs)))?;
    Some(PureExpr::BinOp(
        Arc::new(requires),
        BinOp::Implies,
        Arc::new(equality),
    ))
}

fn wrap_with_relevant_forall_binders(
    body: PureExpr,
    binders: &[ForallBinder],
    trigger: &PureExpr,
) -> PureExpr {
    let options = capture_options();
    let relevant_binders: Vec<&ForallBinder> = binders
        .iter()
        .filter(|binder| expr_has_free_occurrence(&body, &binder.var, &options))
        .collect();
    relevant_binders
        .into_iter()
        .rev()
        .fold(body, |acc, binder| {
            let triggers = if expr_has_free_occurrence(trigger, &binder.var, &options) {
                vec![vec![trigger.clone()]]
            } else {
                Vec::new()
            };
            PureExpr::Forall {
                var: binder.var.clone(),
                var_sort: binder.var_sort.clone(),
                body: Arc::new(acc),
                triggers,
            }
        })
}

fn capture_options() -> CaptureAvoidingSubstOptions {
    CaptureAvoidingSubstOptions {
        depth_limit: Some(crate::encoder::MAX_ENCODING_DEPTH),
    }
}

/// Emit the one-step unfolding as a direct equality: `call = body`.
///
/// The body may contain an ITE structure from the recursive function
/// definition — this is correct and the solver handles ITE evaluation.
fn emit_unfolding_equality(call: &PureExpr, body: &PureExpr, out: &mut Vec<PureExpr>) {
    out.push(PureExpr::BinOp(
        Arc::new(call.clone()),
        BinOp::Eq,
        Arc::new(body.clone()),
    ));
}

fn emit_guarded_positive_branch_unfolding(
    call: &PureExpr,
    body: &PureExpr,
    primed_var: &str,
    base_var: &str,
    offset: i64,
    out: &mut Vec<PureExpr>,
) {
    if offset <= 0 {
        return;
    }
    let PureExpr::Ite(condition, _, positive_branch) = body else {
        return;
    };
    if !is_nonpositive_primed_condition(condition, primed_var) {
        return;
    }

    let guard = PureExpr::BinOp(
        Arc::new(PureExpr::Var(base_var.to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );
    let branch_eq = PureExpr::BinOp(Arc::new(call.clone()), BinOp::Eq, positive_branch.clone());
    out.push(PureExpr::BinOp(
        Arc::new(guard),
        BinOp::Implies,
        Arc::new(branch_eq),
    ));
}

fn is_nonpositive_primed_condition(condition: &PureExpr, primed_var: &str) -> bool {
    let PureExpr::BinOp(lhs, op, rhs) = condition else {
        return false;
    };
    match op {
        BinOp::Le => is_var_named(lhs, primed_var) && matches!(rhs.as_ref(), PureExpr::Int(0)),
        BinOp::Ge => matches!(lhs.as_ref(), PureExpr::Int(0)) && is_var_named(rhs, primed_var),
        _ => false,
    }
}

fn is_var_named(expr: &PureExpr, expected: &str) -> bool {
    matches!(expr, PureExpr::Var(name, _) if name == expected)
}

/// Build a simplified one-step unfolding of a recursive function body.
///
/// Produces the genuine defining-equation instance `f(call_args) == body`,
/// substituting EVERY parameter `p_m` with the call's actual argument
/// `call_args[m]` (not just the single primed parameter). Multi-parameter
/// recursive functions — e.g. `num_of_pos(i, j, t)` called as
/// `num_of_pos(0, i', t)` — otherwise left the non-primed params (`i`, `t`)
/// as their bare parameter names, producing a malformed (and, under loop
/// variable name collisions, false) unfolding. (filter_positive residual)
///
/// In recursive subcalls, the argument at the primed index (`param ± k`, with
/// `param := primed_var = base_var + offset`) is rewritten to
/// `base_var + (offset ± k)` so that the `offset ∓ 1 == 0` case collapses to
/// `base_var`, bridging the primed chain (`f(.., i', ..)`) directly to the
/// unprimed term (`f(.., i, ..)`) the invariant already constrains. This is
/// SOUND: `primed_var = base_var + offset` is a true body-effect fact, so the
/// rewritten argument is provably equal and the whole equation remains a
/// genuine instance of `f`'s definition.
#[allow(clippy::too_many_arguments)]
fn simplify_recursive_body(
    body: &PureExpr,
    fn_name: &str,
    params: &[String],
    call_args: &[PureExpr],
    primed_index: usize,
    param: &str,
    primed_var: &str,
    base_var: &str,
    offset: i64,
) -> Option<PureExpr> {
    // Substitution for every parameter -> its actual call argument. The primed
    // parameter is excluded here and handled structurally below so that its
    // recursive-subcall occurrences (`param ± k`) get the offset rewrite.
    let mut head_subs: HashMap<String, PureExpr> = HashMap::new();
    if params.len() == call_args.len() {
        for (p, a) in params.iter().zip(call_args.iter()) {
            if p != param {
                head_subs.insert(p.clone(), a.clone());
            }
        }
    } else {
        return None;
    }
    simplify_body_inner(
        body,
        fn_name,
        &head_subs,
        param,
        primed_index,
        primed_var,
        base_var,
        offset,
    )
}

#[allow(clippy::too_many_arguments)]
fn simplify_body_inner(
    expr: &PureExpr,
    fn_name: &str,
    head_subs: &HashMap<String, PureExpr>,
    param: &str,
    primed_index: usize,
    primed_var: &str,
    base_var: &str,
    offset: i64,
) -> Option<PureExpr> {
    match expr {
        PureExpr::Var(name, sort) => {
            if name == param {
                Some(PureExpr::Var(primed_var.to_string(), sort.clone()))
            } else if let Some(replacement) = head_subs.get(name) {
                // Non-primed parameter: bind to the call's actual argument.
                Some(replacement.clone())
            } else {
                Some(expr.clone())
            }
        }
        PureExpr::LogicFnCall { name, args } if name == fn_name => {
            // Recursive call: rewrite the primed-index argument via the body
            // effect offset; bind every other argument's parameter occurrences
            // to the call's actual arguments.
            let mut simplified_args = Vec::with_capacity(args.len());
            for (idx, arg) in args.iter().enumerate() {
                let simplified = if idx == primed_index {
                    simplify_recursive_arg(arg, param, base_var, offset)?
                } else {
                    simplify_body_inner(
                        arg,
                        fn_name,
                        head_subs,
                        param,
                        primed_index,
                        primed_var,
                        base_var,
                        offset,
                    )?
                };
                simplified_args.push(simplified);
            }
            Some(PureExpr::LogicFnCall {
                name: name.clone(),
                args: simplified_args,
            })
        }
        PureExpr::LogicFnCall { name, args } => {
            let mut new_args = Vec::with_capacity(args.len());
            for arg in args {
                new_args.push(simplify_body_inner(
                    arg,
                    fn_name,
                    head_subs,
                    param,
                    primed_index,
                    primed_var,
                    base_var,
                    offset,
                )?);
            }
            Some(PureExpr::LogicFnCall {
                name: name.clone(),
                args: new_args,
            })
        }
        // Rewrite a `param ± k` offset subexpression directly to the unprimed
        // base term (`base_var + (offset ∓ k)`) wherever it appears — not only
        // inside recursive subcalls. For `param = primed_var = base_var + offset`
        // this is a provably-equal substitution, so it stays sound. Crucially it
        // makes element accesses inside the body's GUARDS (e.g. `t[j-1]` at
        // `j = i'`, offset 1) collapse to `t[i]`, sharing the SAME SMT term as
        // the loop's accumulator body-effect guard (`t[i] > 0`). Without this the
        // recurrence's `ite(t[i'-1] > 0, ...)` and the effect's `ite(t[i] > 0, ...)`
        // carry distinct (index-congruent but syntactically different) guards, so
        // the two ites never cancel under ay-dpll's single-round E-matching.
        PureExpr::BinOp(l, op, r)
            if matches!(op, BinOp::Add | BinOp::Sub)
                && matches!(
                    (l.as_ref(), r.as_ref()),
                    (PureExpr::Var(name, _), PureExpr::Int(_)) if name == param
                ) =>
        {
            // `param ± k` collapses to `base_var + (offset ∓ k)`.
            simplify_recursive_arg(expr, param, base_var, offset)
        }
        PureExpr::BinOp(l, op, r) => {
            let l2 = simplify_body_inner(
                l,
                fn_name,
                head_subs,
                param,
                primed_index,
                primed_var,
                base_var,
                offset,
            )?;
            let r2 = simplify_body_inner(
                r,
                fn_name,
                head_subs,
                param,
                primed_index,
                primed_var,
                base_var,
                offset,
            )?;
            Some(PureExpr::BinOp(Arc::new(l2), *op, Arc::new(r2)))
        }
        PureExpr::Ite(c, t, e) => {
            let c2 = simplify_body_inner(
                c,
                fn_name,
                head_subs,
                param,
                primed_index,
                primed_var,
                base_var,
                offset,
            )?;
            let t2 = simplify_body_inner(
                t,
                fn_name,
                head_subs,
                param,
                primed_index,
                primed_var,
                base_var,
                offset,
            )?;
            let e2 = simplify_body_inner(
                e,
                fn_name,
                head_subs,
                param,
                primed_index,
                primed_var,
                base_var,
                offset,
            )?;
            Some(PureExpr::Ite(Arc::new(c2), Arc::new(t2), Arc::new(e2)))
        }
        PureExpr::UnOp(op, inner) => {
            let inner2 = simplify_body_inner(
                inner,
                fn_name,
                head_subs,
                param,
                primed_index,
                primed_var,
                base_var,
                offset,
            )?;
            Some(PureExpr::UnOp(*op, Arc::new(inner2)))
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            // `t[j-1]`-style indexing in the body surfaces as a method call
            // (e.g. `seq.get(j-1)`); recurse so the non-primed receiver/args get
            // their parameter -> call-argument bindings too.
            let recv2 = simplify_body_inner(
                receiver,
                fn_name,
                head_subs,
                param,
                primed_index,
                primed_var,
                base_var,
                offset,
            )?;
            let mut new_args = Vec::with_capacity(args.len());
            for arg in args {
                new_args.push(simplify_body_inner(
                    arg,
                    fn_name,
                    head_subs,
                    param,
                    primed_index,
                    primed_var,
                    base_var,
                    offset,
                )?);
            }
            Some(PureExpr::MethodCall {
                receiver: Arc::new(recv2),
                method: method.clone(),
                args: new_args,
            })
        }
        // Transparent unary wrappers (`x@`, `*x`, `old(x)`, `^x`): recurse into
        // the inner expression so element accesses like `t[j-1]@` (which surface
        // as `View(index_logic(t, j-1))`) still get their `param ± k` offset
        // rewrites and non-primed parameter bindings. Without this the whole
        // unfolding is dropped for any body that views/derefs through a recursive
        // index — exactly the `t[j-1]@` shape in `num_of_pos`.
        PureExpr::View(inner) => Some(PureExpr::View(Arc::new(simplify_body_inner(
            inner,
            fn_name,
            head_subs,
            param,
            primed_index,
            primed_var,
            base_var,
            offset,
        )?))),
        PureExpr::Deref(inner) => Some(PureExpr::Deref(Arc::new(simplify_body_inner(
            inner,
            fn_name,
            head_subs,
            param,
            primed_index,
            primed_var,
            base_var,
            offset,
        )?))),
        PureExpr::Old(inner) => Some(PureExpr::Old(Arc::new(simplify_body_inner(
            inner,
            fn_name,
            head_subs,
            param,
            primed_index,
            primed_var,
            base_var,
            offset,
        )?))),
        PureExpr::Final(inner) => Some(PureExpr::Final(Arc::new(simplify_body_inner(
            inner,
            fn_name,
            head_subs,
            param,
            primed_index,
            primed_var,
            base_var,
            offset,
        )?))),
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => Some(expr.clone()),
        // For unsupported structures, bail out rather than produce incorrect output.
        _ => None,
    }
}

/// Simplify a recursive call argument using the body effect offset.
///
/// Pattern: `param ± k` with body effect `primed = base + offset`
/// → `base + (offset ± k)` where ± follows the original operation.
/// When the result offset is 0, returns just `Var(base)`.
fn simplify_recursive_arg(
    arg: &PureExpr,
    param: &str,
    base_var: &str,
    offset: i64,
) -> Option<PureExpr> {
    match arg {
        // Pattern: param - k  or  param + k
        PureExpr::BinOp(lhs, op, rhs) => {
            if let (PureExpr::Var(name, _), PureExpr::Int(k)) = (lhs.as_ref(), rhs.as_ref()) {
                if name == param {
                    let effective = match op {
                        BinOp::Sub => offset - k,
                        BinOp::Add => offset + k,
                        _ => return None,
                    };
                    return Some(make_offset_expr(base_var, effective));
                }
            }
            None
        }
        // Pattern: just param (no offset)
        PureExpr::Var(name, _) if name == param => Some(make_offset_expr(base_var, offset)),
        _ => None,
    }
}

/// Build `Var(base) + offset` or just `Var(base)` when offset is 0.
fn make_offset_expr(base_var: &str, offset: i64) -> PureExpr {
    match offset.cmp(&0) {
        std::cmp::Ordering::Equal => PureExpr::Var(base_var.to_string(), None),
        std::cmp::Ordering::Greater => PureExpr::BinOp(
            Arc::new(PureExpr::Var(base_var.to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(offset)),
        ),
        std::cmp::Ordering::Less => PureExpr::BinOp(
            Arc::new(PureExpr::Var(base_var.to_string(), None)),
            BinOp::Sub,
            Arc::new(PureExpr::Int(-offset)),
        ),
    }
}

/// Extract the linear offset from a body effect expression.
///
/// Returns `Some(c)` if `effect` matches `Var(base_var) + c` or `Var(base_var) - c`,
/// or `Some(0)` if `effect` is just `Var(base_var)`.
fn extract_linear_offset(effect: &PureExpr, base_var: &str) -> Option<i64> {
    match effect {
        PureExpr::BinOp(lhs, op, rhs) => {
            if let (PureExpr::Var(name, _), PureExpr::Int(c)) = (lhs.as_ref(), rhs.as_ref()) {
                if name == base_var {
                    return match op {
                        BinOp::Add => Some(*c),
                        BinOp::Sub => Some(-*c),
                        _ => None,
                    };
                }
            }
            None
        }
        PureExpr::Var(name, _) if name == base_var => Some(0),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use trust_wp_core::formula::MatchArm;

    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn method(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: method.to_string(),
            args,
        }
    }

    #[test]
    fn case_lift_len_body_yields_coercion_free_none_arm() {
        // len(l) = { let ls = l.1; 1 + match ls { Some(ls) => ls.len(), None => 0 } }
        let body = PureExpr::Let {
            var: "ls".to_string(),
            value: Arc::new(PureExpr::LogicFnCall {
                name: "__trust_wp_tuple_get_1".to_string(),
                args: vec![var("l")],
            }),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Int(1)),
                BinOp::Add,
                Arc::new(PureExpr::Match {
                    scrutinee: Arc::new(var("ls")),
                    arms: vec![
                        MatchArm {
                            pattern: Pattern::Constructor {
                                name: "Some".to_string(),
                                inner: Some(Box::new(Pattern::Binding("ls".to_string()))),
                            },
                            body: method(var("ls"), "len", vec![]),
                        },
                        MatchArm {
                            pattern: Pattern::Constructor {
                                name: "None".to_string(),
                                inner: None,
                            },
                            body: PureExpr::Int(0),
                        },
                    ],
                }),
            )),
        };
        let call = PureExpr::LogicFnCall {
            name: "len".to_string(),
            args: vec![var("l")],
        };

        let facts = case_lift_defining_equation(&call, &body);
        let all = facts
            .iter()
            .map(|f| format!("{f:?}"))
            .collect::<Vec<_>>()
            .join("\n");
        assert_eq!(facts.len(), 2, "expected 2 per-arm facts:\n{all}");

        // The whole point: COERCION-FREE None arm  ¬is_some(l.1) => len(l) == 1 + 0.
        let none = facts
            .iter()
            .find(|f| !format!("{f:?}").contains("unwrap"))
            .expect("coercion-free None-arm fact");
        let none = format!("{none:?}");
        assert!(none.contains("Implies"), "None fact is guarded: {none}");
        assert!(
            none.contains("is_some") && none.contains("Not"),
            "None guard is ¬is_some(l.1): {none}"
        );
        assert!(
            none.contains("__trust_wp_tuple_get_1"),
            "guard tests l.1: {none}"
        );
        assert!(none.contains("Int(0)"), "None leaf is 1 + 0: {none}");

        // Recursive Some arm  is_some(l.1) => len(l) == 1 + (l.1).unwrap().len().
        let some = facts
            .iter()
            .find(|f| format!("{f:?}").contains("unwrap"))
            .expect("recursive Some-arm fact");
        let some = format!("{some:?}");
        assert!(some.contains("is_some"), "Some guard uses is_some: {some}");
        assert!(
            some.contains("\"len\""),
            "Some leaf recurses into len: {some}"
        );
    }

    #[test]
    fn case_lift_get_double_match_body_splits_all_three_arms() {
        // get(xs,i) = { let (v,ls)=(xs.0,xs.1);
        //   match i>0 { false => Some(v),
        //               true  => match ls { Some(l) => l.get(i-1), None => None } } }
        let i_gt_0 = PureExpr::BinOp(Arc::new(var("i")), BinOp::Gt, Arc::new(PureExpr::Int(0)));
        let i_minus_1 = PureExpr::BinOp(Arc::new(var("i")), BinOp::Sub, Arc::new(PureExpr::Int(1)));
        let inner_match = PureExpr::Match {
            scrutinee: Arc::new(var("ls")),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "Some".to_string(),
                        inner: Some(Box::new(Pattern::Binding("l".to_string()))),
                    },
                    body: method(var("l"), "get", vec![i_minus_1]),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: "None".to_string(),
                        inner: None,
                    },
                    body: PureExpr::LogicFnCall {
                        name: "None".to_string(),
                        args: vec![],
                    },
                },
            ],
        };
        let body = PureExpr::Let {
            var: "v".to_string(),
            value: Arc::new(PureExpr::LogicFnCall {
                name: "__trust_wp_tuple_get_0".to_string(),
                args: vec![var("xs")],
            }),
            body: Arc::new(PureExpr::Let {
                var: "ls".to_string(),
                value: Arc::new(PureExpr::LogicFnCall {
                    name: "__trust_wp_tuple_get_1".to_string(),
                    args: vec![var("xs")],
                }),
                body: Arc::new(PureExpr::Match {
                    scrutinee: Arc::new(i_gt_0),
                    arms: vec![
                        MatchArm {
                            pattern: Pattern::Literal(PureExpr::Bool(false)),
                            body: PureExpr::LogicFnCall {
                                name: "Some".to_string(),
                                args: vec![var("v")],
                            },
                        },
                        MatchArm {
                            pattern: Pattern::Literal(PureExpr::Bool(true)),
                            body: inner_match,
                        },
                    ],
                }),
            }),
        };
        let call = PureExpr::LogicFnCall {
            name: "get".to_string(),
            args: vec![var("xs"), var("i")],
        };

        let facts = case_lift_defining_equation(&call, &body);
        let all = facts
            .iter()
            .map(|f| format!("{f:?}"))
            .collect::<Vec<_>>()
            .join("\n");
        assert_eq!(facts.len(), 3, "expected 3 per-arm facts:\n{all}");

        // Recursive arm: (i>0) && is_some(xs.1) => get == xs.1.unwrap().get(i-1).
        assert!(
            facts.iter().any(|f| {
                let s = format!("{f:?}");
                s.contains("unwrap") && s.contains("is_some")
            }),
            "recursive arm missing:\n{all}"
        );

        // COERCION-FREE base: (i>0) && ¬is_some(xs.1) => get == None().
        let none = facts
            .iter()
            .find(|f| {
                let s = format!("{f:?}");
                !s.contains("unwrap") && s.contains("is_some")
            })
            .expect("coercion-free None base fact");
        let none = format!("{none:?}");
        assert!(
            none.contains("Not") && none.contains("__trust_wp_tuple_get_1"),
            "None base guard is (i>0) && ¬is_some(xs.1): {none}"
        );

        // Index-boundary arm: ¬(i>0) => get == Some(xs.0).
        assert!(
            facts.iter().any(|f| {
                let s = format!("{f:?}");
                !s.contains("unwrap")
                    && !s.contains("is_some")
                    && s.contains("__trust_wp_tuple_get_0")
            }),
            "index-zero Some(xs.0) arm missing:\n{all}"
        );
    }

    /// `num_of_pos(i, j, t)` from filter_positive: counts positive elements of
    /// `t` in `[i, j)`. Three parameters; the loop primes the upper bound `j`.
    fn num_of_pos_def() -> LogicFnDef {
        // if i >= j then 0
        // else if t[j-1]@ > 0 then num_of_pos(i, j-1, t) + 1 else num_of_pos(i, j-1, t)
        let rec = |upper: PureExpr| PureExpr::LogicFnCall {
            name: "num_of_pos".to_string(),
            args: vec![var("i"), upper, var("t")],
        };
        let elem = PureExpr::View(Arc::new(method(
            var("t"),
            "index_logic",
            vec![PureExpr::BinOp(
                Arc::new(var("j")),
                BinOp::Sub,
                Arc::new(PureExpr::Int(1)),
            )],
        )));
        let body = PureExpr::Ite(
            Arc::new(PureExpr::BinOp(
                Arc::new(var("i")),
                BinOp::Ge,
                Arc::new(var("j")),
            )),
            Arc::new(PureExpr::Int(0)),
            Arc::new(PureExpr::Ite(
                Arc::new(PureExpr::BinOp(
                    Arc::new(elem),
                    BinOp::Gt,
                    Arc::new(PureExpr::Int(0)),
                )),
                Arc::new(PureExpr::BinOp(
                    Arc::new(rec(PureExpr::BinOp(
                        Arc::new(var("j")),
                        BinOp::Sub,
                        Arc::new(PureExpr::Int(1)),
                    ))),
                    BinOp::Add,
                    Arc::new(PureExpr::Int(1)),
                )),
                Arc::new(rec(PureExpr::BinOp(
                    Arc::new(var("j")),
                    BinOp::Sub,
                    Arc::new(PureExpr::Int(1)),
                ))),
            )),
        );
        let mut def = LogicFnDef::new(
            "num_of_pos".to_string(),
            "test::num_of_pos".to_string(),
            vec!["i".to_string(), "j".to_string(), "t".to_string()],
            body,
        );
        def.set_is_recursive(true);
        def
    }

    /// The one-step primed unfolding of a MULTI-parameter recursive function
    /// must substitute EVERY parameter with the call's actual argument — not
    /// just the single primed parameter. For `num_of_pos(0, i', t)` (called with
    /// lower bound `0`) the produced body must reference `num_of_pos(0, i, t)`
    /// (lower bound `0`, upper bound the unprimed `i`), and its guard must read
    /// `t[i]@` with the bare unprimed index. The previous single-parameter
    /// substitution left the lower bound as the parameter name `i`, producing
    /// the WRONG term `num_of_pos(i, i, t)` (== 0), and left the guard at the
    /// primed index `t[i'-1]@`, which never shares a term with the loop's
    /// accumulator effect guard `t[i] > 0`.
    #[test]
    fn multi_param_primed_unfolding_substitutes_all_params_and_collapses_index() {
        let def = num_of_pos_def();
        // Call site as it appears in the primed invariant: num_of_pos(0, i', t).
        let primed_call_args = vec![var("i_prime"), var("t")];
        let _ = &primed_call_args;
        let mut effects: HashMap<String, PureExpr> = HashMap::new();
        effects.insert(
            "i".to_string(),
            PureExpr::BinOp(Arc::new(var("i")), BinOp::Add, Arc::new(PureExpr::Int(1))),
        );
        let modified_vars: Vec<&str> = vec!["i"];
        let primed_invariant = PureExpr::BinOp(
            Arc::new(var("count_prime")),
            BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: "num_of_pos".to_string(),
                args: vec![PureExpr::Int(0), var("i_prime"), var("t")],
            }),
        );

        let mut out = Vec::new();
        collect_recursive_unfoldings(
            &primed_invariant,
            &modified_vars,
            &effects,
            std::slice::from_ref(&def),
            &mut out,
        );

        // Must have emitted at least the head equality.
        assert!(!out.is_empty(), "primed unfolding should be emitted");

        let rendered = format!("{out:?}");
        // SOUND multi-parameter substitution: the recursive subcalls in the body
        // bind to the call's actual lower bound `0`, NOT the parameter name `i`.
        assert!(
            rendered.contains("Int(0)"),
            "lower bound must be substituted with the actual call argument 0: {rendered}"
        );
        assert!(
            !rendered.contains("num_of_pos\", args: [Var(\"i\""),
            "must NOT produce the false term num_of_pos(i, ..) from leaving the \
             lower-bound parameter unsubstituted: {rendered}"
        );
        // The body's recursive subcall upper bound `j-1` at `j = i' = i + 1`
        // collapses to the bare unprimed `i`, sharing the loop accumulator's
        // index term.
        assert!(
            rendered.contains("Var(\"i\""),
            "the j-1 offset must collapse to the bare unprimed index i: {rendered}"
        );
        // The guard element access must also collapse to the bare index i, NOT
        // remain at the primed index i'-1.
        assert!(
            !rendered.contains("i_prime\", None), Int(1)"),
            "the guard/element index must collapse off the primed variable: {rendered}"
        );
    }

    #[test]
    fn local_definition_unfolding_avoids_match_pattern_capture() {
        let body = PureExpr::Match {
            scrutinee: Arc::new(PureExpr::Var("self".to_string(), None)),
            arms: vec![MatchArm {
                pattern: Pattern::Constructor {
                    name: "Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("k".to_string()),
                        Pattern::Binding("tail".to_string()),
                    ]))),
                },
                body: PureExpr::BinOp(Arc::new(var("k")), BinOp::Eq, Arc::new(var("index"))),
            }],
        };
        let def = LogicFnDef::new(
            "get".to_string(),
            "test::get".to_string(),
            vec!["self".to_string(), "index".to_string()],
            body,
        );
        let call = PureExpr::LogicFnCall {
            name: "get".to_string(),
            args: vec![var("l"), var("k")],
        };
        let Some(PureExpr::BinOp(_, BinOp::Eq, rhs)) =
            build_definition_equality(&def, &[var("l"), var("k")], &call)
        else {
            panic!("definition equality");
        };
        let PureExpr::Match { arms, .. } = rhs.as_ref() else {
            panic!("expected match body");
        };
        let arm_body = &arms[0].body;

        assert!(
            expr_has_free_occurrence(arm_body, "k", &capture_options()),
            "substituted outer key must remain free under a match arm that also binds k"
        );
    }

    #[test]
    fn positive_method_predicate_unfolding_emits_quantified_body() {
        let mut get_def = LogicFnDef::new(
            "get".to_string(),
            "test::get".to_string(),
            vec!["self".to_string(), "key".to_string()],
            PureExpr::LogicFnCall {
                name: "get".to_string(),
                args: vec![var("tail"), var("key")],
            },
        );
        get_def.set_is_recursive(true);

        let good_bucket_body = PureExpr::Forall {
            var: "k".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::Forall {
                var: "v".to_string(),
                var_sort: None,
                body: Arc::new(PureExpr::BinOp(
                    Arc::new(PureExpr::BinOp(
                        Arc::new(method(var("l"), "get", vec![var("k")])),
                        BinOp::Eq,
                        Arc::new(var("v")),
                    )),
                    BinOp::Implies,
                    Arc::new(PureExpr::BinOp(
                        Arc::new(method(var("self"), "bucket_ix", vec![var("k")])),
                        BinOp::Eq,
                        Arc::new(var("h")),
                    )),
                )),
                triggers: Vec::new(),
            }),
            triggers: Vec::new(),
        };
        let good_bucket_def = LogicFnDef::new(
            "good_bucket".to_string(),
            "test::good_bucket".to_string(),
            vec!["self".to_string(), "l".to_string(), "h".to_string()],
            good_bucket_body,
        );
        let logic_fns_by_name: HashMap<&str, &LogicFnDef> = [&get_def, &good_bucket_def]
            .into_iter()
            .map(|def| (def.name(), def))
            .collect();

        let asserted = method(
            var("old_self"),
            "good_bucket",
            vec![var("bucket"), var("i")],
        );
        let mut out = Vec::new();
        collect_positive_quantified_logic_body_unfoldings(
            &asserted,
            &logic_fns_by_name,
            &mut Vec::new(),
            &mut out,
        );

        assert_eq!(out.len(), 1);
        assert!(matches!(out[0], PureExpr::Forall { .. }));
        assert!(
            expr_has_free_occurrence(&out[0], "old_self", &capture_options()),
            "receiver should be substituted into the direct body"
        );
        assert!(
            expr_has_free_occurrence(&out[0], "bucket", &capture_options()),
            "datatype argument should be substituted into the direct body"
        );
        assert!(
            !expr_has_free_occurrence(&out[0], "self", &capture_options()),
            "definition parameter should not leak after substitution"
        );
    }

    #[test]
    fn loop_recursive_datatype_unfolding_includes_positive_predicate_body() {
        let mut get_def = LogicFnDef::new(
            "get".to_string(),
            "test::get".to_string(),
            vec!["self".to_string(), "key".to_string()],
            PureExpr::LogicFnCall {
                name: "get".to_string(),
                args: vec![var("tail"), var("key")],
            },
        );
        get_def.set_is_recursive(true);

        let good_bucket_body = PureExpr::Forall {
            var: "k".to_string(),
            var_sort: None,
            body: Arc::new(PureExpr::BinOp(
                Arc::new(method(var("l"), "get", vec![var("k")])),
                BinOp::Eq,
                Arc::new(method(var("self"), "bucket_ix", vec![var("k")])),
            )),
            triggers: Vec::new(),
        };
        let good_bucket_def = LogicFnDef::new(
            "good_bucket".to_string(),
            "test::good_bucket".to_string(),
            vec!["self".to_string(), "l".to_string(), "h".to_string()],
            good_bucket_body,
        );
        let invariant = method(var("old_self"), "good_bucket", vec![var("l"), var("i")]);

        let mut out = Vec::new();
        collect_recursive_datatype_unfoldings(
            &[invariant],
            &[],
            &["l"],
            &[get_def, good_bucket_def],
            &mut out,
        );

        assert!(
            out.iter().any(|fact| matches!(fact, PureExpr::Forall { .. })
                && expr_has_free_occurrence(fact, "old_self", &capture_options())
                && expr_has_free_occurrence(fact, "l", &capture_options())),
            "loop preservation local unfoldings should include the direct quantified predicate body"
        );
    }

    #[test]
    fn local_recursive_datatype_unfolding_treats_method_calls_as_logic_calls() {
        let mut get_def = LogicFnDef::new(
            "get".to_string(),
            "test::get".to_string(),
            vec!["self".to_string(), "key".to_string()],
            PureExpr::Match {
                scrutinee: Arc::new(var("self")),
                arms: vec![
                    MatchArm {
                        pattern: Pattern::Constructor {
                            name: "List::Nil".to_string(),
                            inner: None,
                        },
                        body: var("None"),
                    },
                    MatchArm {
                        pattern: Pattern::Constructor {
                            name: "List::Cons".to_string(),
                            inner: Some(Box::new(Pattern::Tuple(vec![
                                Pattern::Binding("head".to_string()),
                                Pattern::Binding("tail".to_string()),
                            ]))),
                        },
                        body: method(var("tail"), "get", vec![var("key")]),
                    },
                ],
            },
        )
        .with_param_sorts(vec![
            Some(ExprSort::Datatype(
                trust_wp_core::formula::intern_sort_name("List"),
            )),
            Some(ExprSort::Int),
        ]);
        get_def.set_is_recursive(true);
        let logic_fns_by_name: HashMap<&str, &LogicFnDef> =
            HashMap::from([(get_def.name(), &get_def)]);
        let fact = PureExpr::Forall {
            var: "k".to_string(),
            var_sort: Some(ExprSort::Int),
            body: Arc::new(PureExpr::BinOp(
                Arc::new(method(var("l"), "get", vec![var("k")])),
                BinOp::Eq,
                Arc::new(var("None")),
            )),
            triggers: Vec::new(),
        };

        let mut out = Vec::new();
        collect_recursive_datatype_unfoldings_inner(
            &fact,
            None,
            None,
            &logic_fns_by_name,
            &mut Vec::new(),
            &mut out,
            0,
        );

        assert!(
            out.iter()
                .any(|fact| matches!(fact, PureExpr::Forall { .. })
                    && expr_has_free_occurrence(fact, "l", &capture_options())),
            "method-syntax l.get(k) should emit a local recursive get unfolding"
        );
    }

    #[test]
    fn datatype_unfolding_guard_accepts_matching_receiver_sort_hint() {
        let list_id = trust_wp_core::formula::intern_sort_name("List");
        let def = LogicFnDef::new(
            "get".to_string(),
            "test::get".to_string(),
            vec!["self".to_string(), "key".to_string()],
            var("body"),
        )
        .with_param_sorts(vec![Some(ExprSort::Datatype(list_id)), Some(ExprSort::Int)]);
        let mut var_sorts = HashMap::new();
        var_sorts.insert(
            "l".to_string(),
            Sort::Datatype(ay_dpll::api::DatatypeSort::new("List", vec![])),
        );

        assert!(is_datatype_argument(&def, 0, &var("l"), Some(&var_sorts)));
    }

    #[test]
    fn datatype_unfolding_guard_rejects_mismatched_receiver_sort_hint() {
        let list_id = trust_wp_core::formula::intern_sort_name("List");
        let def = LogicFnDef::new(
            "get".to_string(),
            "test::get".to_string(),
            vec!["self".to_string(), "key".to_string()],
            var("body"),
        )
        .with_param_sorts(vec![Some(ExprSort::Datatype(list_id)), Some(ExprSort::Int)]);
        let mut var_sorts = HashMap::new();
        var_sorts.insert(
            "old_self_view".to_string(),
            Sort::Datatype(ay_dpll::api::DatatypeSort::new("MyHashMap", vec![])),
        );

        assert!(!is_datatype_argument(
            &def,
            0,
            &var("old_self_view"),
            Some(&var_sorts)
        ));
    }
}
