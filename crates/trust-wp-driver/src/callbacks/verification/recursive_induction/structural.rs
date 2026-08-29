// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! STRUCTURAL (subterm-descent) induction hypotheses for recursive `#[logic]`
//! functions declared WITHOUT a `#[variant]`.
//!
//! # The scheme
//!
//! For a recursive logic function `f(p_0, .., p_n)` whose body destructures an
//! ADT parameter with `match` and recurses on a constructor-field binder:
//!
//! ```text
//! #[ensures(E)]
//! fn len_logic(self: List) -> Int {
//!     match self { Cons(_, ls) => 1 + len_logic(ls), Nil => 0 }
//! }
//! ```
//!
//! inject, for each such self-call, the TESTER-GUARDED ground hypothesis
//!
//! ```text
//! match self { Cons(_, ls) => requires[A] => E[A, result -> f(A)],  _ => true }
//! ```
//!
//! where `A` is the simultaneous substitution `params -> call args`. The
//! wrapper re-uses the body arm's own pattern, so the encoder's match machinery
//! binds `ls` to the SAME selector term (`sel_tail(self)`) in the hypothesis as
//! in the body — the IH is ground (no quantifier is introduced) and closes by
//! plain DT+LIA reasoning.
//!
//! # Soundness
//!
//! SMT datatypes denote initial algebras: every element of a declared datatype
//! sort is a FINITE constructor tree, so the strict-subterm relation
//! `y ⊏ x := y is a proper constructor-argument descendant of x` is
//! well-founded. Well-founded induction over `⊏` states
//!
//! ```text
//!   ( ∀x. (∀y. y ⊏ x ⇒ P(y)) ⇒ P(x) )  ⊢  ∀x. P(x)
//! ```
//!
//! with `P(x) := ∀ other params. requires ⇒ ensures` (the other parameter
//! positions are universally quantified inside `P`, so instantiating them with
//! arbitrary in-scope expressions is licensed). Each emitted hypothesis is the
//! antecedent's inner universal instantiated at the single witness
//! `y := <constructor-field projection of x>`, guarded by the very tester
//! (`is_Cons(x)`, via the match wrapper) that proves the projection IS a proper
//! subterm. Hence the assumption set is a logical consequence of the
//! well-founded-induction antecedent: discharging the VC discharges the
//! inductive step, and `∀x. P(x)` genuinely holds. A wrong pattern or a
//! non-matching constructor only yields a false guard (the arm does not fire —
//! incompleteness), never an unsound instance.
//!
//! # When the IH must NOT fire (all enforced, fail-closed)
//!
//!  * **Non-subterm recursion** — the induction-position argument must be a
//!    bare match binder bound at a DIRECT constructor-field position (>= 1
//!    constructor layer peeled) of a match on the SAME parameter position.
//!    `f(l)` (identity), `f(Cons(h, ls))` (rebuilt term), `f(g(l))`
//!    (arbitrary expression) all emit nothing.
//!  * **Cross-parameter descent** — a binder descending from parameter `j`
//!    justifies nothing at induction position `i != j`.
//!  * **Alias / top-level bindings** — `l2 @ Cons(..)` and bare `x` patterns
//!    bind the WHOLE scrutinee (depth 0), never a subterm: no descent fact.
//!  * **Different-sort fields** — the binder's declared field sort must be the
//!    SAME datatype as the induction parameter (single-ADT scheme; nested-sort
//!    descent through other type constructors is out of scope).
//!  * **Mutual recursion** — only DIRECT self-calls are considered. A joint
//!    scheme for `f`/`g` cycles would need a simultaneous induction measure;
//!    without one, granting either function's contract while proving the
//!    other's is circular. No IH is emitted for non-self calls, ever.
//!  * **Shadowing** — `let` rebindings and inner binders shadow descent facts
//!    name-wise during collection, so a name that no longer denotes the
//!    projection grants nothing.
//!  * **Capture** — if any binder bound INSIDE the contract clauses (or the
//!    ensures' own binders) collides with the wrapper arm's binder names or a
//!    parameter name, the call site is skipped: substitution could otherwise
//!    place a term under a same-named binder and change its meaning.
//!  * **Prophecy-carrying parameters** — `&mut` induction parameters are
//!    rejected (`MutRef` carries a prophecy slot; the subterm argument does
//!    not transfer). Shared references are transparent value views and are
//!    accepted.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use trust_wp_core::{
    formula::{
        resolve_sort_name, BinOp, CaptureAvoidingSubstOptions, ExprSort, MatchArm, Pattern,
        PureExpr,
    },
    logic::{AdtDecl, AdtDecls, AdtKind, LogicFnDef},
};

use super::{and_all, binop, env_without, is_int_model_bare_name, is_self_call_name};

/// A descent fact: `binder` denotes a direct constructor-field projection of
/// the induction parameter at `param_idx`, bound by `arm_pattern` in a match
/// whose scrutinee expression was `scrutinee` (the parameter, possibly behind
/// transparent `Deref` layers — reused verbatim so the wrapper encodes the
/// SAME scrutinee term as the body).
#[derive(Clone)]
struct DescentFact {
    param_idx: usize,
    scrutinee: PureExpr,
    arm_pattern: Pattern,
    arm_binders: Vec<String>,
}

/// Entry point: build the structural induction hypotheses for `logic_fn`
/// (recursive, has `ensures`, declared WITHOUT any `#[variant]`).
/// Returns an empty vec whenever any sound precondition is not met.
pub(super) fn build_structural_induction_hypotheses(
    logic_fn: &LogicFnDef,
    adt_decls: Option<&AdtDecls>,
) -> Vec<PureExpr> {
    let Some(adt_decls) = adt_decls else {
        return Vec::new();
    };
    let params = logic_fn.params();
    if params.is_empty() {
        return Vec::new();
    }

    // Capture guard (module docs): names bound anywhere inside the contract
    // clauses must not collide with parameter names — otherwise substituting a
    // parameter occurrence under such a binder would be captured.
    let mut contract_bound = HashSet::new();
    for clause in logic_fn.requires().iter().chain(logic_fn.ensures()) {
        collect_bound_names(clause, &mut contract_bound);
    }
    if params.iter().any(|p| contract_bound.contains(p.as_str())) {
        return Vec::new();
    }
    // The conclusion substitutes `result` with the recursive-call term; a
    // contract clause that internally BINDS `result` could capture it.
    if contract_bound.contains("result") {
        return Vec::new();
    }

    let mut sites = Vec::new();
    collect_descent_call_sites(
        logic_fn.body(),
        logic_fn,
        adt_decls,
        &HashMap::new(),
        &HashMap::new(),
        &HashSet::new(),
        &mut sites,
    );

    let param_set: HashSet<&str> = params.iter().map(String::as_str).collect();
    let mut hypotheses: Vec<PureExpr> = Vec::new();
    for site in sites {
        let PureExpr::LogicFnCall { args, .. } = &site.call else {
            continue;
        };
        if args.len() != params.len() {
            continue;
        }
        // Every argument must be expressible inside the wrapper arm's scope:
        // free vars ⊆ params ∪ this arm's binders.
        let scope_ok = args.iter().all(|a| {
            a.free_vars().iter().all(|v| {
                param_set.contains(v.as_str()) || site.fact.arm_binders.iter().any(|b| b == v)
            })
        });
        if !scope_ok {
            continue;
        }
        // Capture guard: contract-internal binders must not collide with the
        // arm binders being substituted in.
        if site
            .fact
            .arm_binders
            .iter()
            .any(|b| contract_bound.contains(b.as_str()))
        {
            continue;
        }

        let subst: HashMap<String, PureExpr> =
            params.iter().cloned().zip(args.iter().cloned()).collect();

        let guard: Vec<PureExpr> = logic_fn
            .requires()
            .iter()
            .map(|req| req.substitute(&subst))
            .collect();

        let mut concl_subst = subst.clone();
        concl_subst.insert("result".to_string(), site.call.clone());
        let conclusion: Vec<PureExpr> = logic_fn
            .ensures()
            .iter()
            .map(|e| e.substitute(&concl_subst))
            .collect();

        let core = if guard.is_empty() {
            and_all(conclusion)
        } else {
            binop(and_all(guard), BinOp::Implies, and_all(conclusion))
        };

        let wrapper = PureExpr::Match {
            scrutinee: Arc::new(site.fact.scrutinee.clone()),
            arms: vec![
                MatchArm {
                    pattern: site.fact.arm_pattern.clone(),
                    body: core,
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: PureExpr::Bool(true),
                },
            ],
        };
        if !hypotheses.contains(&wrapper) {
            hypotheses.push(wrapper);
        }
    }
    hypotheses
}

/// A self-call together with the descent fact justifying its induction
/// position.
struct DescentCallSite {
    call: PureExpr,
    fact: DescentFact,
}

/// Resolve the induction-parameter datatype for `sort`: the parameter must be
/// an ADT (directly or behind SHARED references — transparent value views).
/// `&mut` (prophecy-carrying) and every other sort yields `None`.
fn induction_param_datatype(sort: Option<&ExprSort>) -> Option<u32> {
    match sort? {
        ExprSort::Datatype(id) => Some(*id),
        ExprSort::Ref(inner) => induction_param_datatype(Some(inner)),
        _ => None,
    }
}

/// The bare (last `::`-segment, generic-args-stripped) name of an interned
/// datatype sort, used to key `AdtDecls` and to compare field sorts.
fn bare_datatype_name(id: u32) -> String {
    let full = resolve_sort_name(id);
    let no_generics = full.split('<').next().unwrap_or(full.as_str());
    no_generics
        .rsplit("::")
        .next()
        .unwrap_or(no_generics)
        .trim()
        .to_string()
}

/// Look up the `AdtDecl` for the induction parameter's datatype. The scheme
/// requires a declared ENUM whose bare name is NOT one the encoder lowers to
/// `Int` (those have no native constructors/testers to guard with).
fn eligible_param_adt<'a>(adt_decls: &'a AdtDecls, param_dt: u32) -> Option<&'a AdtDecl> {
    let bare = bare_datatype_name(param_dt);
    if is_int_model_bare_name(&bare) {
        return None;
    }
    let decl = adt_decls.get(&bare)?;
    if decl.kind != AdtKind::Enum {
        return None;
    }
    Some(decl)
}

/// The constructor decl in `adt` matching a pattern's constructor `name`
/// (compared on the last `::` segment of both sides).
fn constructor_decl<'a>(
    adt: &'a AdtDecl,
    pattern_ctor: &str,
) -> Option<&'a trust_wp_core::logic::AdtConstructorDecl> {
    let short = pattern_ctor.rsplit("::").next().unwrap_or(pattern_ctor);
    adt.constructors.iter().find(|c| {
        c.rust_name.rsplit("::").next().unwrap_or(&c.rust_name) == short
            || c.smt_name.rsplit("::").next().unwrap_or(&c.smt_name) == short
    })
}

/// Descent binders granted by an arm pattern over the eligible parameter ADT:
/// names bound by `Pattern::Binding` at a DIRECT field position of the arm's
/// top-level constructor whose declared field sort is the SAME datatype as the
/// parameter (module docs: single-ADT scheme). Aliases, nested patterns, and
/// non-matching field sorts grant nothing.
fn descent_binders(pattern: &Pattern, adt: &AdtDecl, param_bare: &str) -> Vec<String> {
    let Pattern::Constructor {
        name,
        inner: Some(inner),
    } = pattern
    else {
        return Vec::new();
    };
    let Some(ctor) = constructor_decl(adt, name) else {
        return Vec::new();
    };
    let field_sort_matches = |idx: usize| -> bool {
        ctor.fields.get(idx).is_some_and(|f| match &f.sort {
            ExprSort::Datatype(fid) => bare_datatype_name(*fid) == param_bare,
            _ => false,
        })
    };
    match inner.as_ref() {
        Pattern::Binding(b) => {
            if ctor.fields.len() == 1 && field_sort_matches(0) {
                vec![b.clone()]
            } else {
                Vec::new()
            }
        }
        Pattern::Tuple(elements) => {
            if elements.len() != ctor.fields.len() {
                return Vec::new();
            }
            elements
                .iter()
                .enumerate()
                .filter_map(|(idx, el)| match el {
                    Pattern::Binding(b) if field_sort_matches(idx) => Some(b.clone()),
                    _ => None,
                })
                .collect()
        }
        _ => Vec::new(),
    }
}

/// Strip transparent `Deref` layers (Box / shared-reference views).
fn strip_deref_layers(mut expr: &PureExpr) -> &PureExpr {
    while let PureExpr::Deref(inner) = expr {
        expr = inner;
    }
    expr
}

/// Walk the body collecting self-calls whose induction-position argument is a
/// descent binder.
///
/// * `let_env` resolves `let`-bound locals exactly like `collect_self_calls`
///   (parent module);
/// * `descent` maps binder names to their facts;
/// * `shadowed` is the set of ALL names bound by any enclosing binder
///   construct (match arms, lets, quantifiers, closures). A scrutinee whose
///   root Var is shadowed is a LOCAL, never the parameter — without this a
///   binder that reuses a parameter's name would be misread as the parameter
///   and grant unsound descent facts.
///
/// All three are scoped name-wise: any construct that binds a name updates
/// them for its subtree only.
#[allow(clippy::too_many_arguments)]
fn collect_descent_call_sites(
    body: &PureExpr,
    logic_fn: &LogicFnDef,
    adt_decls: &AdtDecls,
    let_env: &HashMap<String, PureExpr>,
    descent: &HashMap<String, DescentFact>,
    shadowed: &HashSet<String>,
    out: &mut Vec<DescentCallSite>,
) {
    match body {
        PureExpr::LogicFnCall { name, args } => {
            if is_self_call_name(name, logic_fn) {
                let resolved = if let_env.is_empty() {
                    body.clone()
                } else {
                    body.substitute_capture_avoiding(
                        let_env,
                        &CaptureAvoidingSubstOptions::default(),
                    )
                };
                if let PureExpr::LogicFnCall {
                    args: resolved_args,
                    ..
                } = &resolved
                {
                    // The induction position: an argument that is a bare
                    // descent binder whose fact roots at the SAME parameter
                    // position (module docs: cross-parameter descent proves
                    // nothing).
                    let fact = resolved_args.iter().enumerate().find_map(|(idx, arg)| {
                        match strip_deref_layers(arg) {
                            PureExpr::Var(v, _) => {
                                descent.get(v).filter(|fact| fact.param_idx == idx).cloned()
                            }
                            _ => None,
                        }
                    });
                    if let Some(fact) = fact {
                        out.push(DescentCallSite {
                            call: resolved.clone(),
                            fact,
                        });
                    }
                }
            }
            for a in args {
                collect_descent_call_sites(a, logic_fn, adt_decls, let_env, descent, shadowed, out);
            }
        }
        PureExpr::BinOp(l, _, r) => {
            collect_descent_call_sites(l, logic_fn, adt_decls, let_env, descent, shadowed, out);
            collect_descent_call_sites(r, logic_fn, adt_decls, let_env, descent, shadowed, out);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => {
            collect_descent_call_sites(inner, logic_fn, adt_decls, let_env, descent, shadowed, out);
        }
        PureExpr::Ite(c, t, e) => {
            collect_descent_call_sites(c, logic_fn, adt_decls, let_env, descent, shadowed, out);
            collect_descent_call_sites(t, logic_fn, adt_decls, let_env, descent, shadowed, out);
            collect_descent_call_sites(e, logic_fn, adt_decls, let_env, descent, shadowed, out);
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            collect_descent_call_sites(
                receiver, logic_fn, adt_decls, let_env, descent, shadowed, out,
            );
            for a in args {
                collect_descent_call_sites(a, logic_fn, adt_decls, let_env, descent, shadowed, out);
            }
        }
        PureExpr::Forall {
            var,
            body: inner,
            triggers,
            ..
        }
        | PureExpr::Exists {
            var,
            body: inner,
            triggers,
            ..
        } => {
            let scoped_let = env_without(let_env, std::slice::from_ref(var));
            let scoped_descent = descent_without(descent, std::slice::from_ref(var));
            let let_env = scoped_let.as_ref().unwrap_or(let_env);
            let descent = scoped_descent.as_ref().unwrap_or(descent);
            let shadowed = shadowed_with(shadowed, std::slice::from_ref(var));
            collect_descent_call_sites(
                inner, logic_fn, adt_decls, let_env, descent, &shadowed, out,
            );
            for trig in triggers {
                for t in trig {
                    collect_descent_call_sites(
                        t, logic_fn, adt_decls, let_env, descent, &shadowed, out,
                    );
                }
            }
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_descent_call_sites(
                scrutinee, logic_fn, adt_decls, let_env, descent, shadowed, out,
            );

            // Does this match destructure an induction-eligible parameter?
            // The scrutinee must be the parameter Var itself (behind
            // transparent Deref layers) and NOT shadowed by ANY binder in
            // scope (let, match arm, quantifier, closure).
            let match_param = match strip_deref_layers(scrutinee) {
                PureExpr::Var(name, _) if !shadowed.contains(name) => logic_fn
                    .params()
                    .iter()
                    .position(|p| p == name)
                    .and_then(|idx| {
                        let dt = induction_param_datatype(
                            logic_fn.param_sorts().get(idx).and_then(Option::as_ref),
                        )?;
                        let adt = eligible_param_adt(adt_decls, dt)?;
                        Some((idx, adt, bare_datatype_name(dt)))
                    }),
                _ => None,
            };

            for arm in arms {
                let bound = arm.pattern.bound_names();
                let scoped_let = env_without(let_env, &bound);
                let scoped_descent = descent_without(descent, &bound);
                let arm_let = scoped_let.as_ref().unwrap_or(let_env);
                let arm_descent_base = scoped_descent.as_ref().unwrap_or(descent);
                let arm_shadowed = shadowed_with(shadowed, &bound);

                let granted: Vec<String> = match &match_param {
                    Some((_, adt, param_bare)) => {
                        descent_binders(&arm.pattern, *adt, param_bare.as_str())
                    }
                    None => Vec::new(),
                };
                if granted.is_empty() {
                    collect_descent_call_sites(
                        &arm.body,
                        logic_fn,
                        adt_decls,
                        arm_let,
                        arm_descent_base,
                        &arm_shadowed,
                        out,
                    );
                } else {
                    let (idx, _, _) = match_param.as_ref().expect("granted implies match_param");
                    let arm_binders: Vec<String> = bound.iter().map(|s| (*s).to_string()).collect();
                    let mut arm_descent = arm_descent_base.clone();
                    for b in granted {
                        arm_descent.insert(
                            b,
                            DescentFact {
                                param_idx: *idx,
                                scrutinee: scrutinee.as_ref().clone(),
                                arm_pattern: arm.pattern.clone(),
                                arm_binders: arm_binders.clone(),
                            },
                        );
                    }
                    collect_descent_call_sites(
                        &arm.body,
                        logic_fn,
                        adt_decls,
                        arm_let,
                        &arm_descent,
                        &arm_shadowed,
                        out,
                    );
                }
            }
        }
        PureExpr::Let { var, value, body } => {
            collect_descent_call_sites(value, logic_fn, adt_decls, let_env, descent, shadowed, out);
            let resolved_value = if let_env.is_empty() {
                value.as_ref().clone()
            } else {
                value.substitute_capture_avoiding(let_env, &CaptureAvoidingSubstOptions::default())
            };
            let mut inner_let = let_env.clone();
            inner_let.insert(var.clone(), resolved_value);
            let scoped_descent = descent_without(descent, std::slice::from_ref(var));
            let descent = scoped_descent.as_ref().unwrap_or(descent);
            let shadowed = shadowed_with(shadowed, std::slice::from_ref(var));
            collect_descent_call_sites(
                body, logic_fn, adt_decls, &inner_let, descent, &shadowed, out,
            );
        }
        PureExpr::LetAssume {
            assumption: value,
            body,
        }
        | PureExpr::LetObligation {
            obligation: value,
            body,
        } => {
            collect_descent_call_sites(value, logic_fn, adt_decls, let_env, descent, shadowed, out);
            collect_descent_call_sites(body, logic_fn, adt_decls, let_env, descent, shadowed, out);
        }
        PureExpr::Closure { params, body } => {
            let bound: Vec<String> = params.iter().map(|(name, _)| name.clone()).collect();
            let scoped_let = env_without(let_env, &bound);
            let scoped_descent = descent_without(descent, &bound);
            let shadowed = shadowed_with(shadowed, &bound);
            collect_descent_call_sites(
                body,
                logic_fn,
                adt_decls,
                scoped_let.as_ref().unwrap_or(let_env),
                scoped_descent.as_ref().unwrap_or(descent),
                &shadowed,
                out,
            );
        }
        // Leaves contain no self-call. Missing a future variant only drops an
        // IH (incompleteness), never affects soundness.
        _ => {}
    }
}

/// `shadowed` plus the given bound names (owned clone; bodies are small).
fn shadowed_with<S: AsRef<str>>(shadowed: &HashSet<String>, bound: &[S]) -> HashSet<String> {
    let mut extended = shadowed.clone();
    for name in bound {
        extended.insert(name.as_ref().to_string());
    }
    extended
}

/// `descent` minus the given bound names (shadowing). `None` when unchanged.
fn descent_without<S: AsRef<str>>(
    descent: &HashMap<String, DescentFact>,
    bound: &[S],
) -> Option<HashMap<String, DescentFact>> {
    if bound
        .iter()
        .all(|name| !descent.contains_key(name.as_ref()))
    {
        return None;
    }
    let mut scoped = descent.clone();
    for name in bound {
        scoped.remove(name.as_ref());
    }
    Some(scoped)
}

/// Collect every name bound by ANY binder construct inside `expr`
/// (quantifiers, lets, match patterns, closures) — the capture guard.
fn collect_bound_names(expr: &PureExpr, out: &mut HashSet<String>) {
    match expr {
        PureExpr::Forall { var, body, .. } | PureExpr::Exists { var, body, .. } => {
            out.insert(var.clone());
            collect_bound_names(body, out);
        }
        PureExpr::Let { var, value, body } => {
            out.insert(var.clone());
            collect_bound_names(value, out);
            collect_bound_names(body, out);
        }
        PureExpr::Match { scrutinee, arms } => {
            collect_bound_names(scrutinee, out);
            for arm in arms {
                for b in arm.pattern.bound_names() {
                    out.insert(b.to_string());
                }
                collect_bound_names(&arm.body, out);
            }
        }
        PureExpr::Closure { params, body } => {
            for (name, _) in params {
                out.insert(name.clone());
            }
            collect_bound_names(body, out);
        }
        PureExpr::BinOp(l, _, r) => {
            collect_bound_names(l, out);
            collect_bound_names(r, out);
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => collect_bound_names(inner, out),
        PureExpr::Ite(c, t, e) => {
            collect_bound_names(c, out);
            collect_bound_names(t, out);
            collect_bound_names(e, out);
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            collect_bound_names(receiver, out);
            for a in args {
                collect_bound_names(a, out);
            }
        }
        PureExpr::LogicFnCall { args, .. } => {
            for a in args {
                collect_bound_names(a, out);
            }
        }
        PureExpr::LetAssume {
            assumption: a,
            body,
        }
        | PureExpr::LetObligation {
            obligation: a,
            body,
        } => {
            collect_bound_names(a, out);
            collect_bound_names(body, out);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests;
