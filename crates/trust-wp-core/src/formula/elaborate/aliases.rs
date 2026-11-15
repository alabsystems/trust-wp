// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A name bound to another name is that name; a projection of a branch is a
//! branch of projections.
//!
//! A pass that reads a name as a program variable (a `&mut` parameter's
//! state, a parameter's sort, a summary fact's endpoint) cannot see through a
//! binder: in `match p { q => *q == old(*p) }` the `*q` reads `p`'s referent,
//! and in `*(if c { p } else { q })` the `*` reads `p`'s or `q`'s. Each such
//! pass once decided by the spelling, so the same value read through an alias
//! or a branch was read at another state (the entry value where the text
//! means the final one). This rewrite removes the difference before any pass
//! runs: every binder whose value is a name (through the branches of an `if`
//! whose condition is bound first) is substituted away, a `match` or `if let`
//! whose first arm cannot fail is that arm, a field of a tuple literal is
//! that component, and `*`, `^` and `@` of an `if`, a `match` or a `let` are
//! pushed into its branches. Each step is an
//! identity of the pure logic, so every reading of the result is a reading
//! of the text.
//!
//! A logic function's body is elaborated keeping every call it evaluates
//! ([`resolve_aliases_keeping_calls`]): there each call owes its callee's
//! precondition (Creusot's logic vcgen), so a component of a tuple literal a
//! projection drops, or a closed scrutinee a wildcard drops, is dropped only
//! when it calls nothing (logic_fn_callee_precondition_dropped_tuple_component.rs).
//!
//! A name is read in a state: `let t = x; old(t)` is the `x` the clause is
//! evaluated at, and `old(x)` another value. An alias is therefore
//! substituted into an `old(..)` its binder is outside of only where that is
//! the same value: as the operand of `*` or `^` (only a reference has one,
//! and a reference is one value in every state), or when every name its value
//! reads is one value in every state (a binder of the clause, or a name the
//! caller vouches for, [`resolve_aliases_with`]). Otherwise the binder stays.

use std::{collections::HashSet, ops::Not, sync::Arc};

use crate::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_index, tuple_logic_fn_arity},
    ExprSort, MatchArm, Pattern, PureExpr,
};

/// `expr` with every alias substituted away and every projection of a branch
/// pushed into the branches, reading no free name as one value in every
/// state. See the module documentation.
#[must_use]
pub(crate) fn resolve_aliases(expr: &PureExpr) -> PureExpr {
    resolve_aliases_with(expr, &|_| false)
}

/// [`resolve_aliases`] for a logic function's body: a subterm that evaluates
/// a call is never dropped, so the call's precondition stays owed.
#[must_use]
pub(crate) fn resolve_aliases_keeping_calls(expr: &PureExpr) -> PureExpr {
    resolve(expr, &|_| false, true)
}

/// [`resolve_aliases`], reading each free name `state_free` accepts as one
/// value in every state (a parameter the caller knows is a reference, or
/// cannot change), so an alias of it is substituted under `old` too.
#[must_use]
pub fn resolve_aliases_with(expr: &PureExpr, state_free: &dyn Fn(&str) -> bool) -> PureExpr {
    resolve(expr, state_free, false)
}

fn resolve(expr: &PureExpr, state_free: &dyn Fn(&str) -> bool, keep_calls: bool) -> PureExpr {
    if !expr.any_recursive(|node| {
        matches!(
            node,
            PureExpr::Let { .. }
                | PureExpr::Match { .. }
                | PureExpr::Deref(_)
                | PureExpr::Final(_)
                | PureExpr::View(_)
        ) || matches!(node, PureExpr::LogicFnCall { name, .. }
            if tuple_field_logic_fn_index(name).is_some())
    }) {
        return expr.clone();
    }
    let mut used = HashSet::new();
    expr.for_each_recursive(|node| match node {
        PureExpr::Var(name, _) => {
            used.insert(name.clone());
        }
        PureExpr::Let { var, .. } | PureExpr::Forall { var, .. } | PureExpr::Exists { var, .. } => {
            used.insert(var.clone());
        }
        PureExpr::Closure { params, .. } => {
            used.extend(params.iter().map(|(name, _)| name.clone()));
        }
        PureExpr::Match { arms, .. } => {
            for arm in arms {
                used.extend(arm.pattern.bound_names().into_iter().map(str::to_string));
            }
        }
        _ => {}
    });
    let mut resolver = Resolver {
        scope: Vec::new(),
        used,
        counter: 0,
        in_old: false,
        state_free,
        keep_calls,
    };
    resolver.resolve(expr)
}

/// Whether evaluating `expr` calls a function: a method call, or a logic call
/// other than a tuple literal or a field of one. A constructor is counted:
/// the spelling alone cannot tell it from a function.
pub(crate) fn evaluates_a_call(expr: &PureExpr) -> bool {
    expr.any_recursive(|node| match node {
        PureExpr::MethodCall { .. } => true,
        PureExpr::LogicFnCall { name, .. } => {
            tuple_logic_fn_arity(name).is_none() && tuple_field_logic_fn_index(name).is_none()
        }
        _ => false,
    })
}

/// Whether a component of `fields` other than `index` evaluates a call.
fn drops_a_call(fields: &[PureExpr], index: usize) -> bool {
    fields
        .iter()
        .enumerate()
        .any(|(at, field)| at != index && evaluates_a_call(field))
}

/// Which projection a node applies to its operand.
#[derive(Debug, Clone, Copy)]
enum Projection {
    Deref,
    Final,
    View,
}

impl Projection {
    fn apply(self, operand: PureExpr) -> PureExpr {
        let operand = Arc::new(operand);
        match self {
            Self::Deref => PureExpr::Deref(operand),
            Self::Final => PureExpr::Final(operand),
            Self::View => PureExpr::View(operand),
        }
    }
}

/// `projection` of `operand`, pushed into every branch of an `if` and a
/// `match` and into the body of a `let`: `*(if c { a } else { b })` is
/// `if c { *a } else { *b }`.
fn project(projection: Projection, operand: PureExpr) -> PureExpr {
    match operand {
        PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
            cond,
            Arc::new(project(projection, then_expr.as_ref().clone())),
            Arc::new(project(projection, else_expr.as_ref().clone())),
        ),
        PureExpr::Let { var, value, body } => PureExpr::Let {
            var,
            value,
            body: Arc::new(project(projection, body.as_ref().clone())),
        },
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    body: project(projection, arm.body),
                })
                .collect(),
        },
        operand => projection.apply(operand),
    }
}

/// What a name in scope stands for.
#[derive(Debug, Clone)]
enum Binding {
    /// A binder the output keeps, under this (possibly fresh) name.
    Kept(String),
    /// A name the output substitutes: its value, already resolved.
    Alias(PureExpr),
}

struct Resolver<'a> {
    /// Innermost last.
    scope: Vec<(String, Binding)>,
    /// Every name the input spells, so a fresh one is none of them.
    used: HashSet<String>,
    counter: usize,
    /// Whether the node being resolved is under an `old(..)`.
    in_old: bool,
    state_free: &'a dyn Fn(&str) -> bool,
    /// Whether a subterm that evaluates a call must survive
    /// ([`resolve_aliases_keeping_calls`]).
    keep_calls: bool,
}

impl Resolver<'_> {
    fn fresh(&mut self, base: &str) -> String {
        loop {
            let candidate = format!("{base}$a{}", self.counter);
            self.counter += 1;
            if !self.used.contains(&candidate) {
                self.used.insert(candidate.clone());
                return candidate;
            }
        }
    }

    fn lookup(&self, name: &str) -> Option<&Binding> {
        self.scope
            .iter()
            .rev()
            .find(|(bound, _)| bound == name)
            .map(|(_, binding)| binding)
    }

    /// Whether every name `value` reads is one value in every state: a
    /// binder of the clause, or a free name the caller vouches for.
    fn is_state_free(&self, value: &PureExpr) -> bool {
        !value.any_free_var(|name, _| {
            !(self
                .scope
                .iter()
                .any(|(_, binding)| matches!(binding, Binding::Kept(kept) if kept == name))
                || (self.state_free)(name))
        })
    }

    fn aliases_read(&self, name: &str) -> bool {
        self.scope.iter().any(|(_, binding)| {
            matches!(binding, Binding::Alias(value) if value.any_free_var(|free, _| free == name))
        })
    }

    /// Enter a binder the output keeps: its name, or a fresh one when a
    /// value substituted in its scope reads the name.
    fn bind_kept(&mut self, name: &str) -> String {
        let kept = if self.aliases_read(name) {
            self.fresh(name)
        } else {
            name.to_string()
        };
        self.scope
            .push((name.to_string(), Binding::Kept(kept.clone())));
        kept
    }

    fn resolve(&mut self, expr: &PureExpr) -> PureExpr {
        match expr {
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => expr.clone(),
            PureExpr::Var(name, sort) => match self.lookup(name) {
                Some(Binding::Alias(value)) => value.clone(),
                Some(Binding::Kept(kept)) if kept != name => {
                    PureExpr::Var(kept.clone(), sort.clone())
                }
                _ => expr.clone(),
            },
            PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
                Arc::new(self.resolve(left)),
                *op,
                Arc::new(self.resolve(right)),
            ),
            PureExpr::UnOp(op, inner) => PureExpr::UnOp(*op, Arc::new(self.resolve(inner))),
            PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
                Arc::new(self.resolve(cond)),
                Arc::new(self.resolve(then_expr)),
                Arc::new(self.resolve(else_expr)),
            ),
            PureExpr::Old(inner) => {
                let outer = std::mem::replace(&mut self.in_old, true);
                let inner = self.resolve(inner);
                self.in_old = outer;
                PureExpr::Old(Arc::new(inner))
            }
            PureExpr::Deref(inner) => project(Projection::Deref, self.resolve(inner)),
            PureExpr::Final(inner) => project(Projection::Final, self.resolve(inner)),
            PureExpr::View(inner) => project(Projection::View, self.resolve(inner)),
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => PureExpr::MethodCall {
                receiver: Arc::new(self.resolve(receiver)),
                method: method.clone(),
                args: args.iter().map(|arg| self.resolve(arg)).collect(),
            },
            PureExpr::LogicFnCall { name, args } => self.resolve_logic_call(name, args),
            PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
                assumption: Arc::new(self.resolve(assumption)),
                body: Arc::new(self.resolve(body)),
            },
            PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
                obligation: Arc::new(self.resolve(obligation)),
                body: Arc::new(self.resolve(body)),
            },
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let (var, body, triggers) = self.resolve_quantifier(var, body, triggers);
                PureExpr::Forall {
                    var,
                    var_sort: var_sort.clone(),
                    body,
                    triggers,
                }
            }
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } => {
                let (var, body, triggers) = self.resolve_quantifier(var, body, triggers);
                PureExpr::Exists {
                    var,
                    var_sort: var_sort.clone(),
                    body,
                    triggers,
                }
            }
            PureExpr::Closure { params, body } => {
                let depth = self.scope.len();
                let params = params
                    .iter()
                    .map(|(name, sort)| (self.bind_kept(name), sort.clone()))
                    .collect();
                let body = Arc::new(self.resolve(body));
                self.scope.truncate(depth);
                PureExpr::Closure { params, body }
            }
            PureExpr::Let { var, value, body } => {
                let value = self.resolve(value);
                self.resolve_bindings(vec![(var.clone(), value)], body)
            }
            PureExpr::Match { scrutinee, arms } => self.resolve_match(scrutinee, arms),
        }
    }

    fn resolve_logic_call(&mut self, name: &str, args: &[PureExpr]) -> PureExpr {
        let args: Vec<PureExpr> = args.iter().map(|arg| self.resolve(arg)).collect();
        // A field of a tuple literal is that component: `(p, 0).0`
        // is `p`, which a pass reading names can place.
        if let (
            Some(index),
            [PureExpr::LogicFnCall {
                name: tuple,
                args: fields,
            }],
        ) = (tuple_field_logic_fn_index(name), args.as_slice())
        {
            if tuple_logic_fn_arity(tuple) == Some(fields.len())
                && index < fields.len()
                && !(self.keep_calls && drops_a_call(fields, index))
            {
                return fields[index].clone();
            }
        }
        PureExpr::LogicFnCall {
            name: name.to_string(),
            args,
        }
    }

    fn resolve_match(&mut self, scrutinee: &PureExpr, arms: &[MatchArm]) -> PureExpr {
        let scrutinee = self.resolve(scrutinee);
        if let Some(first) = arms.first() {
            if let Some(bindings) =
                irrefutable_bindings(&first.pattern, &scrutinee, self.keep_calls)
            {
                return self.resolve_bindings(bindings, &first.body);
            }
        }
        let arms = arms
            .iter()
            .map(|arm| {
                let depth = self.scope.len();
                let mut pattern = arm.pattern.clone();
                for name in arm.pattern.bound_names() {
                    let kept = self.bind_kept(name);
                    if kept != name {
                        pattern = pattern.rename_binding(name, &kept);
                    }
                }
                let body = self.resolve(&arm.body);
                self.scope.truncate(depth);
                MatchArm { pattern, body }
            })
            .collect();
        PureExpr::Match {
            scrutinee: Arc::new(scrutinee),
            arms,
        }
    }

    fn resolve_quantifier(
        &mut self,
        var: &str,
        body: &PureExpr,
        triggers: &[Vec<PureExpr>],
    ) -> (String, Arc<PureExpr>, Vec<Vec<PureExpr>>) {
        let depth = self.scope.len();
        let kept = self.bind_kept(var);
        let body = Arc::new(self.resolve(body));
        let triggers = triggers
            .iter()
            .map(|group| group.iter().map(|expr| self.resolve(expr)).collect())
            .collect();
        self.scope.truncate(depth);
        (kept, body, triggers)
    }

    /// `body` under `bindings`, each a name and its resolved value, bound at
    /// once (no value reads another binding's name). An alias value is
    /// substituted; every other value is a `let` of the name, renamed apart
    /// when a substituted value reads it. The alias of a name some use
    /// annotates is kept a `let`: the annotation belongs to the name, and the
    /// substituted value would not carry it.
    fn resolve_bindings(&mut self, bindings: Vec<(String, PureExpr)>, body: &PureExpr) -> PureExpr {
        let depth = self.scope.len();
        let mut hoisted = Vec::new();
        let mut aliases = Vec::new();
        let mut kept = Vec::new();
        for (name, value) in bindings {
            // An alias no use reads is kept: substituted into no use, its
            // value's names would leave the clause, and a consumer binding
            // them (a bundle clause binding) would find them unread.
            let read = body.any_free_var(|free, _| free == name);
            let same_value_everywhere =
                self.in_old || !reads_as_value_under_old(body, &name) || self.is_state_free(&value);
            if read && same_value_everywhere && !has_annotated_use(body, &name) {
                if let Some(alias) = alias_value(&value) {
                    let (alias, conditions) = self.hoist(alias);
                    hoisted.extend(conditions);
                    aliases.push((name, alias));
                    continue;
                }
            }
            kept.push((name, value));
        }
        for (name, alias) in aliases {
            self.scope.push((name, Binding::Alias(alias)));
        }
        let mut lets = Vec::new();
        for (name, value) in kept {
            let binder = if self.aliases_read(&name) {
                self.fresh(&name)
            } else {
                name.clone()
            };
            self.scope.push((name, Binding::Kept(binder.clone())));
            lets.push((binder, value));
        }
        let mut result = self.resolve(body);
        self.scope.truncate(depth);
        for (name, value) in lets.into_iter().rev().chain(hoisted.into_iter().rev()) {
            result = PureExpr::Let {
                var: name,
                value: Arc::new(value),
                body: Arc::new(result),
            };
        }
        result
    }

    /// Bind each condition of an alias value where it is written (`$ifN`):
    /// moved to a use, a condition would be evaluated there, under another
    /// `old`, and read another state.
    fn hoist(&mut self, alias: PureExpr) -> (PureExpr, Vec<(String, PureExpr)>) {
        let mut hoisted = Vec::new();
        let value = self.hoist_conditions(alias, &mut hoisted);
        (value, hoisted)
    }

    fn hoist_conditions(
        &mut self,
        value: PureExpr,
        hoisted: &mut Vec<(String, PureExpr)>,
    ) -> PureExpr {
        match value {
            PureExpr::Ite(cond, then_expr, else_expr) => {
                let cond = if let PureExpr::Bool(_) = cond.as_ref() {
                    cond
                } else {
                    let name = self.fresh("$if");
                    hoisted.push((name.clone(), cond.as_ref().clone()));
                    Arc::new(PureExpr::Var(name, Some(ExprSort::Bool)))
                };
                let then_expr = self.hoist_conditions(then_expr.as_ref().clone(), hoisted);
                let else_expr = self.hoist_conditions(else_expr.as_ref().clone(), hoisted);
                PureExpr::Ite(cond, Arc::new(then_expr), Arc::new(else_expr))
            }
            value => value,
        }
    }
}

/// A value a binder can be substituted by: a name, or an `if` whose branches
/// are such values.
fn alias_value(value: &PureExpr) -> Option<PureExpr> {
    match value {
        PureExpr::Var(..) => Some(value.clone()),
        PureExpr::Ite(_, then_expr, else_expr) => (alias_value(then_expr).is_some()
            && alias_value(else_expr).is_some())
        .then(|| value.clone()),
        _ => None,
    }
}

/// Whether `body` reads the `name` it is the scope of under an `old(..)`
/// other than as the operand of `*` or `^`: there the name would be read in
/// the entry state, where the binder read it in the state the clause is
/// evaluated at.
fn reads_as_value_under_old(body: &PureExpr, name: &str) -> bool {
    fn walk(expr: &PureExpr, name: &str, in_old: bool, operand_of_deref: bool) -> bool {
        match expr {
            PureExpr::Var(var, _) => in_old && var == name && !operand_of_deref,
            PureExpr::Old(inner) => walk(inner, name, true, false),
            PureExpr::Deref(inner) | PureExpr::Final(inner) => walk(inner, name, in_old, true),
            PureExpr::Forall { var, .. }
            | PureExpr::Exists { var, .. }
            | PureExpr::Let { var, .. }
                if var == name =>
            {
                // A `let` value is read in the enclosing scope.
                matches!(expr, PureExpr::Let { value, .. } if walk(value, name, in_old, false))
            }
            PureExpr::Closure { params, .. } if params.iter().any(|(param, _)| param == name) => {
                false
            }
            PureExpr::Match { scrutinee, arms } => {
                walk(scrutinee, name, in_old, false)
                    || arms.iter().any(|arm| {
                        !arm.pattern.binds_name(name) && walk(&arm.body, name, in_old, false)
                    })
            }
            _ => super::children(expr)
                .into_iter()
                .any(|child| walk(child, name, in_old, false)),
        }
    }
    walk(body, name, false, false)
}

/// Whether a use of `name` free in `body` carries an annotation.
fn has_annotated_use(body: &PureExpr, name: &str) -> bool {
    body.any_free_var(|free, sort| free == name && sort.is_some())
}

/// The bindings of `pattern` matched against `scrutinee` when the match
/// cannot fail, each a name and the value it binds: a name, `_`, `x @ p` of
/// such a pattern, or a tuple of such patterns against a tuple literal of its
/// arity. `None` when the pattern can fail or the value it binds is a part
/// of the scrutinee no expression here names.
fn irrefutable_bindings(
    pattern: &Pattern,
    scrutinee: &PureExpr,
    keep_calls: bool,
) -> Option<Vec<(String, PureExpr)>> {
    let mut bindings = Vec::new();
    collect_irrefutable(pattern, scrutinee, keep_calls, &mut bindings)?;
    Some(bindings)
}

fn collect_irrefutable(
    pattern: &Pattern,
    value: &PureExpr,
    keep_calls: bool,
    out: &mut Vec<(String, PureExpr)>,
) -> Option<()> {
    match pattern {
        // A value `_` drops is kept by keeping the `match`, when it reads a
        // name (the clause still reads it) or, where calls are kept, when it
        // evaluates one.
        Pattern::Wildcard => (value.any_free_var(|_, _| true)
            || (keep_calls && evaluates_a_call(value)))
        .not()
        .then_some(()),
        Pattern::Binding(name) => {
            out.push((name.clone(), value.clone()));
            Some(())
        }
        // The alias names the value, and the subpattern matches the value
        // itself: only when the value is a name or the subpattern binds by
        // name alone is it read once.
        Pattern::Alias { alias, pattern } => {
            if alias_value(value).is_none()
                && !matches!(pattern.as_ref(), Pattern::Wildcard | Pattern::Binding(_))
            {
                return None;
            }
            out.push((alias.clone(), value.clone()));
            collect_irrefutable(pattern, value, keep_calls, out)
        }
        Pattern::Tuple(elements) => match value {
            PureExpr::LogicFnCall { name, args }
                if tuple_logic_fn_arity(name) == Some(elements.len())
                    && args.len() == elements.len() =>
            {
                for (element, component) in elements.iter().zip(args) {
                    collect_irrefutable(element, component, keep_calls, out)?;
                }
                Some(())
            }
            _ => None,
        },
        Pattern::Literal(_) | Pattern::Constructor { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use super::resolve_aliases;
    use crate::contract_parser::parse_contract;

    fn resolved(text: &str) -> String {
        resolve_aliases(&parse_contract(text).expect("parses")).to_string()
    }

    #[test]
    fn a_name_bound_to_a_name_is_that_name() {
        for (text, expected) in [
            ("match p { q => *q == old(*p) }", "(*p == old(*p))"),
            ("match p { p => *p == old(*p) }", "(*p == old(*p))"),
            ("{ let q = p; *q == old(*p) }", "(*p == old(*p))"),
            (
                "if let q = p { *q == old(*p) } else { true }",
                "(*p == old(*p))",
            ),
            (
                "match (p, 0) { (q, _) => *q == old(*p) }",
                "(*p == old(*p))",
            ),
            ("match p { q @ r => *q == *r }", "(*p == *p)"),
        ] {
            let parsed = parse_contract(text).expect("parses");
            assert_eq!(parsed.to_string(), expected, "{text}");
        }
    }

    #[test]
    fn a_projection_of_a_branch_is_a_branch_of_projections() {
        let text = resolved("*(if c { p } else { q }) == 0");
        assert!(!text.contains("*(if"), "{text}");
        assert!(text.contains("*p") && text.contains("*q"), "{text}");
    }

    #[test]
    fn a_substituted_name_is_not_captured() {
        // `q` is `p`; the inner binder of `p` is another value.
        let parsed = parse_contract("{ let q = p; forall<p: Int> *q == p }").expect("parses");
        let text = parsed.to_string();
        assert!(text.contains("*p =="), "{text}");
        assert!(!text.contains("*p == p)"), "{text}");
    }

    /// The component a projection drops, and a closed scrutinee a wildcard
    /// drops, survive in a logic body when they call something, and only
    /// then (logic_fn_callee_precondition_dropped_tuple_component.rs).
    #[test]
    fn a_logic_body_drops_no_evaluated_call() {
        use crate::contract_parser::{
            parse_contract_body_with_leading_exprs, parse_logic_body_expr_with_elisions,
        };
        let body = |text: &str| {
            parse_contract_body_with_leading_exprs(text)
                .expect("parses")
                .1
        };
        let expr = |text: &str| parse_logic_body_expr_with_elisions(text).expect("parses").0;
        for text in [
            "(needs_pos(y), 1).1",
            "match needs_pos(0) { _ => 1 }",
            "match (needs_pos(0), 1) { (_, b) => b }",
            "(s.len(), 1).1",
        ] {
            for parsed in [body(text), expr(text)] {
                assert!(
                    super::evaluates_a_call(&parsed),
                    "{text} lost its call: {parsed}"
                );
            }
            assert!(
                !super::evaluates_a_call(&parse_contract(text).expect("parses")),
                "a contract clause still reads {text} as its value"
            );
        }
        for (text, expected) in [("(needs_pos(y), 1).0", "needs_pos(y)"), ("(y, 1).1", "1")] {
            assert_eq!(body(text).to_string(), expected, "{text}");
        }
    }

    #[test]
    fn a_condition_is_bound_where_it_is_written() {
        let parsed =
            parse_contract("{ let r = if *p > 0 { p } else { q }; old(*r) == 0 }").expect("parses");
        let text = parsed.to_string();
        assert!(text.contains("$if"), "{text}");
        assert!(!text.contains("old(if (*p > 0)"), "{text}");
    }
}
