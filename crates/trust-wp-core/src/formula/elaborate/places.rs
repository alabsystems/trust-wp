// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Where a `&mut` parameter's referent is read.
//!
//! A clause reads a `&mut` parameter `p`'s referent through `*p`, `p@` and
//! every read of its final value (`^p`, `resolve(p)`, a logic function
//! reading `^q` of its argument: `FinalReaders::final_operands`), and the
//! state each of these reads (entry or final) is decided by the parameter's
//! name. After [`super::resolve_aliases_with`] no binder renames
//! `p` and no projection sits on a branch, so each read the text makes is
//! spelled on `p` itself. What is left is a projection of a value that holds
//! `p` some other way (`*t.0` of a `let t = (p, 0)`, `*id(p)`, `*old(p)`):
//! the name-keyed state rule cannot see `p` there, and read the entry value
//! where the text means the final one. Such a read has no placement, and is
//! refused by name. So is every read of a `&mut` a parameter holds without
//! being it (a binding of a destructuring parameter, a field of a tuple
//! parameter): the state rule names no such value, in either dialect.

use super::children;
use crate::{
    formula::{
        internal::tuple_lowering::{NAMED_FIELD_LOGIC_FN_PREFIX, TUPLE_FIELD_LOGIC_FN_PREFIX},
        Pattern, PureExpr,
    },
    logic::final_reads::FinalReaders,
};

/// Whether `name` is the logic function a field access `e.f` or `e.0` lowers
/// to.
pub(super) fn is_field_projection(name: &str) -> bool {
    name.starts_with(NAMED_FIELD_LOGIC_FN_PREFIX) || name.starts_with(TUPLE_FIELD_LOGIC_FN_PREFIX)
}

/// Whether `method(args)` is the call an index `e[i]` lowers to.
fn is_element_projection(method: &str, args: &[PureExpr]) -> bool {
    args.len() == 1 && matches!(method, "index_logic" | "index")
}

/// The first final read in an assertion (`^e`, `resolve(e)` and every other
/// reading [`FinalReaders::final_operands`] names) whose operand is not a
/// borrow named as one: a variable, a `*` or `^` of one, or an `if`, `match`
/// or `let` that chooses among such. Any other operand — a field or tuple
/// element (`^x.m`, `^(^x).m`), an element (`^x[0]`, `^(x@[0])`), a view, or
/// a value a call computes — is the final value of a borrow that value
/// holds, when it holds one, and that borrow's holder decides it: the
/// assertion's function holds neither `x.m` of `x: &mut M { m: &mut i32 }`
/// nor `x[0]` of `x: &mut [&mut i32; 1]`, and no lane gives it a prophecy.
/// The encoder reads such an operand by Creusot's rule for a REBORROWED
/// place, `^(x.m) == (^x).m`, which is the value the outer borrow is left
/// with; an untouched `x` made `^x[0] == *x[0]` hold (D-129). The driver's
/// own image of a reborrow is substituted into the assertion after this
/// reads it, so only what the assertion's text writes is refused.
#[must_use]
pub fn first_final_of_a_value_not_named_as_a_borrow(
    expr: &PureExpr,
    readers: &FinalReaders,
) -> Option<String> {
    let mut walk = NamedBorrows {
        readers,
        scope: Vec::new(),
    };
    walk.expr(expr)
}

struct NamedBorrows<'a> {
    readers: &'a FinalReaders,
    /// Binders in scope, innermost last, each with whether its value is a
    /// borrow named as one.
    scope: Vec<(String, bool)>,
}

impl NamedBorrows<'_> {
    /// Whether `expr` is a borrow named as one: a variable not bound to
    /// another value, `*` or `^` of one, or an `if`, `match` or `let` whose
    /// every result is one.
    fn names_a_borrow(&mut self, expr: &PureExpr) -> bool {
        match expr {
            // A dotted name (`x.m`) is a field path a driver rewrite
            // flattened into one name, not a borrow named as one.
            PureExpr::Var(name, _) if name.contains('.') => false,
            PureExpr::Var(name, _) => self
                .scope
                .iter()
                .rev()
                .find(|(bound, _)| bound == name)
                .is_none_or(|(_, named)| *named),
            PureExpr::Deref(inner) | PureExpr::Final(inner) => self.names_a_borrow(inner),
            PureExpr::Ite(_, then_branch, else_branch) => {
                self.names_a_borrow(then_branch) && self.names_a_borrow(else_branch)
            }
            PureExpr::Match { scrutinee, arms } => {
                let whole = self.names_a_borrow(scrutinee);
                arms.iter().all(|arm| {
                    let depth = self.scope.len();
                    self.bind_pattern(&arm.pattern, whole);
                    let named = self.names_a_borrow(&arm.body);
                    self.scope.truncate(depth);
                    named
                })
            }
            PureExpr::Let { var, value, body } => {
                let named = self.names_a_borrow(value);
                self.scope.push((var.clone(), named));
                let body_named = self.names_a_borrow(body);
                self.scope.pop();
                body_named
            }
            _ => false,
        }
    }

    /// Bind a `match` arm's names: a bare binding names what the scrutinee
    /// names; a name a constructor, tuple or alias pattern takes apart is a
    /// part of the scrutinee, not a borrow named as one.
    fn bind_pattern(&mut self, pattern: &Pattern, whole: bool) {
        match pattern {
            Pattern::Binding(name) => self.scope.push((name.clone(), whole)),
            other => self.scope.extend(
                other
                    .bound_names()
                    .into_iter()
                    .map(|name| (name.to_string(), false)),
            ),
        }
    }

    fn expr(&mut self, expr: &PureExpr) -> Option<String> {
        if let Some(operands) = self.readers.final_operands(expr) {
            for operand in operands {
                if !self.names_a_borrow(operand) {
                    return Some(format!(
                        "`{expr}` reads the final value of `{operand}`, which is no borrow named as \
                         one: a borrow a field, element or view holds is its holder's, which \
                         decides its final value, and no lane gives it a prophecy; `(^x).f` reads \
                         the field `x` is left with"
                    ));
                }
            }
        }
        match expr {
            PureExpr::Let { var, value, body } => {
                if let Some(found) = self.expr(value) {
                    return Some(found);
                }
                let named = self.names_a_borrow(value);
                self.scope.push((var.clone(), named));
                let found = self.expr(body);
                self.scope.pop();
                found
            }
            PureExpr::Match { scrutinee, arms } => {
                if let Some(found) = self.expr(scrutinee) {
                    return Some(found);
                }
                let whole = self.names_a_borrow(scrutinee);
                arms.iter().find_map(|arm| {
                    let depth = self.scope.len();
                    self.bind_pattern(&arm.pattern, whole);
                    let found = self.expr(&arm.body);
                    self.scope.truncate(depth);
                    found
                })
            }
            PureExpr::Forall { var, .. } | PureExpr::Exists { var, .. } => {
                self.scope.push((var.clone(), true));
                let found = children(expr)
                    .into_iter()
                    .find_map(|child| self.expr(child));
                self.scope.pop();
                found
            }
            PureExpr::Closure { params, body } => {
                let depth = self.scope.len();
                self.scope
                    .extend(params.iter().map(|(name, _)| (name.clone(), true)));
                let found = self.expr(body);
                self.scope.truncate(depth);
                found
            }
            _ => children(expr)
                .into_iter()
                .find_map(|child| self.expr(child)),
        }
    }
}

/// What a parameter's type makes of `*p` and `^p`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParamReference {
    /// `&mut T`: `*p` and `^p` read its referent.
    Mutable,
    /// `&T`: `*p` reads its referent; `^p` has no reading.
    Shared,
    /// A value no `*` reads through (an integer, a `bool`, a `char`, a
    /// float, a tuple of such values): neither `*p` nor `^p` has a reading.
    Value,
    /// A `&mut`, or a value holding one, that a parameter holds without
    /// being it: a binding of a destructuring parameter pattern (`(p, q):
    /// (&mut i32, &mut i32)`), or a parameter whose value holds one (`t:
    /// (&mut i32, i32)`). The state rule places the reads of a `&mut`
    /// parameter's own name only, so a postcondition's `*`, `^` or `@` read
    /// through such a name has no placement.
    HeldMutable,
}

/// The first `*p` or `^p` of a parameter `p` whose type has no such read
/// ([`ParamReference`]), described for the refusal. A binder that shadows the
/// parameter's name is another value, and is left to its own reading.
///
/// `*x` of an `x: i32` has no reading, and was read as `x` itself where the
/// clause spelled it on the parameter, but not through a binder: `{ let ref
/// a @ t = x; *t == result }` was unknown, and the same `*x` spelled directly
/// verified. Every spelling now reads the one refusal.
#[must_use]
pub fn first_dereference_of_a_non_reference(
    expr: &PureExpr,
    param: &dyn Fn(&str) -> Option<ParamReference>,
) -> Option<String> {
    fn walk(
        expr: &PureExpr,
        param: &dyn Fn(&str) -> Option<ParamReference>,
        bound: &mut Vec<String>,
    ) -> Option<String> {
        let read = match expr {
            PureExpr::Deref(operand) => Some(('*', operand)),
            PureExpr::Final(operand) => Some(('^', operand)),
            _ => None,
        };
        if let Some((spelling, operand)) = read {
            if let PureExpr::Var(name, _) = operand.as_ref() {
                if !bound.iter().any(|binder| binder == name) {
                    match (spelling, param(name)) {
                        ('*' | '^', Some(ParamReference::Value)) => {
                            return Some(format!(
                                "`{spelling}{name}` reads through the parameter `{name}`, which \
                                 is not a reference"
                            ));
                        }
                        ('^', Some(ParamReference::Shared)) => {
                            return Some(format!(
                                "`^{name}` is the final value of the parameter `{name}`, which is \
                                 a shared reference"
                            ));
                        }
                        _ => {}
                    }
                }
            }
        }
        let depth = bound.len();
        let found = match expr {
            PureExpr::Let { var, value, body } => walk(value, param, bound).or_else(|| {
                bound.push(var.clone());
                walk(body, param, bound)
            }),
            PureExpr::Forall { var, .. } | PureExpr::Exists { var, .. } => {
                bound.push(var.clone());
                children(expr)
                    .into_iter()
                    .find_map(|child| walk(child, param, bound))
            }
            PureExpr::Closure { params, body } => {
                bound.extend(params.iter().map(|(name, _)| name.clone()));
                walk(body, param, bound)
            }
            PureExpr::Match { scrutinee, arms } => walk(scrutinee, param, bound).or_else(|| {
                arms.iter().find_map(|arm| {
                    let depth = bound.len();
                    bound.extend(arm.pattern.bound_names().into_iter().map(str::to_string));
                    let found = walk(&arm.body, param, bound);
                    bound.truncate(depth);
                    found
                })
            }),
            _ => children(expr)
                .into_iter()
                .find_map(|child| walk(child, param, bound)),
        };
        bound.truncate(depth);
        found
    }
    walk(expr, param, &mut Vec::new())
}

/// The first `*e`, `e@` or final read of `e` (however `readers` denote one:
/// `^e`, `resolve(e)`, a logic function reading `^` of its argument) whose
/// operand holds a `&mut` parameter other than as the name itself, or holds
/// a [`ParamReference::HeldMutable`] name at all, described for the refusal.
#[must_use]
pub fn first_unplaced_mut_ref_read(
    expr: &PureExpr,
    param: &dyn Fn(&str) -> Option<ParamReference>,
    readers: &FinalReaders,
) -> Option<String> {
    let mut walk = Walk {
        param,
        readers,
        scope: Vec::new(),
        finals_only: false,
        reached: Vec::new(),
    };
    walk.expr(expr)
}

/// The first final read (`^e`, `resolve(e)` and every other reading
/// `readers` denote) whose operand is a value reached through a reference
/// parameter by one or more projections: a dereference, a final value, a
/// field or tuple element, a view or an element of one, on any branch of an
/// `if` or `match` choosing the holder (`^x.m`, `^(x.m)`, `^*x`, `^(^x).m`,
/// `^x[0]`, `^(x@[0])` of `x: &mut ..` or `x: &..`). Such an operand, read by
/// `^`, is a borrow the parameter's referent holds, and its final value is
/// that inner borrow's, which its holder decides after the call; no lane
/// gives it a prophecy, and the encoder reads it by the reborrow rule as the
/// field the OUTER borrow is left with. Decided here, from the parameter's
/// type, once for every lane that reads a written clause: a precondition, a
/// postcondition, a `proof_assert!` and a loop invariant (D-183).
#[must_use]
pub fn first_final_held_through_a_reference_parameter(
    expr: &PureExpr,
    param: &dyn Fn(&str) -> Option<ParamReference>,
    readers: &FinalReaders,
) -> Option<String> {
    let mut walk = Walk {
        param,
        readers,
        scope: Vec::new(),
        finals_only: true,
        reached: Vec::new(),
    };
    walk.expr(expr)
}

struct Walk<'a> {
    param: &'a dyn Fn(&str) -> Option<ParamReference>,
    readers: &'a FinalReaders,
    /// Binders in scope, innermost last, each with whether its value holds a
    /// `&mut` parameter.
    scope: Vec<(String, bool)>,
    /// Whether only final reads of a value held through a reference
    /// parameter are refused ([`first_final_held_through_a_reference_parameter`]).
    finals_only: bool,
    /// Binders in scope, innermost last, each with the reference parameter
    /// its value is reached through and by how many projections: `m` of
    /// `match *x { M { m } => .. }` is `(*x).m`, two below `x`.
    reached: Vec<(String, Option<(String, usize)>)>,
}

impl Walk<'_> {
    /// Whether the name `name` read here holds a `&mut` parameter: a binder
    /// whose value holds one, or the free parameter itself.
    fn holds_by_name(&self, name: &str) -> bool {
        match self.scope.iter().rev().find(|(bound, _)| bound == name) {
            Some((_, holds)) => *holds,
            None => matches!(
                (self.param)(name),
                Some(ParamReference::Mutable | ParamReference::HeldMutable)
            ),
        }
    }

    /// Whether `expr` holds a `&mut` parameter's reference, not counting a
    /// `*p`, `^p` or `p@` read of the parameter's own name (a value, placed
    /// by the state rule).
    fn holds(&mut self, expr: &PureExpr) -> Option<String> {
        match expr {
            PureExpr::Var(name, _) => self.holds_by_name(name).then(|| name.clone()),
            PureExpr::Deref(inner) | PureExpr::Final(inner) | PureExpr::View(inner)
                if self.is_the_parameter_itself(inner) =>
            {
                None
            }
            // `p.f` and `p.0` of the parameter itself are `(*p).f` and
            // `(*p).0`: Rust's auto-deref reads a field of the referent, at
            // the state `*p` is placed at, and holds no reference.
            PureExpr::LogicFnCall { name, args }
                if args.len() == 1
                    && is_field_projection(name)
                    && self.is_the_parameter_itself(&args[0]) =>
            {
                None
            }
            _ => self.in_scope_of(expr, Walk::holds),
        }
    }

    /// Whether `expr` is a parameter's own name, not a binder in scope, and
    /// one whose reads the state rule places (not a
    /// [`ParamReference::HeldMutable`]).
    fn is_the_parameter_itself(&self, expr: &PureExpr) -> bool {
        matches!(expr, PureExpr::Var(name, _)
            if !self.scope.iter().any(|(bound, _)| bound == name)
                && (self.param)(name) != Some(ParamReference::HeldMutable))
    }

    /// `visit` over each child of `expr`, each under the binders `expr`
    /// puts in its scope: a `let` or `match` name holds a parameter when its
    /// value does.
    fn in_scope_of(
        &mut self,
        expr: &PureExpr,
        mut visit: impl FnMut(&mut Self, &PureExpr) -> Option<String>,
    ) -> Option<String> {
        match expr {
            PureExpr::Let { var, value, body } => {
                if let Some(found) = visit(self, value) {
                    return Some(found);
                }
                let holds = self.holds(value).is_some();
                let reached = self.reached_through_a_reference_parameter(value, 0);
                self.scope.push((var.clone(), holds));
                self.reached.push((var.clone(), reached));
                let found = visit(self, body);
                self.scope.pop();
                self.reached.pop();
                found
            }
            PureExpr::Match { scrutinee, arms } => {
                if let Some(found) = visit(self, scrutinee) {
                    return Some(found);
                }
                let holds = self.holds(scrutinee).is_some();
                let reached = self.reached_through_a_reference_parameter(scrutinee, 0);
                arms.iter().find_map(|arm| {
                    let depth = self.scope.len();
                    // A bare binding is the scrutinee; a name a constructor,
                    // tuple or alias pattern takes apart is a part of it.
                    let part = usize::from(!matches!(arm.pattern, Pattern::Binding(_)));
                    for name in arm.pattern.bound_names() {
                        self.scope.push((name.to_string(), holds));
                        self.reached.push((
                            name.to_string(),
                            reached
                                .clone()
                                .map(|(param, layers)| (param, layers + part)),
                        ));
                    }
                    let found = visit(self, &arm.body);
                    self.scope.truncate(depth);
                    self.reached.truncate(depth);
                    found
                })
            }
            PureExpr::Forall { var, .. } | PureExpr::Exists { var, .. } => {
                self.scope.push((var.clone(), false));
                self.reached.push((var.clone(), None));
                let found = children(expr)
                    .into_iter()
                    .find_map(|child| visit(self, child));
                self.scope.pop();
                self.reached.pop();
                found
            }
            PureExpr::Closure { params, body } => {
                let depth = self.scope.len();
                for (name, _) in params {
                    self.scope.push((name.clone(), false));
                    self.reached.push((name.clone(), None));
                }
                let found = visit(self, body);
                self.scope.truncate(depth);
                self.reached.truncate(depth);
                found
            }
            _ => children(expr)
                .into_iter()
                .find_map(|child| visit(self, child)),
        }
    }

    /// Each operand `expr` reads a state of, with the read as spelled.
    fn reads<'e>(&self, expr: &'e PureExpr) -> Vec<(String, &'e PureExpr)> {
        match expr {
            PureExpr::Deref(operand) => vec![(format!("*({operand})"), operand.as_ref())],
            PureExpr::View(operand) => vec![(format!("({operand})@"), operand.as_ref())],
            _ => self
                .readers
                .final_operands(expr)
                .unwrap_or_default()
                .into_iter()
                .map(|operand| {
                    let read = match expr {
                        PureExpr::Final(_) => format!("^({operand})"),
                        PureExpr::LogicFnCall { name, .. } => format!("{name}({operand})"),
                        PureExpr::MethodCall { method, .. } => format!("({operand}).{method}()"),
                        _ => format!("{expr}"),
                    };
                    (read, operand)
                })
                .collect(),
        }
    }

    /// The `&mut` parameter `expr` is a value held through, when `expr` is
    /// one or more reads or projections of that parameter's own name and not
    /// the name itself: a dereference or final value (`*p`, `^p`), a field
    /// or tuple element (`p.m`, `(^p).m`), a view (`p@`) or an element of
    /// one (`p[0]`, `p@[0]`), on any branch of an `if` or `match` that
    /// chooses the holder (`(if c { *p } else { *p }).m`). `(^p).m` is the
    /// borrow the referent is left holding, which the caller decides after
    /// the call as it does `p.m`'s (D-129).
    fn held_through_a_mutable_parameter(&self, expr: &PureExpr) -> Option<String> {
        self.reached_through_a_reference_parameter(expr, 0)
            .and_then(|(param, layers)| (layers > 0).then_some(param))
    }

    /// The reference parameter `expr` is reached through and by how many
    /// projections (`layers` counted above `expr`), when it is one: the
    /// parameter's own name (zero), or a binder in scope whose value is
    /// reached through one ([`Self::reached`]), under dereferences, final
    /// values, views, field and tuple getters, elements, `old` and every
    /// branch of an `if` or `match` choosing the holder.
    fn reached_through_a_reference_parameter(
        &self,
        expr: &PureExpr,
        layers: usize,
    ) -> Option<(String, usize)> {
        let below =
            |inner: &PureExpr| self.reached_through_a_reference_parameter(inner, layers + 1);
        match expr {
            PureExpr::Deref(inner) | PureExpr::Final(inner) | PureExpr::View(inner) => below(inner),
            PureExpr::LogicFnCall { name, args }
                if args.len() == 1 && is_field_projection(name) =>
            {
                below(&args[0])
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } if is_element_projection(method, args) => below(receiver),
            PureExpr::Old(inner) => self.reached_through_a_reference_parameter(inner, layers),
            PureExpr::Ite(_, then_branch, else_branch) => {
                let then_reached = self.reached_through_a_reference_parameter(then_branch, layers);
                let else_reached = self.reached_through_a_reference_parameter(else_branch, layers);
                // The deeper reach decides: a branch below the parameter is
                // a held borrow whatever the other branch is.
                match (then_reached, else_reached) {
                    (Some(a), Some(b)) => Some(if a.1 >= b.1 { a } else { b }),
                    (a, b) => a.or(b),
                }
            }
            PureExpr::Match { arms, .. } => arms
                .iter()
                .filter_map(|arm| {
                    // A name the arm binds is another value, not the parameter.
                    let shadowed = arm.pattern.bound_names();
                    let found = self.reached_through_a_reference_parameter(&arm.body, layers)?;
                    (!shadowed.contains(&found.0.as_str())).then_some(found)
                })
                .max_by_key(|(_, layers)| *layers),
            PureExpr::Var(name, _) => {
                if let Some((_, reached)) =
                    self.reached.iter().rev().find(|(bound, _)| bound == name)
                {
                    return reached
                        .clone()
                        .map(|(param, below)| (param, below + layers));
                }
                // A borrow reached through a shared reference parameter
                // (`^*x`, `^x.m` of `x: &M { m: &mut i32 }`) is no more the
                // function's than one reached through a `&mut` (D-183).
                (self.is_the_parameter_itself(expr)
                    && matches!(
                        (self.param)(name),
                        Some(ParamReference::Mutable | ParamReference::Shared)
                    ))
                .then(|| (name.clone(), layers))
            }
            _ => None,
        }
    }

    fn expr(&mut self, expr: &PureExpr) -> Option<String> {
        // A final value read of a value held through a `&mut` parameter
        // (`^(p.m)`, `^*p`, `resolve(p.m)`) is the final value of a borrow
        // `p`'s referent holds, when it has one: that borrow is its holder's
        // after the call, which decides the value, and no lane gives it a
        // prophecy. The name-keyed rule placed it as `(^p).m`, the field the
        // OUTER borrow is left with, so `^(x.m) == *(x.m)` of an untouched
        // `x: &mut M { m: &mut i32 }` held (D-127).
        if !matches!(expr, PureExpr::Deref(_) | PureExpr::View(_)) {
            for (read, operand) in self.reads(expr) {
                let Some(param) = self.held_through_a_mutable_parameter(operand) else {
                    continue;
                };
                let kind = if (self.param)(&param) == Some(ParamReference::Shared) {
                    // Through a shared reference only a written `^` is
                    // refused here: `resolve(*r)` of `r: &i32` is `true`,
                    // and `resolve` of a value that may hold a borrow is
                    // refused at its own type (D-126).
                    if !matches!(expr, PureExpr::Final(_)) {
                        continue;
                    }
                    "shared reference"
                } else {
                    "`&mut`"
                };
                return Some(format!(
                    "`{read}` reads the final value of a value held through the {kind} \
                     parameter `{param}`: a borrow `{param}`'s referent holds is its holder's \
                     after the call, which decides that value, and no lane gives it a \
                     prophecy; `(^{param}).f` reads the field `{param}` is left with"
                ));
            }
        }
        if self.finals_only {
            return self.in_scope_of(expr, Walk::expr);
        }
        for (read, operand) in self.reads(expr) {
            let placed = self.is_the_parameter_itself(operand)
                || matches!(operand, PureExpr::Var(name, _)
                    if self.scope.iter().rev().find(|(bound, _)| bound == name)
                        .is_some_and(|(_, holds)| !*holds));
            if !placed {
                if let Some(param) = self.holds(operand) {
                    return Some(format!(
                        "`{read}` reads through `{param}`, which holds a `&mut` parameter \
                         other than as that parameter's own name: the state a `&mut` \
                         parameter's referent is read at is placed only where `*p`, `^p` \
                         or `p@` names the parameter `p` itself, and a `&mut` a parameter \
                         holds without being it has no placement"
                    ));
                }
            }
        }
        self.in_scope_of(expr, Walk::expr)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        first_dereference_of_a_non_reference, first_unplaced_mut_ref_read, ParamReference,
    };
    use crate::{contract_parser::parse_contract, logic::final_reads::FinalReaders};

    fn ill_typed(text: &str) -> Option<String> {
        let expr = parse_contract(text).expect("parses");
        first_dereference_of_a_non_reference(&expr, &|name| match name {
            "p" => Some(ParamReference::Mutable),
            "r" => Some(ParamReference::Shared),
            "x" => Some(ParamReference::Value),
            _ => None,
        })
    }

    #[test]
    fn a_dereference_of_a_value_parameter_is_refused_however_spelled() {
        for text in [
            "*x == 0",
            "^x == 0",
            "^r == 0",
            "{ let t = x; *t == 0 }",
            "{ let ref a @ t = x; *t == 0 }",
            "match x { t => *t == 0 }",
        ] {
            assert!(ill_typed(text).is_some(), "{text}");
        }
        for text in [
            "*p == ^p",
            "*r == 0",
            "forall<x: &Int> *x == 0",
            "{ let x = r; *x == 0 }",
            "{ let ref a @ t = x; *a == 0 }",
        ] {
            assert_eq!(ill_typed(text), None, "{text}");
        }
    }

    fn unplaced(text: &str) -> Option<String> {
        let expr = parse_contract(text).expect("parses");
        first_unplaced_mut_ref_read(
            &expr,
            &|name| match name {
                "p" | "q" => Some(ParamReference::Mutable),
                "h" | "t" => Some(ParamReference::HeldMutable),
                _ => None,
            },
            &FinalReaders::default(),
        )
    }

    #[test]
    fn a_read_of_the_parameter_itself_is_placed() {
        for text in [
            "*p == old(*p) + 1",
            "^p == *p + 1",
            "p@ == old(p@)",
            "(*p)@ == old((*p)@)",
            "*(if c { p } else { q }) == 0",
            "match p { r => *r == 0 }",
            "(*p, 0).0 == 1",
            "*(p, 0).0 == 1",
            "{ let t = *p; old(t) == t }",
            "forall<r: &mut Int> *r == 0",
            "*x == 0",
            "(^p).v@.len() == p.v@.len() + 1",
            "p.0@ == old(p.0@)",
            "p.a.b@ == 0",
            "(*p).v@ == old(p.v@)",
        ] {
            assert_eq!(unplaced(text), None, "{text}");
        }
    }

    #[test]
    fn a_read_through_a_value_that_holds_the_parameter_is_refused() {
        for (text, param) in [
            ("{ let t = f(p); *t == old(*p) }", "t"),
            ("*id(p) == old(*p)", "p"),
            ("*old(p) == 0", "p"),
            (
                "match Some(p) { Some(r) => *r == old(*p), None => true }",
                "r",
            ),
            ("{ let t = f(p); (*t.0)@ == 0 }", "t"),
            ("match Some(p) { Some(r) => r.v@ == 0, None => true }", "r"),
            // A `&mut` a parameter holds without being it: a destructured
            // binding, a field of a tuple parameter.
            ("*h == old(*h)", "h"),
            ("old(*h) == 0", "h"),
            ("^h == 0", "h"),
            ("h@ == 0", "h"),
            ("h.v@ == 0", "h"),
            ("*t.0 == old(*t.0)", "t"),
            ("{ let u = h; *u == 0 }", "h"),
            // A final value however denoted: `resolve(e)` is `*e == ^e`.
            ("match Some(p) { Some(r) => resolve(r), None => true }", "r"),
            ("resolve(h)", "h"),
            ("{ let t = f(p); t.resolve() }", "t"),
        ] {
            let refusal = unplaced(text).unwrap_or_else(|| panic!("{text} is placed"));
            assert!(refusal.contains(&format!("`{param}`")), "{text}: {refusal}");
        }
    }

    /// A final value of a value held through a `&mut` parameter is the final
    /// value of a borrow its referent holds, which the holder decides after
    /// the call: `^x.m == *x.m` of an untouched `x: &mut M { m: &mut i32 }`
    /// was placed as `(^x).m == (*x).m` and verified (D-127). The field the
    /// outer borrow is left with stays placed.
    #[test]
    fn a_final_read_of_a_value_held_through_the_parameter_is_refused() {
        for text in [
            "^p.m == *p.m",
            "^(p.m) == *(p.m)",
            "^(p.0) == *(p.0)",
            "^((*p).m) == *((*p).m)",
            "^*p == **p",
            "^(*p) == **p",
            "resolve(p.m)",
            "resolve(*p)",
            // The borrow the referent is left holding, and a holder an `if`
            // or `match` chooses, an element and a view's element (D-129).
            "^(^p).m == *(^p).m",
            "^(^p).s.m == *(^p).s.m",
            "^(^p).m == *(*p).m",
            "^(if c { ^p } else { ^p }).m == *(^p).m",
            "^(if c { *p } else { *p }).m == *(*p).m",
            "^(match c { true => *p, false => *p }).m == *(*p).m",
            "^(p@[0]) == *(p@[0])",
            "^(p[0]) == *(p[0])",
            "^p[0].m == *p[0].m",
            "^^p == **p",
        ] {
            let refusal = unplaced(text).unwrap_or_else(|| panic!("{text} is placed"));
            assert!(refusal.contains("`p`"), "{text}: {refusal}");
        }
        for text in [
            "(^p).m == (*p).m",
            "^p == *p",
            "(^p).0 == p.0",
            "resolve(p)",
            "*p.m == 0",
            // `^p@[0]` is `(^p)@[0]`, the element `p` is left with.
            "^p@[0] == *p@[0]",
            "^(if c { p } else { q }) == 0",
            "(^(if c { p } else { q })).m == 0",
            "match c { true => ^p == *p, false => true }",
        ] {
            assert_eq!(unplaced(text), None, "{text}");
        }
    }

    fn held(text: &str) -> Option<String> {
        let expr = parse_contract(text).expect("parses");
        let reference = |name: &str| match name {
            "p" | "self" => Some(ParamReference::Mutable),
            "s" => Some(ParamReference::Shared),
            "k" => Some(ParamReference::Value),
            _ => None,
        };
        super::first_final_held_through_a_reference_parameter(
            &expr,
            &reference,
            &FinalReaders::default(),
        )
    }

    /// The final value of a borrow reached through any projection of a
    /// reference parameter is that inner borrow's, whatever clause reads it:
    /// a precondition (`#[requires(^x.m == k)]` of a body writing `*x.m = 5`
    /// proved `ensures(k == 5)`), a postcondition, a `proof_assert!`
    /// (`^*x == **x` of `x: &mut &mut i32` passed the name guard) or a loop
    /// invariant (D-183).
    #[test]
    fn a_final_held_through_a_reference_parameter_is_refused_in_every_clause() {
        for text in [
            "^p.m == k",
            "^(p.m) == k",
            "^p.m == *y",
            "^(*p).m == k",
            "^*p == **p",
            "^(*p) == **p",
            "^p[0] == *p[0]",
            "^(p@[0]) == *(p@[0])",
            "^(^p).m == *(^p).m",
            "^(if c { p } else { p }).m == 0",
            "^(if c { q } else { p.m }) == 0",
            "^(match c { true => *p, false => *p }).m == 0",
            "resolve(p.m)",
            "resolve(*p)",
            "^old(p.m) == 0",
            "^self.m == 0",
            "^s.m == 0",
            "^*s == **s",
            "{ let y = p.m; ^y == *y }",
            "{ let y = p; ^y.m == *y.m }",
            "match *p { M { m } => ^m == *m }",
            "match p { r => ^r.m == 0 }",
            "forall<i: Int> ^p[i] == *p[i]",
            "^(match *p { M { m } => m }) == 0",
            "^{ let y = p.m; y } == 0",
            "^{ let y = p; y.m } == 0",
            "^(match p { r => r.m }) == 0",
            "^(if c { ^p } else { *p }).m == 0",
        ] {
            let refusal = held(text).unwrap_or_else(|| panic!("{text} is not refused"));
            assert!(refusal.contains("parameter"), "{text}: {refusal}");
        }
        for text in [
            "^p == *p",
            "(^p).m == (*p).m",
            "^p@[0] == *p@[0]",
            "resolve(p)",
            "*p.m == 0",
            "^q.m == 0",
            "^(if c { p } else { q }) == 0",
            "{ let y = p; ^y == *y }",
            "match p { r => ^r == *r }",
            "{ let p = q.m; ^p == *p }",
            "forall<p: &mut Int> ^p == *p",
            "match c { true => ^p == 0, false => true }",
            "resolve(*s)",
            "resolve(s.v)",
        ] {
            assert_eq!(held(text), None, "{text}");
        }
    }

    fn unnamed(text: &str) -> Option<String> {
        let expr = parse_contract(text).expect("parses");
        super::first_final_of_a_value_not_named_as_a_borrow(&expr, &FinalReaders::default())
    }

    /// An assertion's final read of a value no name denotes as a borrow (a
    /// field, an element, a view, a value a call computes) is the final
    /// value of a borrow that value holds, which its holder decides: each of
    /// these was proved of an untouched `x` whose field or element is a
    /// borrow, read as the value the outer borrow is left with (D-129).
    #[test]
    fn a_final_of_a_value_not_named_as_a_borrow_is_refused() {
        for text in [
            "^x[0] == *x[0]",
            "^x[1] == *x[1]",
            "^x[0][0] == *x[0][0]",
            "^x[0].m == *x[0].m",
            "^x[0].0 == *x[0].0",
            "^x.m == *x.m",
            "^x.s.m == *x.s.m",
            "^(^x).m == *(^x).m",
            "^(if c { x } else { x }).m == *x.m",
            "^(match c { true => x, false => x }).m == *x.m",
            "^(if c { *x } else { *x }).m == *(*x).m",
            "^(x@[0]) == *(x@[0])",
            "resolve(x.m)",
            "{ let y = x.m; ^y == *y }",
            "match x { M { m } => ^m == *m }",
            "match Some(x.m) { Some(r) => ^r == *r, None => true }",
            "^f(x) == 0",
            "^old(x) == 0",
            "forall<i: Int> ^x[i] == *x[i]",
        ] {
            assert!(unnamed(text).is_some(), "{text} is not refused");
        }
        for text in [
            "^x == *x",
            "^*x == **x",
            "(^**by)@ == 1",
            "(^*bx2)@ == 2",
            "^x@[0] == *x@[0]",
            "(^x).m == (*x).m",
            "(^x)[0] == (*x)[0]",
            "^(if c { x } else { y }) == 0",
            "^(match c { true => x, false => y }) == 0",
            "{ let y = x; ^y == *y }",
            "match c { true => ^x == 0, false => true }",
            "resolve(x)",
            "forall<q: &mut Int> ^q == *q",
            "x.m@ == 3",
        ] {
            assert_eq!(unnamed(text), None, "{text}");
        }
        // A driver rewrite that flattened `x.m` into one name (`x.0`, as a
        // loop invariant reaches the lane) is a field path, not a borrow
        // named as one (D-129).
        let flattened = crate::formula::PureExpr::Final(std::sync::Arc::new(
            crate::formula::PureExpr::Var("x.0".to_string(), None),
        ));
        assert!(
            super::first_final_of_a_value_not_named_as_a_borrow(
                &flattened,
                &FinalReaders::default()
            )
            .is_some(),
            "^x.0 of a flattened field path is not refused"
        );
    }
}
