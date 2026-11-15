// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The sort of every subterm of a claim, decided once by unification over
//! its uses, and written onto the claim ([`elaborate`]): each name, free or
//! bound, is annotated with the sort its uses and its binder give it, so
//! every consumer (the claim decoder's admission checks, native replay's
//! rules, a summary fact's endpoints) reads the one sort from the node
//! instead of re-deriving it from its own environment.
//!
//! A pure-expr predicate declares no sorts, so what `x` means in it is fixed
//! only by where it stands: an operand of arithmetic or of an ordering is an
//! integer, an operand of a connective is a boolean, and the two sides of an
//! equality are one sort, the operand of `*` (`^`) is a reference to the
//! sort the dereference is read at, and the operand of `@` is a value whose
//! view has the sort the view is read at: one sort per operand, however
//! often the claim views it. A consumer that attaches meaning to a
//! name from outside the claim (a clause binding) must agree with that
//! reading, or it describes a claim other than the one proved. The inference
//! is fail-closed: a name read at two sorts is [`NativeNameUse::Conflicting`],
//! and a use it does not model reads the name at a described
//! [`NativeUseSort::Other`], which agrees with no `Int` or `Bool` reading. A
//! bound name is read at its binder's declared sort too, so a use (an
//! annotation included) at another sort conflicts with the binder: a
//! `forall<p: &bool>` whose `*p` is added to reads `p` as a reference to both
//! an `Int` and a `Bool`.
//!
//! A reference sort is never inferred from a use alone: `*b` of a name no
//! binder or annotation makes a reference has no sort, and is refused
//! ([`unmodeled_dereference`]).

use std::{fmt, sync::Arc};

use crate::formula::{BinOp, ExprSort, PureExpr, UnOp};

fn viewed() -> NativeUseSort {
    NativeUseSort::Other("a value with a view".to_string())
}

/// A sort a use of a name reads it at.
///
/// Deliberately exhaustive: a consumer that admits a reading must classify a
/// new sort before it builds, never admit it by a wildcard.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeUseSort {
    /// An unbounded mathematical integer.
    Int,
    Bool,
    /// Anything else, described: a reference (to the sort its dereferences
    /// read), a declared sort other than `Int` or `Bool`, or a use the
    /// inference does not model (a method call, ...).
    Other(String),
}

impl NativeUseSort {
    fn rank(&self) -> (u8, &str) {
        match self {
            Self::Int => (0, ""),
            Self::Bool => (1, ""),
            Self::Other(what) => (2, what),
        }
    }
}

impl fmt::Display for NativeUseSort {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int => formatter.write_str("Int"),
            Self::Bool => formatter.write_str("Bool"),
            Self::Other(what) => formatter.write_str(what),
        }
    }
}

/// How a claim's goal reads one of its free names, over all its uses.
///
/// Deliberately exhaustive, for the same reason as [`NativeUseSort`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeNameUse {
    /// Every use that fixes a sort fixes this one.
    Sort(NativeUseSort),
    /// No use fixes a sort (`x == x`); an unsorted name is read as `Int`, the
    /// formula AST's convention for an absent sort, which is how native
    /// replay reads it.
    Unfixed,
    /// Two uses read the name at different sorts, so no one sort is its
    /// reading. The pair is ordered `Int`, `Bool`, then the others by
    /// description, whatever order the uses came in.
    Conflicting(NativeUseSort, NativeUseSort),
}

/// The free names of `goal`, in first-use order, each with how the goal reads
/// it. The goal itself is read as a boolean.
pub(crate) fn infer_name_uses(goal: &PureExpr) -> Vec<(String, NativeNameUse)> {
    let mut inference = UseInference::default();
    let root = inference.walk(goal, &mut Vec::new());
    inference.fix(root, NativeUseSort::Bool);
    let free = std::mem::take(&mut inference.free);
    inference.readings(free)
}

/// What a class of sort variables is fixed at.
#[derive(Debug, Clone)]
enum Fixed {
    /// A sort that is neither a reference nor a viewed value.
    Sort(NativeUseSort),
    /// A reference, to the class of this variable.
    Ref(usize),
    /// A value whose view (`@`) is of the class of this variable. A view is
    /// a function of its operand, so two views of one class are one class.
    Viewed(usize),
}

/// What a class is read through on the way to a sort.
#[derive(Debug, Clone, Copy)]
enum Through {
    Reference,
    View,
}

impl Through {
    fn describe(self, sort: NativeUseSort) -> NativeUseSort {
        NativeUseSort::Other(match self {
            Self::Reference => format!("a reference to {sort}"),
            Self::View => format!("a value whose view is {sort}"),
        })
    }
}

/// `sort` behind each of `path`, innermost last.
fn behind(path: &[Through], sort: NativeUseSort) -> NativeUseSort {
    path.iter()
        .rev()
        .fold(sort, |sort, through| through.describe(sort))
}

/// Union-find over sort variables: one per free name, per bound name and per
/// subexpression value. A root carries what its class is fixed at (a sort,
/// or a reference to another class), or the first two sorts that contradict
/// each other.
#[derive(Default)]
struct UseInference {
    parent: Vec<usize>,
    fixed: Vec<Option<Fixed>>,
    conflict: Vec<Option<(NativeUseSort, NativeUseSort)>>,
    /// Per root, the first sort a binder or an annotation declared its class
    /// at, whole (`&[Int]`, `T`): the sort a name of the class is written
    /// with.
    declared: Vec<Option<ExprSort>>,
    /// The class of each name occurrence [`Self::walk`] visits, in the order
    /// it visits them, which [`Self::annotate`] follows.
    occurrences: Vec<usize>,
    /// Free names in first-use order.
    free: Vec<(String, usize)>,
    /// Names a quantifier or a `let` binds, in binder order, each with the
    /// variable of that binding.
    bound: Vec<(String, usize)>,
}

impl UseInference {
    /// How the goal reads each of `names`, from the inference's final state.
    fn readings(&mut self, names: Vec<(String, usize)>) -> Vec<(String, NativeNameUse)> {
        names
            .into_iter()
            .map(|(name, var)| {
                let reading = match self.reading(var) {
                    // Reported in a fixed order, not the order unification met
                    // them in.
                    NativeNameUse::Conflicting(first, second) if first.rank() > second.rank() => {
                        NativeNameUse::Conflicting(second, first)
                    }
                    reading => reading,
                };
                (name, reading)
            })
            .collect()
    }

    /// How the goal reads `var`: its class's sort, or its conflict, followed
    /// through each reference to what the reference is read to point at, and
    /// through each viewed value to what its view is read at. A conflict in a
    /// referent is a conflict of the reference (`p` read as a reference to
    /// both `Int` and `Bool`), one in a view a conflict of the viewed value
    /// (`b@` read as both an `Int` and a `Bool`), and a reference that points
    /// at its own class has no sort at all.
    fn reading(&mut self, var: usize) -> NativeNameUse {
        let mut root = self.find(var);
        let mut path = Vec::new();
        let mut seen = Vec::new();
        loop {
            if seen.contains(&root) {
                let (value, own) = match path.pop() {
                    Some(Through::View) => ("a value with a view", "its own view"),
                    Some(Through::Reference) | None => ("a reference", "the value it references"),
                };
                return NativeNameUse::Conflicting(
                    behind(&path, NativeUseSort::Other(value.to_string())),
                    behind(&path, NativeUseSort::Other(own.to_string())),
                );
            }
            seen.push(root);
            if let Some((first, second)) = self.conflict[root].clone() {
                return NativeNameUse::Conflicting(behind(&path, first), behind(&path, second));
            }
            match self.fixed[root].clone() {
                Some(Fixed::Sort(sort)) => return NativeNameUse::Sort(behind(&path, sort)),
                Some(Fixed::Ref(referent)) => {
                    path.push(Through::Reference);
                    root = self.find(referent);
                }
                Some(Fixed::Viewed(view)) => {
                    path.push(Through::View);
                    root = self.find(view);
                }
                None => {
                    return match path.pop() {
                        None => NativeNameUse::Unfixed,
                        Some(Through::Reference) => NativeNameUse::Sort(behind(
                            &path,
                            NativeUseSort::Other("a reference".to_string()),
                        )),
                        Some(Through::View) => NativeNameUse::Sort(behind(
                            &path,
                            NativeUseSort::Other("a value with a view".to_string()),
                        )),
                    }
                }
            }
        }
    }

    fn fresh(&mut self) -> usize {
        let var = self.parent.len();
        self.parent.push(var);
        self.fixed.push(None);
        self.conflict.push(None);
        self.declared.push(None);
        var
    }

    fn fixed(&mut self, sort: NativeUseSort) -> usize {
        let var = self.fresh();
        self.fix(var, sort);
        var
    }

    fn find(&mut self, var: usize) -> usize {
        let mut root = var;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        let mut at = var;
        while self.parent[at] != root {
            let next = self.parent[at];
            self.parent[at] = root;
            at = next;
        }
        root
    }

    fn fix(&mut self, var: usize, sort: NativeUseSort) {
        let root = self.find(var);
        if self.conflict[root].is_some() {
            return;
        }
        match self.fixed[root].clone() {
            None => self.fixed[root] = Some(Fixed::Sort(sort)),
            Some(Fixed::Sort(existing)) if existing == sort => {}
            Some(Fixed::Sort(existing)) => self.conflict[root] = Some((existing, sort)),
            Some(Fixed::Ref(_)) => {
                self.conflict[root] = Some((NativeUseSort::Other("a reference".to_string()), sort));
            }
            Some(Fixed::Viewed(_)) => {
                self.conflict[root] = Some((viewed(), sort));
            }
        }
    }

    /// Fix `var` as a reference to the class of `referent`.
    fn fix_ref(&mut self, var: usize, referent: usize) {
        let root = self.find(var);
        if self.conflict[root].is_some() {
            return;
        }
        match self.fixed[root].clone() {
            None => self.fixed[root] = Some(Fixed::Ref(referent)),
            Some(Fixed::Ref(existing)) => self.unify(existing, referent),
            Some(Fixed::Sort(existing)) => {
                self.conflict[root] =
                    Some((existing, NativeUseSort::Other("a reference".to_string())));
            }
            Some(Fixed::Viewed(_)) => {
                self.conflict[root] =
                    Some((viewed(), NativeUseSort::Other("a reference".to_string())));
            }
        }
    }

    /// Fix `var` as a value whose view is of the class of `view`. A second
    /// view of one class is the first: the view is a function of the value,
    /// so `b@ == true` and `b@ + 1` read one view at two sorts. A viewed value
    /// that is also read at a sort, or as a reference, conflicts: native
    /// replay models the view of no sort a claim fixes.
    fn fix_view(&mut self, var: usize, view: usize) {
        let root = self.find(var);
        if self.conflict[root].is_some() {
            return;
        }
        match self.fixed[root].clone() {
            None => self.fixed[root] = Some(Fixed::Viewed(view)),
            Some(Fixed::Viewed(existing)) => self.unify(existing, view),
            Some(Fixed::Sort(existing)) => {
                self.conflict[root] = Some((existing, viewed()));
            }
            Some(Fixed::Ref(_)) => {
                self.conflict[root] =
                    Some((NativeUseSort::Other("a reference".to_string()), viewed()));
            }
        }
    }

    /// Fix `var` at a sort a binder declares: a reference fixes a class for
    /// its referent, so a dereference reads the declared referent sort.
    fn fix_declared(&mut self, var: usize, sort: &ExprSort) {
        let root = self.find(var);
        if self.declared[root].is_none() {
            self.declared[root] = Some(sort.clone());
        }
        match sort {
            ExprSort::Int => self.fix(var, NativeUseSort::Int),
            ExprSort::Bool => self.fix(var, NativeUseSort::Bool),
            ExprSort::Ref(referent) | ExprSort::MutRef(referent) => {
                let referent_var = self.fresh();
                self.fix_declared(referent_var, referent);
                self.fix_ref(var, referent_var);
            }
            other => self.fix(var, NativeUseSort::Other(other.to_string())),
        }
    }

    fn unify(&mut self, left: usize, right: usize) {
        let left = self.find(left);
        let right = self.find(right);
        if left == right {
            return;
        }
        self.parent[right] = left;
        if self.conflict[left].is_none() {
            self.conflict[left] = self.conflict[right].take();
        }
        if self.declared[left].is_none() {
            self.declared[left] = self.declared[right].take();
        }
        match self.fixed[right].take() {
            Some(Fixed::Sort(sort)) => self.fix(left, sort),
            Some(Fixed::Ref(referent)) => self.fix_ref(left, referent),
            Some(Fixed::Viewed(view)) => self.fix_view(left, view),
            None => {}
        }
    }

    /// The variable a name denotes here: the innermost binder of that
    /// spelling in `scope`, else the free name's own.
    fn name_var(&mut self, name: &str, scope: &[(String, usize)]) -> usize {
        if let Some((_, var)) = scope.iter().rev().find(|(bound, _)| bound == name) {
            return *var;
        }
        if let Some((_, var)) = self.free.iter().find(|(free, _)| free == name) {
            return *var;
        }
        let var = self.fresh();
        self.free.push((name.to_string(), var));
        var
    }

    /// Every name `expr` reads, free or bound in `scope`, stands in a use the
    /// inference does not model, and so is read at `what`.
    fn unmodeled(&mut self, expr: &PureExpr, scope: &[(String, usize)], what: &str) -> usize {
        let mut names = Vec::new();
        expr.for_each_free_var(|name, _| names.push(name.to_string()));
        for name in names {
            let var = self.name_var(&name, scope);
            self.fix(var, NativeUseSort::Other(what.to_string()));
        }
        self.fixed(NativeUseSort::Other(what.to_string()))
    }

    #[allow(clippy::too_many_lines)]
    fn walk(&mut self, expr: &PureExpr, scope: &mut Vec<(String, usize)>) -> usize {
        match expr {
            PureExpr::Bool(_) => self.fixed(NativeUseSort::Bool),
            PureExpr::Int(_) => self.fixed(NativeUseSort::Int),
            PureExpr::Float(_) => self.fixed(NativeUseSort::Other("Float".to_string())),
            PureExpr::Var(name, sort) => {
                let var = self.name_var(name, scope);
                if let Some(sort) = sort {
                    self.fix_declared(var, sort);
                }
                self.occurrences.push(var);
                var
            }
            PureExpr::BinOp(left, op, right) => {
                let left = self.walk(left, scope);
                let right = self.walk(right, scope);
                match op {
                    BinOp::Eq | BinOp::Ne => {
                        self.unify(left, right);
                        self.fixed(NativeUseSort::Bool)
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        self.fix(left, NativeUseSort::Int);
                        self.fix(right, NativeUseSort::Int);
                        self.fixed(NativeUseSort::Bool)
                    }
                    BinOp::And | BinOp::Or | BinOp::Implies => {
                        self.fix(left, NativeUseSort::Bool);
                        self.fix(right, NativeUseSort::Bool);
                        self.fixed(NativeUseSort::Bool)
                    }
                    // Native replay reads every one of these as integer
                    // arithmetic, the bitwise ones included.
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Mod
                    | BinOp::DivTrunc
                    | BinOp::RemTrunc
                    | BinOp::Shl
                    | BinOp::Shr
                    | BinOp::BitAnd
                    | BinOp::BitXor
                    | BinOp::BitOr => {
                        self.fix(left, NativeUseSort::Int);
                        self.fix(right, NativeUseSort::Int);
                        self.fixed(NativeUseSort::Int)
                    }
                }
            }
            PureExpr::UnOp(UnOp::Not, inner) => {
                let inner = self.walk(inner, scope);
                self.fix(inner, NativeUseSort::Bool);
                self.fixed(NativeUseSort::Bool)
            }
            PureExpr::UnOp(UnOp::Neg | UnOp::BitNot, inner) => {
                let inner = self.walk(inner, scope);
                self.fix(inner, NativeUseSort::Int);
                self.fixed(NativeUseSort::Int)
            }
            PureExpr::Ite(cond, then_expr, else_expr) => {
                let cond = self.walk(cond, scope);
                self.fix(cond, NativeUseSort::Bool);
                let then_value = self.walk(then_expr, scope);
                let else_value = self.walk(else_expr, scope);
                self.unify(then_value, else_value);
                then_value
            }
            // `old(e)` is `e` in the entry state: the same sort.
            PureExpr::Old(inner) => self.walk(inner, scope),
            // The operand is a reference to the sort the dereference (the
            // final value) is read at.
            PureExpr::Deref(inner) | PureExpr::Final(inner) => {
                let inner = self.walk(inner, scope);
                let referent = self.fresh();
                self.fix_ref(inner, referent);
                referent
            }
            // The view of the operand's class: every view of one operand is
            // one sort variable. Native replay models the view of an integer
            // only (that integer), so the view is read as an `Int` and a use
            // at any other sort conflicts with it.
            PureExpr::View(inner) => {
                let inner = self.walk(inner, scope);
                let view = self.fresh();
                self.fix_view(inner, view);
                self.fix(view, NativeUseSort::Int);
                view
            }
            PureExpr::MethodCall { .. } => self.unmodeled(expr, scope, "a method-call operand"),
            PureExpr::Match { .. } => self.unmodeled(expr, scope, "a match operand"),
            PureExpr::LogicFnCall { .. } => self.unmodeled(expr, scope, "a logic-function operand"),
            PureExpr::Closure { .. } => self.unmodeled(expr, scope, "a closure operand"),
            PureExpr::Forall {
                var,
                var_sort,
                body,
                ..
            }
            | PureExpr::Exists {
                var,
                var_sort,
                body,
                ..
            } => {
                let bound = self.fresh();
                if let Some(sort) = var_sort {
                    self.fix_declared(bound, sort);
                }
                self.bound.push((var.clone(), bound));
                scope.push((var.clone(), bound));
                let body = self.walk(body, scope);
                scope.pop();
                self.fix(body, NativeUseSort::Bool);
                self.fixed(NativeUseSort::Bool)
            }
            // `let v = e in b` reads `v` at `e`'s sort: a use of `v` in `b`
            // is a use of whatever `e` reads.
            PureExpr::Let { var, value, body } => {
                let value = self.walk(value, scope);
                self.bound.push((var.clone(), value));
                scope.push((var.clone(), value));
                let body = self.walk(body, scope);
                scope.pop();
                body
            }
            PureExpr::LetAssume {
                assumption: left,
                body: right,
            }
            | PureExpr::LetObligation {
                obligation: left,
                body: right,
            } => {
                let left = self.walk(left, scope);
                let right = self.walk(right, scope);
                self.fix(left, NativeUseSort::Bool);
                self.fix(right, NativeUseSort::Bool);
                self.fixed(NativeUseSort::Bool)
            }
        }
    }
}

impl UseInference {
    /// The sort a name of class `var` is written with: the sort a binder or
    /// an annotation declared the class at, else the `Int` or `Bool` its uses
    /// fix, else none (an unfixed name, a viewed one, one only an unmodeled
    /// use reads).
    fn resolve(&mut self, var: usize) -> Option<ExprSort> {
        let root = self.find(var);
        if let Some(declared) = &self.declared[root] {
            return Some(declared.clone());
        }
        match &self.fixed[root] {
            Some(Fixed::Sort(NativeUseSort::Int)) => Some(ExprSort::Int),
            Some(Fixed::Sort(NativeUseSort::Bool)) => Some(ExprSort::Bool),
            _ => None,
        }
    }

    /// `expr` with each name occurrence [`Self::walk`] visited annotated with
    /// its class's sort ([`Self::resolve`]). Follows `walk` node for node: an
    /// unmodeled node (a method call, a `match`, a logic-function call, a
    /// closure, a float) is left as it is, and a quantifier's triggers too.
    fn annotate(&mut self, expr: &PureExpr, cursor: &mut usize) -> PureExpr {
        let mut sub =
            |this: &mut Self, child: &Arc<PureExpr>| Arc::new(this.annotate(child, cursor));
        match expr {
            PureExpr::Bool(_)
            | PureExpr::Int(_)
            | PureExpr::Float(_)
            | PureExpr::MethodCall { .. }
            | PureExpr::Match { .. }
            | PureExpr::LogicFnCall { .. }
            | PureExpr::Closure { .. } => expr.clone(),
            PureExpr::Var(name, annotation) => {
                let Some(&var) = self.occurrences.get(*cursor) else {
                    return expr.clone();
                };
                *cursor += 1;
                PureExpr::Var(
                    name.clone(),
                    self.resolve(var).or_else(|| annotation.clone()),
                )
            }
            PureExpr::BinOp(left, op, right) => {
                let left = sub(self, left);
                PureExpr::BinOp(left, *op, sub(self, right))
            }
            PureExpr::UnOp(op, inner) => PureExpr::UnOp(*op, sub(self, inner)),
            PureExpr::Ite(cond, then_expr, else_expr) => {
                let cond = sub(self, cond);
                let then_expr = sub(self, then_expr);
                PureExpr::Ite(cond, then_expr, sub(self, else_expr))
            }
            PureExpr::Old(inner) => PureExpr::Old(sub(self, inner)),
            PureExpr::Deref(inner) => PureExpr::Deref(sub(self, inner)),
            PureExpr::Final(inner) => PureExpr::Final(sub(self, inner)),
            PureExpr::View(inner) => PureExpr::View(sub(self, inner)),
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => PureExpr::Forall {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: sub(self, body),
                triggers: triggers.clone(),
            },
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } => PureExpr::Exists {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: sub(self, body),
                triggers: triggers.clone(),
            },
            PureExpr::Let { var, value, body } => {
                let value = sub(self, value);
                PureExpr::Let {
                    var: var.clone(),
                    value,
                    body: sub(self, body),
                }
            }
            PureExpr::LetAssume { assumption, body } => {
                let assumption = sub(self, assumption);
                PureExpr::LetAssume {
                    assumption,
                    body: sub(self, body),
                }
            }
            PureExpr::LetObligation { obligation, body } => {
                let obligation = sub(self, obligation);
                PureExpr::LetObligation {
                    obligation,
                    body: sub(self, body),
                }
            }
        }
    }
}

/// A claim with the sort of every subterm decided: the one typing pass every
/// consumer of the claim reads.
#[derive(Debug, Clone)]
pub(crate) struct Elaboration {
    /// The claim, each name annotated with its sort ([`sort_of`] reads any
    /// subterm's).
    pub(crate) typed: PureExpr,
    /// The first name, free or bound, read at two sorts, with the two.
    pub(crate) conflict: Option<(String, NativeUseSort, NativeUseSort)>,
}

/// Elaborate `goal`, read as a boolean.
#[must_use]
pub(crate) fn elaborate(goal: &PureExpr) -> Elaboration {
    let mut inference = UseInference::default();
    let root = inference.walk(goal, &mut Vec::new());
    inference.fix(root, NativeUseSort::Bool);
    let mut names = std::mem::take(&mut inference.free);
    names.append(&mut std::mem::take(&mut inference.bound));
    let conflict = inference
        .readings(names)
        .into_iter()
        .find_map(|(name, used)| match used {
            NativeNameUse::Conflicting(first, second) => Some((name, first, second)),
            NativeNameUse::Sort(_) | NativeNameUse::Unfixed => None,
        });
    let mut cursor = 0;
    let typed = inference.annotate(goal, &mut cursor);
    debug_assert_eq!(cursor, inference.occurrences.len());
    Elaboration { typed, conflict }
}

/// The sort an elaborated subterm has where the claim fixes one: a name its
/// annotation, a literal its own, `*e` and `^e` the sort `e` references,
/// through `old`, `if` branches that agree and `let` bodies. A name with no
/// sort has none: it is read as an integer by convention, never as a
/// reference.
#[must_use]
pub(crate) fn sort_of(expr: &PureExpr) -> Option<ExprSort> {
    match expr {
        PureExpr::Int(_) => Some(ExprSort::Int),
        PureExpr::Bool(_) => Some(ExprSort::Bool),
        PureExpr::Var(_, annotation) => annotation.clone(),
        PureExpr::Deref(operand) => dereferenced(operand, Dereference::Current).referent(),
        PureExpr::Final(operand) => dereferenced(operand, Dereference::Final).referent(),
        PureExpr::Old(inner) | PureExpr::Let { body: inner, .. } => sort_of(inner),
        PureExpr::Ite(_, then_expr, else_expr) => {
            let then_sort = sort_of(then_expr)?;
            (sort_of(else_expr)? == then_sort).then_some(then_sort)
        }
        _ => None,
    }
}

/// Which value of a reference a dereference reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Dereference {
    /// `*e`: the current value, of a shared or a mutable reference.
    Current,
    /// `^e`: the value when the borrow ends, of a mutable reference only.
    Final,
}

impl Dereference {
    fn spelling(self) -> char {
        match self {
            Self::Current => '*',
            Self::Final => '^',
        }
    }
}

/// What a dereference of an operand reads, by the operand's sort.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Dereferenced {
    /// The operand references a value of this sort.
    Referent(ExprSort),
    /// The operand has this sort, which the dereference does not read
    /// through: not a reference (for `^`, not a mutable one).
    NotAReference(ExprSort),
    /// Nothing in the claim gives the operand a sort.
    Unsorted,
}

impl Dereferenced {
    pub(crate) fn referent(self) -> Option<ExprSort> {
        match self {
            Self::Referent(sort) => Some(sort),
            Self::NotAReference(_) | Self::Unsorted => None,
        }
    }
}

/// What `*operand` (`^operand`) of an elaborated operand reads.
pub(crate) fn dereferenced(operand: &PureExpr, dereference: Dereference) -> Dereferenced {
    match (sort_of(operand), dereference) {
        (Some(ExprSort::MutRef(referent)), _)
        | (Some(ExprSort::Ref(referent)), Dereference::Current) => {
            Dereferenced::Referent(*referent)
        }
        (Some(sort), _) => Dereferenced::NotAReference(sort),
        (None, _) => Dereferenced::Unsorted,
    }
}

/// Why `*operand` (`^operand`) of an elaborated operand has no sort native
/// replay models, or `None` when it reads an `Int`, a `Bool` or a
/// reference. A type parameter could be any type and a slice is a sequence;
/// each was read as an integer.
pub(crate) fn unmodeled_dereference(
    operand: &PureExpr,
    dereference: Dereference,
) -> Option<String> {
    let spelled = format!("{}{operand}", dereference.spelling());
    match dereferenced(operand, dereference) {
        Dereferenced::Referent(
            ExprSort::Int | ExprSort::Bool | ExprSort::Ref(_) | ExprSort::MutRef(_),
        ) => None,
        Dereferenced::Referent(referent) => Some(format!(
            "`{spelled}` reads the referent of `{operand}` at sort {referent}, which native \
             replay does not model"
        )),
        Dereferenced::NotAReference(sort) => Some(match dereference {
            Dereference::Current => format!(
                "`{spelled}` dereferences `{operand}`, which is not a reference: its sort is {sort}"
            ),
            Dereference::Final => format!(
                "`{spelled}` is the final value of `{operand}`, which is not a mutable \
                 reference: its sort is {sort}"
            ),
        }),
        Dereferenced::Unsorted => Some(format!(
            "`{spelled}` dereferences `{operand}`, which nothing in the claim makes a reference"
        )),
    }
}

/// The first dereference (`*e`) or final value (`^e`) of an elaborated
/// claim that reads no sort native replay models ([`unmodeled_dereference`]),
/// described for the refusal.
pub(crate) fn first_unmodeled_dereference(typed: &PureExpr) -> Option<String> {
    let mut found = None;
    typed.for_each_recursive(|node| {
        if found.is_some() {
            return;
        }
        found = match node {
            PureExpr::Deref(operand) => unmodeled_dereference(operand, Dereference::Current),
            PureExpr::Final(operand) => unmodeled_dereference(operand, Dereference::Final),
            _ => None,
        };
    });
    found
}
