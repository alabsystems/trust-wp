// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pure expression AST types.
//!
//! Contains `PureExpr`, `MatchArm`, `Pattern` — the core heap-independent
//! expression language used in separation logic formulas.

use std::sync::Arc;

pub use super::float_bits::FloatBits;
use super::{
    sort_intern::resolve_sort_name,
    types::{BinOp, UnOp},
};

mod free_vars;
mod pattern;
mod rewrite;
mod walk;

pub use rewrite::PureExprChildRole;

/// Sort annotation for expressions, carrying type information from MIR into SMT.
///
/// Used as `Option<ExprSort>` on `PureExpr` nodes to override the default `Sort::Int`
/// when the Rust type is known. `None` means "use default (Int)" for backward
/// compatibility. This is the mechanism by which MIR type information flows from
/// the driver into the ay encoder.
///
/// Relationship to other sort enums:
/// - `ExprSort` models expression-level sort annotations, including `Unit`
/// - `logic::ParamSortHint` stores only non-default overrides (Bool/Seq/Datatype)
/// - `smt::VarSort` models SMT declaration sorts and therefore excludes `Unit`
///
/// Extensible for future Datatype/Uninterpreted sorts when generic ADT encoding
/// is implemented (#717).
///
/// Reference: designs/2026-02-08-encoder-sort-inference.md (Option A)
/// Extended with Datatype/FMap/Tuple/Ref per designs/2026-03-07-994-solver-unknown-alternative.md
/// Datatype interned per designs/2026-03-07-expr-sort-interning.md (#2047)
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprSort {
    /// Integer sort (i8, i16, i32, i64, u8, u16, u32, u64, isize, usize)
    Int,
    /// Boolean sort
    Bool,
    /// Sequence sort (Vec<T>@, Seq<T> — logical view of collections)
    Seq,
    /// Unit sort — the singleton type `()`. Quantifiers over Unit are trivially
    /// eliminable: `forall<_x: ()> P` ≡ `P`, `exists<_x: ()> P` ≡ `P`.
    Unit,
    /// Algebraic data type, carrying an interned ID for the ADT `def_path_str`.
    /// Use `intern_sort_name` / `resolve_sort_name` to convert. (#994, #2036, #2047)
    Datatype(u32),
    /// Finite map sort. Previously hinted but not representable in `ExprSort`.
    FMap,
    /// Tuple sort with arity. Prevents Seq/Int confusion for multi-return functions.
    Tuple(u8),
    /// Reference sort, preserving the referent's sort. Allows tracking sort
    /// through dereference chains without losing type information.
    Ref(Box<ExprSort>),
    /// Mutable reference sort, preserving the referent's sort while keeping
    /// `&mut T` distinct from `&T` in the annotation layer.
    MutRef(Box<ExprSort>),
    /// Generic type parameter sort (T, K, V, ...), carrying an interned ID
    /// for the parameter name. Distinct from Datatype: this is an opaque
    /// polymorphic sort placeholder, not a declared ADT. (#2062)
    TypeParam(u32),
    /// Float sort (f32, f64). Maps to SMT `Real` — exact rational arithmetic
    /// without IEEE 754 semantics (no NaN, infinity, or rounding). (#1802)
    Float,
}

impl std::fmt::Display for ExprSort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprSort::Bool => f.write_str("Bool"),
            ExprSort::Int => f.write_str("Int"),
            ExprSort::Seq => f.write_str("Seq"),
            ExprSort::Unit => f.write_str("()"),
            ExprSort::FMap => f.write_str("FMap"),
            ExprSort::Datatype(id) => write!(f, "Datatype({})", resolve_sort_name(*id)),
            ExprSort::Tuple(n) => write!(f, "Tuple({n})"),
            ExprSort::Ref(inner) => write!(f, "&{inner}"),
            ExprSort::MutRef(inner) => write!(f, "&mut {inner}"),
            ExprSort::TypeParam(id) => write!(f, "TypeParam({})", resolve_sort_name(*id)),
            ExprSort::Float => f.write_str("Float"),
        }
    }
}

/// A pure (heap-independent) expression
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PureExpr {
    /// Boolean literal
    Bool(bool),
    /// Integer literal
    Int(i64),
    /// Float literal, stored as bit pattern. Maps to SMT Real. (#1802)
    Float(FloatBits),
    /// Variable reference, with optional sort annotation
    Var(String, Option<ExprSort>),
    /// Binary operation
    BinOp(Arc<PureExpr>, BinOp, Arc<PureExpr>),
    /// Unary operation
    UnOp(UnOp, Arc<PureExpr>),
    /// Conditional expression: if cond then t else e
    Ite(Arc<PureExpr>, Arc<PureExpr>, Arc<PureExpr>),
    /// Old expression - captures value at function entry (for postconditions)
    Old(Arc<PureExpr>),
    /// Dereference current value: `*v` (Creusot-style)
    ///
    /// In `RustHorn` encoding, this corresponds to `{var}_current` - the value
    /// of the borrow at creation time.
    Deref(Arc<PureExpr>),
    /// Final/prophecy value: `^v` (Creusot-style)
    ///
    /// In `RustHorn` encoding, this corresponds to `{var}_final` - the value
    /// the borrow will have when it ends.
    Final(Arc<PureExpr>),
    /// View operator: `expr@` (Creusot-style)
    ///
    /// Converts runtime types to their logical views for specification:
    /// - `Vec<T>` → `Seq<T>` (logical sequence)
    /// - `Option<T>` → `Option<T::View>` (logical option)
    /// - `String` → `Seq<char>` (logical character sequence)
    ///
    /// Enables reasoning about collections without heap modeling.
    View(Arc<PureExpr>),
    /// Method call on logical view: `expr.method(args...)`
    ///
    /// Specification-only methods on logical types:
    /// - `seq.len()` → sequence length
    /// - `seq.index_logic(i)` → element at index
    /// - `seq.push_back(v)` → new sequence with element appended
    MethodCall {
        receiver: Arc<PureExpr>,
        method: String,
        args: Vec<PureExpr>,
    },
    /// Universal quantifier: `forall<x: Type> body`
    ///
    /// Expresses that the body holds for all values of the bound variable.
    /// `var_sort` records an optional explicit sort annotation for the binder.
    ///
    /// # Triggers
    ///
    /// Optional trigger patterns control SMT instantiation. Each trigger is a
    /// list of expressions that must all match for the quantifier to be instantiated.
    /// Multiple triggers provide alternative instantiation patterns.
    ///
    /// In SMT-LIB2, triggers are encoded as:
    /// ```text
    /// (forall ((x Int)) (! body :pattern ((f x) (g x)) :pattern ((h x))))
    /// ```
    Forall {
        /// Bound variable name
        var: String,
        /// Optional sort for the bound variable
        var_sort: Option<ExprSort>,
        /// Quantifier body
        body: Arc<PureExpr>,
        /// Optional trigger patterns for SMT instantiation control
        /// Each inner Vec is a multi-trigger (all must match)
        triggers: Vec<Vec<PureExpr>>,
    },
    /// Existential quantifier: `exists<x: Type> body`
    ///
    /// Expresses that there exists some value of the bound variable for which
    /// the body holds. `var_sort` records an optional explicit sort annotation
    /// for the binder.
    ///
    /// # Triggers
    ///
    /// Same as `Forall` - controls SMT instantiation.
    Exists {
        /// Bound variable name
        var: String,
        /// Optional sort for the bound variable
        var_sort: Option<ExprSort>,
        /// Quantifier body
        body: Arc<PureExpr>,
        /// Optional trigger patterns for SMT instantiation control
        triggers: Vec<Vec<PureExpr>>,
    },
    /// Match expression: `match scrutinee { pattern => expr, ... }`
    ///
    /// Used for pattern matching in specifications, e.g.:
    /// ```text
    /// match *self {
    ///     Some(v) => result == v,
    ///     None => result == default,
    /// }
    /// ```
    Match {
        /// The expression being matched
        scrutinee: Arc<PureExpr>,
        /// List of match arms
        arms: Vec<MatchArm>,
    },
    /// Logic function call: `logic_fn(args...)`
    ///
    /// Calls to user-defined `#[logic]` functions that exist only for
    /// specification. These are encoded as uninterpreted SMT functions
    /// with defining axioms.
    ///
    /// Example:
    /// ```text
    /// #[logic]
    /// fn max(a: Int, b: Int) -> Int {
    ///     if a >= b { a } else { b }
    /// }
    ///
    /// // In a contract:
    /// #[ensures(result@ == max(x@, y@))]
    /// ```
    LogicFnCall {
        /// Qualified name of the logic function (e.g., "`crate::specs::max`")
        name: String,
        /// Arguments to the function
        args: Vec<PureExpr>,
    },
    /// Let binding: `let var = value; body`
    ///
    /// Introduces a local variable binding in a logic function body.
    /// Semantically equivalent to `body[var := value]` (substitution).
    ///
    /// In SMT-LIB2, encoded as `(let ((var value)) body)`.
    Let {
        /// Bound variable name
        var: String,
        /// Value bound to the variable
        value: Arc<PureExpr>,
        /// Body expression where the variable is in scope
        body: Arc<PureExpr>,
    },
    /// Scoped call assumption: assume `assumption` holds within `body`.
    ///
    /// Used to scope call-site postconditions to the branch they were
    /// created in during MIR extraction. Without scoping, assumptions
    /// from branch-local calls leak globally. (#815)
    ///
    /// SMT encoding: `assumption => encode(body)`
    LetAssume {
        /// Call postcondition to assume in scope
        assumption: Arc<PureExpr>,
        /// Continuation body where the assumption holds
        body: Arc<PureExpr>,
    },
    /// Scoped call obligation: `obligation` must be proved alongside `body`.
    ///
    /// Used to enforce call-site preconditions in the `proof_assert` path.
    /// Without this, call postconditions are assumed without checking that
    /// the caller satisfies the callee's preconditions. (#815)
    ///
    /// SMT encoding: `encode(obligation) AND encode(body)`
    LetObligation {
        /// Call precondition that must be proved
        obligation: Arc<PureExpr>,
        /// Continuation body
        body: Arc<PureExpr>,
    },
    /// Closure expression: `|param1: Type1, param2: Type2| body`
    ///
    /// Parsed from pearlite/logic function bodies where closures appear
    /// as anonymous functions (e.g., `let f = |x: Int| x + 1`).
    ///
    /// Closure parameters carry optional sort annotations from type
    /// annotations in the source.
    ///
    /// Encoding: closures in logic context are treated as named lambdas
    /// when let-bound. The encoder currently returns `unsupported` for
    /// standalone closures. (#985)
    Closure {
        /// Parameter names with optional sort annotations
        params: Vec<(String, Option<ExprSort>)>,
        /// Closure body expression
        body: Arc<PureExpr>,
    },
}

/// A match arm: `pattern => expression`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MatchArm {
    /// The pattern to match against
    pub pattern: Pattern,
    /// The expression to evaluate if pattern matches
    pub body: PureExpr,
}

/// A pattern in a match expression
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pattern {
    /// Wildcard pattern `_`
    Wildcard,
    /// Variable binding: `x` or `Some(x)`
    Binding(String),
    /// Literal pattern: `0`, `true`
    Literal(PureExpr),
    /// Constructor pattern: `Some(inner)`, `None`
    Constructor {
        name: String,
        inner: Option<Box<Pattern>>,
    },
    /// Alias pattern: `name @ Pattern`
    Alias {
        alias: String,
        pattern: Box<Pattern>,
    },
    /// Tuple pattern: `(a, b)`, `(Some(x), None)`
    Tuple(Vec<Pattern>),
}

impl PureExpr {
    /// O(1) pointer-based equality check for rewrite short-circuiting.
    ///
    /// Returns `true` when two `PureExpr` values have the same variant and all
    /// `Arc` children are pointer-equal (`Arc::ptr_eq`). Leaf variants
    /// (`Bool`, `Int`, `Float`, `Var`) fall back to value equality, which is
    /// still O(1) per node.
    ///
    /// This is **sound as a fast path** for `reuse_arc` / `reuse_node`:
    /// `ptr_eq_shallow(a, b) == true` implies `a == b` (because identical Arc
    /// pointers reference identical data). The converse does not hold — two
    /// structurally equal trees with distinct allocations will return `false`,
    /// which merely skips the optimisation (correctness preserved, just slower).
    ///
    /// # Performance
    ///
    /// Eliminates the O(T) structural comparison inside `reuse_arc`/`reuse_node`
    /// for the common no-change rewrite path, reducing left-recursive chain
    /// rewrites from O(T**2) to O(T). (#2647)
    #[must_use]
    #[allow(clippy::too_many_lines)] // Exhaustive match over all PureExpr variants is inherently cohesive
    pub fn ptr_eq_shallow(&self, other: &Self) -> bool {
        match (self, other) {
            (PureExpr::Bool(a), PureExpr::Bool(b)) => a == b,
            (PureExpr::Int(a), PureExpr::Int(b)) => a == b,
            (PureExpr::Float(a), PureExpr::Float(b)) => a == b,
            (PureExpr::Var(a, sa), PureExpr::Var(b, sb)) => a == b && sa == sb,
            (PureExpr::BinOp(l1, op1, r1), PureExpr::BinOp(l2, op2, r2)) => {
                op1 == op2 && Arc::ptr_eq(l1, l2) && Arc::ptr_eq(r1, r2)
            }
            (PureExpr::UnOp(op1, a), PureExpr::UnOp(op2, b)) => op1 == op2 && Arc::ptr_eq(a, b),
            (PureExpr::Ite(c1, t1, e1), PureExpr::Ite(c2, t2, e2)) => {
                Arc::ptr_eq(c1, c2) && Arc::ptr_eq(t1, t2) && Arc::ptr_eq(e1, e2)
            }
            (PureExpr::Old(a), PureExpr::Old(b))
            | (PureExpr::Deref(a), PureExpr::Deref(b))
            | (PureExpr::Final(a), PureExpr::Final(b))
            | (PureExpr::View(a), PureExpr::View(b)) => Arc::ptr_eq(a, b),
            (
                PureExpr::MethodCall {
                    receiver: r1,
                    method: m1,
                    args: a1,
                },
                PureExpr::MethodCall {
                    receiver: r2,
                    method: m2,
                    args: a2,
                },
            ) => {
                Arc::ptr_eq(r1, r2)
                    && m1 == m2
                    && a1.len() == a2.len()
                    && a1.iter().zip(a2.iter()).all(|(x, y)| x.ptr_eq_shallow(y))
            }
            (
                PureExpr::Forall {
                    var: v1,
                    var_sort: s1,
                    body: b1,
                    triggers: t1,
                },
                PureExpr::Forall {
                    var: v2,
                    var_sort: s2,
                    body: b2,
                    triggers: t2,
                },
            )
            | (
                PureExpr::Exists {
                    var: v1,
                    var_sort: s1,
                    body: b1,
                    triggers: t1,
                },
                PureExpr::Exists {
                    var: v2,
                    var_sort: s2,
                    body: b2,
                    triggers: t2,
                },
            ) => {
                v1 == v2
                    && s1 == s2
                    && Arc::ptr_eq(b1, b2)
                    && t1.len() == t2.len()
                    && t1.iter().zip(t2.iter()).all(|(trig1, trig2)| {
                        trig1.len() == trig2.len()
                            && trig1
                                .iter()
                                .zip(trig2.iter())
                                .all(|(x, y)| x.ptr_eq_shallow(y))
                    })
            }
            (
                PureExpr::Match {
                    scrutinee: s1,
                    arms: a1,
                },
                PureExpr::Match {
                    scrutinee: s2,
                    arms: a2,
                },
            ) => {
                Arc::ptr_eq(s1, s2)
                    && a1.len() == a2.len()
                    && a1.iter().zip(a2.iter()).all(|(arm1, arm2)| {
                        arm1.pattern == arm2.pattern && arm1.body.ptr_eq_shallow(&arm2.body)
                    })
            }
            (
                PureExpr::LogicFnCall { name: n1, args: a1 },
                PureExpr::LogicFnCall { name: n2, args: a2 },
            ) => {
                n1 == n2
                    && a1.len() == a2.len()
                    && a1.iter().zip(a2.iter()).all(|(x, y)| x.ptr_eq_shallow(y))
            }
            (
                PureExpr::Let {
                    var: v1,
                    value: val1,
                    body: b1,
                },
                PureExpr::Let {
                    var: v2,
                    value: val2,
                    body: b2,
                },
            ) => v1 == v2 && Arc::ptr_eq(val1, val2) && Arc::ptr_eq(b1, b2),
            (
                PureExpr::LetAssume {
                    assumption: a1,
                    body: b1,
                },
                PureExpr::LetAssume {
                    assumption: a2,
                    body: b2,
                },
            ) => Arc::ptr_eq(a1, a2) && Arc::ptr_eq(b1, b2),
            (
                PureExpr::LetObligation {
                    obligation: o1,
                    body: b1,
                },
                PureExpr::LetObligation {
                    obligation: o2,
                    body: b2,
                },
            ) => Arc::ptr_eq(o1, o2) && Arc::ptr_eq(b1, b2),
            (
                PureExpr::Closure {
                    params: p1,
                    body: b1,
                },
                PureExpr::Closure {
                    params: p2,
                    body: b2,
                },
            ) => p1 == p2 && Arc::ptr_eq(b1, b2),
            _ => false,
        }
    }
}

/// Reuse the original `Arc` when the rewritten child is unchanged.
///
/// Uses `ptr_eq_shallow` as an O(1) check. The rewrite framework guarantees
/// that unchanged subtrees preserve `Arc` pointer identity through
/// `Arc::clone`, so `ptr_eq_shallow` is sufficient — no deep structural
/// comparison is needed. Removing the O(subtree_size) fallback eliminates
/// the O(T**2) behaviour on left-recursive expression chains. (#2647)
pub fn reuse_arc(original: &Arc<PureExpr>, rewritten: PureExpr) -> Arc<PureExpr> {
    if rewritten.ptr_eq_shallow(original.as_ref()) {
        Arc::clone(original)
    } else {
        Arc::new(rewritten)
    }
}

/// Reuse the original node when the rebuilt expression is unchanged.
///
/// Uses `ptr_eq_shallow` as an O(1) check. The rewrite framework guarantees
/// that unchanged subtrees preserve `Arc` pointer identity, so no deep
/// structural comparison is needed. (#2647)
pub fn reuse_node(original: &PureExpr, rebuilt: PureExpr) -> PureExpr {
    if rebuilt.ptr_eq_shallow(original) {
        original.clone()
    } else {
        rebuilt
    }
}
