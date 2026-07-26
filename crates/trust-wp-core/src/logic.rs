// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic function definitions for trust-wp.
//!
//! This module provides types for representing user-defined `#[logic]` functions
//! that exist only for specification purposes.

use std::collections::HashMap;

use num_bigint::BigInt;

use crate::formula::{ExprSort, PureExpr};

/// Sort hint for a logic function parameter.
///
/// Used to override the default `Int` sort for parameters that are Bool, Seq,
/// or Datatype.  `None` in `LogicFnDef::param_sorts` means "use default (Int)".
///
/// Relationship to other sort enums:
/// - `ParamSortHint` only encodes non-default overrides (`Bool`/`Seq`/`Datatype`)
/// - `ExprSort` includes the default (`Int`) and `Unit`
/// - `smt::VarSort` includes the SMT variable sorts (`Int`/`Bool`/`Seq`)
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParamSortHint {
    /// Parameter has Bool sort (e.g., `bool` in Rust)
    Bool,
    /// Parameter has Seq sort (e.g., `Seq<T>` model types)
    Seq,
    /// Parameter has Datatype sort (e.g., `OptionInt`, `ResultIntInt`).
    ///
    /// The string carries the datatype name used to construct
    /// `ExprSort::Datatype(intern_sort_name(name))` and ultimately
    /// `Sort::Uninterpreted(name)` in the ay encoding. (#1943)
    Datatype(String),
}

impl ParamSortHint {
    /// Convert an optional hint into a concrete expression sort.
    ///
    /// `None` is treated as `ExprSort::Int` (the default sort).
    /// `Datatype(name)` is interned via [`crate::formula::intern_sort_name`].
    #[must_use]
    pub fn resolve_expr_sort(hint: Option<Self>) -> ExprSort {
        match hint {
            Some(ParamSortHint::Bool) => ExprSort::Bool,
            Some(ParamSortHint::Seq) => ExprSort::Seq,
            Some(ParamSortHint::Datatype(name)) => {
                ExprSort::Datatype(crate::formula::intern_sort_name(&name))
            }
            None => ExprSort::Int,
        }
    }
}

impl From<ParamSortHint> for ExprSort {
    fn from(value: ParamSortHint) -> Self {
        match value {
            ParamSortHint::Bool => ExprSort::Bool,
            ParamSortHint::Seq => ExprSort::Seq,
            ParamSortHint::Datatype(name) => {
                ExprSort::Datatype(crate::formula::intern_sort_name(&name))
            }
        }
    }
}

/// Range constraint for an ADT constructor field.
///
/// Carries the information needed to inject non-negativity or bounded-range
/// axioms for ADT fields that correspond to unsigned or signed integer types
/// in Rust. Without these constraints, all ADT fields are unbounded
/// `Sort::Int` in SMT, allowing the solver to assign negative values to u32
/// fields — producing spurious counterexamples. (#2097, RC1)
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldRangeKind {
    /// Unsigned integer: `field >= 0 && field <= 2^bits - 1`
    Unsigned(u32),
    /// Signed integer: `field >= -2^(bits-1) && field <= 2^(bits-1) - 1`
    Signed(u32),
}

/// Per-constructor field range hints for one ADT.
///
/// Structure: `[(ctor_name, [(field_index, range)])]`
pub type AdtCtorFieldRanges = Vec<(String, Vec<(usize, FieldRangeKind)>)>;

/// Per-ADT field range hints, mapping constructor names to per-field range info.
///
/// Structure: `adt_name -> [(ctor_name, [(field_index, range)])]`
///
/// The driver populates this from `TyCtxt` ADT definitions. The encoder uses
/// it to inject quantified range axioms after datatype declaration.
pub type AdtFieldRanges = HashMap<String, AdtCtorFieldRanges>;

/// Rust ADT category for native datatype declarations.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdtKind {
    Struct,
    Enum,
}

/// Rust-level field metadata for a datatype constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdtFieldDecl {
    pub name: String,
    pub sort: ExprSort,
}

impl AdtFieldDecl {
    #[must_use]
    pub fn new(name: String, sort: ExprSort) -> Self {
        Self { name, sort }
    }
}

/// Rust-level constructor metadata for a datatype declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdtConstructorDecl {
    pub rust_name: String,
    pub smt_name: String,
    pub fields: Vec<AdtFieldDecl>,
    /// Actual discriminant value from rustc, if known.
    ///
    /// For standard enums this equals the variant index (0, 1, 2, ...),
    /// but for `#[repr]` enums with explicit discriminant assignments
    /// (e.g., `Active = 10`) the value differs from the index. Stored as
    /// `BigInt` so we preserve signed explicit discriminants and large
    /// `#[repr(u128)]` values exactly. When `None`, the encoder falls back to
    /// using the variant index. (#2631)
    pub discriminant_value: Option<BigInt>,
}

impl AdtConstructorDecl {
    #[must_use]
    pub fn new(rust_name: String, smt_name: String, fields: Vec<AdtFieldDecl>) -> Self {
        Self {
            rust_name,
            smt_name,
            fields,
            discriminant_value: None,
        }
    }

    /// Set the discriminant value from rustc's `adt_def.discriminants(tcx)`.
    #[must_use]
    pub fn with_discriminant_value(mut self, value: impl Into<BigInt>) -> Self {
        self.discriminant_value = Some(value.into());
        self
    }
}

/// Rust-level ADT declaration metadata collected from `TyCtxt`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdtDecl {
    pub rust_path: String,
    pub adt_name: String,
    pub kind: AdtKind,
    pub constructors: Vec<AdtConstructorDecl>,
}

impl AdtDecl {
    #[must_use]
    pub fn new(
        rust_path: String,
        adt_name: String,
        kind: AdtKind,
        constructors: Vec<AdtConstructorDecl>,
    ) -> Self {
        Self {
            rust_path,
            adt_name,
            kind,
            constructors,
        }
    }
}

/// Per-query rustc-backed datatype declarations keyed by simple ADT name.
pub type AdtDecls = HashMap<String, AdtDecl>;

/// Openness mode for `#[logic]` / `#[predicate]` functions.
///
/// Controls whether the function body is visible to callers during verification.
/// Mirrors the proc-macro-side `LogicMode` in `trust-wp-macros`.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicMode {
    /// Default: body is opaque to callers (only contract is visible)
    Default,
    /// `#[logic(open)]`: body is visible to all callers
    Open,
    /// `#[logic(open(self))]`: body visible within same module/type
    OpenSelf,
    /// `#[logic(prophetic)]`: may reference final values (`^v`)
    Prophetic,
}

impl LogicMode {
    /// Parse a `LogicMode` from a doc marker suffix string.
    ///
    /// The marker format is `trust-wp:logic:{suffix}` where suffix is:
    /// - `""` → Default
    /// - `"open:"` → Open
    /// - `"open_self:"` → `OpenSelf`
    /// - `"prophetic:"` → Prophetic
    /// - `"predicate"` → Default (predicate indicator, not a mode)
    /// - `"open:predicate"` → Open (predicate indicator after mode)
    #[must_use]
    pub fn from_marker_suffix(suffix: &str) -> Self {
        Self::try_from_marker_suffix(suffix).unwrap_or(LogicMode::Default)
    }

    /// Parse a logic mode from a marker suffix, returning `None` for unknown modes.
    #[must_use]
    pub fn try_from_marker_suffix(suffix: &str) -> Option<Self> {
        // Strip trailing "predicate" — it's not a mode, just a type indicator
        let mode_part = suffix
            .strip_suffix("predicate")
            .unwrap_or(suffix)
            .trim_end_matches(':');

        match mode_part {
            "" => Some(LogicMode::Default),
            "open" => Some(LogicMode::Open),
            "open_self" => Some(LogicMode::OpenSelf),
            "prophetic" => Some(LogicMode::Prophetic),
            _ => None,
        }
    }
}

/// A logic function definition.
///
/// Logic functions are pure specification-only functions that:
/// - Exist only for verification (erased at runtime)
/// - Are encoded as uninterpreted SMT functions with defining axioms
/// - Can be called from contracts and ghost blocks
///
/// # Example
///
/// ```text
/// #[logic]
/// fn max(a: Int, b: Int) -> Int {
///     if a >= b { a } else { b }
/// }
/// ```
///
/// Encoded as:
/// ```text
/// (declare-fun logic_max (Int Int) Int)
/// (assert (forall ((a Int) (b Int))
///   (= (logic_max a b) (ite (>= a b) a b))))
/// ```
///
/// If the logic function has preconditions, they guard the axiom:
/// ```text
/// (assert (forall ((a Int) (b Int))
///   (=> (and <requires...>)
///       (= (logic_max a b) (ite (>= a b) a b)))))
/// ```
#[allow(clippy::struct_excessive_bools)]
#[derive(Debug, Clone)]
pub struct LogicFnDef {
    /// Function name (without module path)
    name: String,
    /// Full path for qualified lookups (e.g., "`crate::specs::max`")
    full_path: String,
    /// Parameter names
    params: Vec<String>,
    /// Optional sort hints for parameters (parallel to `params`).
    ///
    /// `None` means default (Int). Non-default sorts include `ExprSort::Bool`,
    /// `ExprSort::Seq`, and `ExprSort::Datatype(id)` for ADT-sorted parameters.
    /// Empty vec is treated as "all default" for backward compatibility.
    param_sorts: Vec<Option<ExprSort>>,
    /// Optional sort hint for the return type.
    ///
    /// `None` means default (Int). Non-default sorts include `ExprSort::Bool`,
    /// `ExprSort::Seq`, and `ExprSort::Datatype(id)` for ADT return types.
    return_sort: Option<ExprSort>,
    /// Preconditions guarding the function body
    requires: Vec<PureExpr>,
    /// Postconditions to verify about the function body.
    ///
    /// When non-empty, the logic function's body is verified against these
    /// postconditions (matching Creusot behavior for `#[logic]` + `#[ensures]`).
    /// Logic functions without `#[ensures]` remain axiomatized-only.
    ensures: Vec<PureExpr>,
    /// Function body as a pure expression
    body: PureExpr,
    /// Whether this function is recursive
    is_recursive: bool,
    /// Decreasing `#[variant(...)]` measure expressions, parsed (parallel to the
    /// source order). Used to gate sound recursive-induction-hypothesis injection
    /// when verifying a recursive logic function's own postcondition: the IH for
    /// a self-recursive call is admitted only under a guard that the variant
    /// strictly decreases into the non-negative integers (well-foundedness).
    /// Empty means no `#[variant]` was declared (then NO IH is injected). (#ri)
    variants: Vec<PureExpr>,
    /// Whether this function is opaque to callers (no defining axiom emitted).
    is_opaque: bool,
    /// Whether this function is `#[trusted]` — postconditions assumed, not verified.
    ///
    /// Trusted logic functions have their ensures clauses treated as axioms
    /// rather than verification targets. The logic function postcondition
    /// verification pass skips them entirely. (#2700)
    is_trusted: bool,
    /// Whether this function was marked as a Creusot compatibility law.
    ///
    /// Law postconditions are exposed as axioms to callers. The driver may
    /// choose a different proof policy for laws than for ordinary logic
    /// functions with postconditions.
    is_law: bool,
    /// Openness mode from the `#[logic(...)]` attribute argument.
    mode: LogicMode,
}

impl LogicFnDef {
    /// Create a new non-recursive logic function definition without preconditions.
    #[must_use]
    pub fn new(name: String, full_path: String, params: Vec<String>, body: PureExpr) -> Self {
        Self {
            name,
            full_path,
            param_sorts: Vec::new(),
            return_sort: None,
            params,
            requires: Vec::new(),
            ensures: Vec::new(),
            body,
            is_recursive: false,
            variants: Vec::new(),
            is_opaque: false,
            is_trusted: false,
            is_law: false,
            mode: LogicMode::Default,
        }
    }

    /// Create a new non-recursive logic function definition with preconditions.
    #[must_use]
    pub fn new_with_requires(
        name: String,
        full_path: String,
        params: Vec<String>,
        requires: Vec<PureExpr>,
        body: PureExpr,
    ) -> Self {
        Self {
            name,
            full_path,
            param_sorts: Vec::new(),
            return_sort: None,
            params,
            requires,
            ensures: Vec::new(),
            body,
            is_recursive: false,
            variants: Vec::new(),
            is_opaque: false,
            is_trusted: false,
            is_law: false,
            mode: LogicMode::Default,
        }
    }

    /// Set the parsed decreasing `#[variant(...)]` measure expressions.
    #[must_use]
    pub fn with_variants(mut self, variants: Vec<PureExpr>) -> Self {
        self.variants = variants;
        self
    }

    /// Set sort hints for parameters.
    #[must_use]
    pub fn with_param_sorts(mut self, param_sorts: Vec<Option<ExprSort>>) -> Self {
        self.param_sorts = param_sorts;
        self
    }

    /// Set the sort hint for the return type.
    #[must_use]
    pub fn with_return_sort(mut self, return_sort: Option<ExprSort>) -> Self {
        self.return_sort = return_sort;
        self
    }

    /// Mark whether this logic function should be treated as opaque.
    #[must_use]
    pub fn with_opaque(mut self, is_opaque: bool) -> Self {
        self.is_opaque = is_opaque;
        self
    }

    /// Mark whether this logic function is `#[trusted]`.
    ///
    /// Trusted logic functions have their ensures clauses treated as axioms
    /// rather than verification targets. (#2700)
    #[must_use]
    pub fn with_trusted(mut self, is_trusted: bool) -> Self {
        self.is_trusted = is_trusted;
        self
    }

    /// Mark whether this logic function is a Creusot compatibility law.
    #[must_use]
    pub fn with_law(mut self, is_law: bool) -> Self {
        self.is_law = is_law;
        self
    }

    /// Set the logic mode from the attribute argument.
    #[must_use]
    pub fn with_mode(mut self, mode: LogicMode) -> Self {
        self.mode = mode;
        self
    }

    /// Auto-detect whether this logic function is recursive by checking if
    /// its body contains a call to its own name. Sets `is_recursive` accordingly.
    #[must_use]
    pub fn detect_recursion(mut self) -> Self {
        self.is_recursive = expr_contains_fn_call(&self.body, &self.name);
        self
    }

    /// Re-detect recursion counting ONLY resolved `LogicFnCall` nodes,
    /// ignoring `MethodCall` name coincidences.
    ///
    /// `detect_recursion` treats any `MethodCall` whose method name equals
    /// the function name as a self-call. That is correct BEFORE method-call
    /// routing, but a user trait impl of a builtin-named logic method (e.g.
    /// `impl IndexLogic<usize> for Memory { #[logic] fn index_logic(self, i)
    /// { self.0[i] } }`) keeps builtin method-call syntax for the *builtin*
    /// occurrences in its body (`self.0[i]` parses to an `index_logic`
    /// MethodCall on the Vec field), which falsely flags the function as
    /// recursive and suppresses its global defining axiom
    /// (list_reversal_lasso).
    ///
    /// Call this only AFTER the driver has routed every genuine
    /// self-dispatch occurrence to `LogicFnCall` (shadowed-builtin rewrite):
    /// remaining same-named `MethodCall`s are builtin-receiver calls that
    /// encode to builtin/opaque symbols, never to this function's own
    /// symbol, so a defining equation over them is not self-referential.
    pub fn redetect_recursion_logic_calls_only(&mut self) {
        self.is_recursive = expr_contains_logic_fn_call_only(&self.body, &self.name);
    }

    // --- Accessors (#906) ---

    /// Returns the function name (without module path).
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the full path for qualified lookups.
    #[must_use]
    pub fn full_path(&self) -> &str {
        &self.full_path
    }

    /// Returns the parameter names.
    #[must_use]
    pub fn params(&self) -> &[String] {
        &self.params
    }

    /// Returns the sort hints for parameters.
    #[must_use]
    pub fn param_sorts(&self) -> &[Option<ExprSort>] {
        &self.param_sorts
    }

    /// Returns the sort hint for the return type.
    #[must_use]
    pub fn return_sort(&self) -> Option<ExprSort> {
        self.return_sort.clone()
    }

    /// Returns the precondition expressions.
    #[must_use]
    pub fn requires(&self) -> &[PureExpr] {
        &self.requires
    }

    /// Returns the postcondition expressions.
    #[must_use]
    pub fn ensures(&self) -> &[PureExpr] {
        &self.ensures
    }

    /// Returns a reference to the function body expression.
    #[must_use]
    pub fn body(&self) -> &PureExpr {
        &self.body
    }

    /// Returns whether this function is recursive.
    #[must_use]
    pub fn is_recursive(&self) -> bool {
        self.is_recursive
    }

    /// Returns the parsed decreasing `#[variant(...)]` measure expressions.
    #[must_use]
    pub fn variants(&self) -> &[PureExpr] {
        &self.variants
    }

    /// Returns whether this function is opaque to callers.
    #[must_use]
    pub fn is_opaque(&self) -> bool {
        self.is_opaque
    }

    /// Returns whether this function is `#[trusted]`.
    ///
    /// Trusted logic functions have their ensures clauses treated as axioms
    /// rather than verification targets. (#2700)
    #[must_use]
    pub fn is_trusted(&self) -> bool {
        self.is_trusted
    }

    /// Returns whether this function was marked as a Creusot compatibility law.
    #[must_use]
    pub fn is_law(&self) -> bool {
        self.is_law
    }

    /// Returns the openness mode.
    #[must_use]
    pub fn mode(&self) -> LogicMode {
        self.mode
    }

    // --- Mutable setters (#906) ---

    /// Replace the function body.
    pub fn set_body(&mut self, body: PureExpr) {
        self.body = body;
    }

    /// Replace the preconditions.
    pub fn set_requires(&mut self, requires: Vec<PureExpr>) {
        self.requires = requires;
    }

    /// Append preconditions.
    pub fn extend_requires(&mut self, extra: impl IntoIterator<Item = PureExpr>) {
        self.requires.extend(extra);
    }

    /// Replace the postconditions.
    pub fn set_ensures(&mut self, ensures: Vec<PureExpr>) {
        self.ensures = ensures;
    }

    /// Replace the mode.
    pub fn set_mode(&mut self, mode: LogicMode) {
        self.mode = mode;
    }

    /// Mutable access to the preconditions.
    pub fn requires_mut(&mut self) -> &mut Vec<PureExpr> {
        &mut self.requires
    }

    /// Mutable access to the postconditions.
    pub fn ensures_mut(&mut self) -> &mut Vec<PureExpr> {
        &mut self.ensures
    }

    /// Set the recursive flag directly.
    pub fn set_is_recursive(&mut self, is_recursive: bool) {
        self.is_recursive = is_recursive;
    }

    /// Set the opaque flag directly.
    pub fn set_is_opaque(&mut self, is_opaque: bool) {
        self.is_opaque = is_opaque;
    }

    /// Set the param sorts directly.
    pub fn set_param_sorts(&mut self, param_sorts: Vec<Option<ExprSort>>) {
        self.param_sorts = param_sorts;
    }

    /// Set the return sort directly.
    pub fn set_return_sort(&mut self, return_sort: Option<ExprSort>) {
        self.return_sort = return_sort;
    }

    /// Mutable access to the function body.
    pub fn body_mut(&mut self) -> &mut PureExpr {
        &mut self.body
    }

    /// Mutable access to the parameter names.
    pub fn params_mut(&mut self) -> &mut Vec<String> {
        &mut self.params
    }

    /// Take ownership of the preconditions, leaving an empty vec.
    #[must_use]
    pub fn take_requires(&mut self) -> Vec<PureExpr> {
        std::mem::take(&mut self.requires)
    }

    /// Take ownership of the postconditions, leaving an empty vec.
    #[must_use]
    pub fn take_ensures(&mut self) -> Vec<PureExpr> {
        std::mem::take(&mut self.ensures)
    }

    /// Take ownership of the body, replacing with a default.
    #[must_use]
    pub fn take_body(&mut self) -> PureExpr {
        std::mem::replace(&mut self.body, PureExpr::Bool(false))
    }
}

/// Check whether a `PureExpr` tree contains a `LogicFnCall` or `MethodCall`
/// with the given name. Method-syntax self-calls (e.g., `self.lemma()`) must
/// also be detected as recursive so that `detect_recursion()` correctly sets
/// `is_recursive = true` for logic functions defined on impl blocks. (#2548)
fn expr_contains_fn_call(expr: &PureExpr, fn_name: &str) -> bool {
    expr_contains_fn_call_impl(expr, fn_name, true)
}

/// Like [`expr_contains_fn_call`], but a `MethodCall` name match does NOT
/// count as a call — only resolved `LogicFnCall` nodes do. Used by
/// [`LogicFnDef::redetect_recursion_logic_calls_only`].
fn expr_contains_logic_fn_call_only(expr: &PureExpr, fn_name: &str) -> bool {
    expr_contains_fn_call_impl(expr, fn_name, false)
}

fn expr_contains_fn_call_impl(expr: &PureExpr, fn_name: &str, match_method_calls: bool) -> bool {
    let rec = |ex: &PureExpr| expr_contains_fn_call_impl(ex, fn_name, match_method_calls);
    match expr {
        PureExpr::LogicFnCall { name, args } => {
            logic_fn_name_matches(name, fn_name) || args.iter().any(rec)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => (match_method_calls && method == fn_name) || rec(receiver) || args.iter().any(rec),
        PureExpr::BinOp(lhs, _, rhs) => rec(lhs) || rec(rhs),
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => rec(inner),
        PureExpr::Ite(cond, then, els) => rec(cond) || rec(then) || rec(els),
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            rec(body) || triggers.iter().any(|trig| trig.iter().any(rec))
        }
        PureExpr::Closure { body, .. } => rec(body),
        PureExpr::Let { value, body, .. }
        | PureExpr::LetAssume {
            assumption: value,
            body,
        }
        | PureExpr::LetObligation {
            obligation: value,
            body,
        } => rec(value) || rec(body),
        PureExpr::Match { scrutinee, arms } => {
            rec(scrutinee) || arms.iter().any(|arm| rec(&arm.body))
        }
        _ => false,
    }
}

fn logic_fn_name_matches(call_name: &str, fn_name: &str) -> bool {
    call_name == fn_name
        || call_name
            .strip_prefix("Self::")
            .is_some_and(|method| method == fn_name)
}

/// Definition of a type invariant body for SMT axiom registration (#359).
///
/// Created by the driver from `impl Invariant for T { fn invariant(&self) -> bool { body } }`
/// blocks. The encoder uses this to assert a type-qualified axiom:
/// ```text
/// (assert (forall ((self : sort)) (= (method___trust_wp_invariant_<Type>_1_<tag> self) body)))
/// ```
/// Each type gets a unique SMT symbol to prevent collisions when multiple types
/// share the same parameter sort (#666).
#[derive(Debug, Clone)]
pub struct TypeInvariantDef {
    /// The type name this invariant applies to (e.g., "Counter", "`NonZero`").
    /// Used for per-type matching during injection (#659).
    type_name: String,
    /// Name of the self parameter in the invariant body (usually "self")
    self_param: String,
    /// Sort hint for the self parameter (None = default Int)
    param_sort: Option<ExprSort>,
    /// The invariant body as a pure expression
    body: PureExpr,
    /// Whether this is a newtype (single-field struct). When true, field-0
    /// access is identity: `self.0 == self` in the logical domain. Used to
    /// simplify body expressions and user contracts for consistent SMT
    /// encoding. (#359)
    is_newtype: bool,
    /// For container types (e.g., Vec), the element type's invariant method name.
    /// When set, the encoder generates a bridge axiom connecting the container
    /// invariant to element invariants via `seq_index_logic`:
    ///   `inv_container(x) => forall i. 0 <= i < len(view(x)) => inv_element(index(view(x), i))`
    /// This enables proof assertions like `x[0].a + x[0].b == 10` when
    /// `x: Vec<SumTo10>` and `SumTo10` has `impl Invariant`. (#869)
    element_invariant_method: Option<String>,
}

impl TypeInvariantDef {
    /// Create a new type invariant definition with default optional metadata.
    #[must_use]
    pub fn new(type_name: String, self_param: String, body: PureExpr) -> Self {
        Self {
            type_name,
            self_param,
            param_sort: None,
            body,
            is_newtype: false,
            element_invariant_method: None,
        }
    }

    /// Set the sort annotation for the self parameter.
    #[must_use]
    pub fn with_param_sort(mut self, sort: Option<ExprSort>) -> Self {
        self.param_sort = sort;
        self
    }

    /// Mark whether this invariant belongs to a logical newtype.
    #[must_use]
    pub fn with_newtype(mut self, is_newtype: bool) -> Self {
        self.is_newtype = is_newtype;
        self
    }

    /// Attach the element invariant dependency for container invariants.
    #[must_use]
    pub fn with_element_invariant_method(mut self, method: Option<String>) -> Self {
        self.element_invariant_method = method;
        self
    }

    /// Returns the type name this invariant applies to.
    #[must_use]
    pub fn type_name(&self) -> &str {
        &self.type_name
    }

    /// Returns the name of the logical self parameter.
    #[must_use]
    pub fn self_param(&self) -> &str {
        &self.self_param
    }

    /// Returns the optional sort annotation for the self parameter.
    #[must_use]
    pub fn param_sort(&self) -> Option<&ExprSort> {
        self.param_sort.as_ref()
    }

    /// Returns the invariant body expression.
    #[must_use]
    pub fn body(&self) -> &PureExpr {
        &self.body
    }

    /// Returns whether this invariant is treated as a newtype.
    #[must_use]
    pub fn is_newtype(&self) -> bool {
        self.is_newtype
    }

    /// Returns the dependent element invariant method, if any.
    #[must_use]
    pub fn element_invariant_method(&self) -> Option<&str> {
        self.element_invariant_method.as_deref()
    }

    /// Replace the invariant body after a rewrite pass.
    pub fn set_body(&mut self, body: PureExpr) {
        self.body = body;
    }
}

/// Construct a [`TypeInvariantDef`] without depending on its private fields.
#[macro_export]
macro_rules! type_invariant_def {
    (
        type_name: $type_name:expr,
        self_param: $self_param:expr,
        param_sort: $param_sort:expr,
        body: $body:expr,
        is_newtype: $is_newtype:expr,
        element_invariant_method: $element_invariant_method:expr $(,)?
    ) => {
        $crate::logic::TypeInvariantDef::new($type_name, $self_param, $body)
            .with_param_sort($param_sort)
            .with_newtype($is_newtype)
            .with_element_invariant_method($element_invariant_method)
    };
    (
        type_name: $type_name:expr,
        self_param: $self_param:expr,
        body: $body:expr,
        param_sort: $param_sort:expr,
        is_newtype: $is_newtype:expr,
        element_invariant_method: $element_invariant_method:expr $(,)?
    ) => {
        $crate::logic::TypeInvariantDef::new($type_name, $self_param, $body)
            .with_param_sort($param_sort)
            .with_newtype($is_newtype)
            .with_element_invariant_method($element_invariant_method)
    };
}

/// Prefix for type-qualified invariant method names.
///
/// Driver-side contract rewriting replaces `.invariant()` with
/// `.__trust_wp_invariant_<Type>()` so each invariant definition gets a distinct
/// SMT symbol even when multiple types share the same parameter sort.
pub const TYPE_INVARIANT_METHOD_PREFIX: &str = "__trust_wp_invariant_";

/// Build the method name used for a specific type's invariant predicate.
///
/// The type suffix is sanitized to `[A-Za-z0-9_]` so the resulting method name
/// is stable and SMT-safe. Special characters are encoded distinctly to avoid
/// collisions between types like `Foo<T>` and `Foo_T_` (#687).
#[must_use]
pub fn type_invariant_method_name(type_name: &str) -> String {
    let mut suffix = String::with_capacity(type_name.len() + 16);
    for ch in type_name.chars() {
        match ch {
            // Escape underscore so encoding tokens (_LT_, etc.) cannot appear
            // in pass-through output, guaranteeing injectivity (#687).
            '_' => suffix.push_str("__"),
            _ if ch.is_ascii_alphanumeric() => suffix.push(ch),
            '<' => suffix.push_str("_LT_"),
            '>' => suffix.push_str("_GT_"),
            ',' => suffix.push_str("_C_"),
            ':' => suffix.push_str("_P_"),
            ' ' => suffix.push_str("_S_"),
            '&' => suffix.push_str("_R_"),
            '*' => suffix.push_str("_D_"),
            '(' => suffix.push_str("_LP_"),
            ')' => suffix.push_str("_RP_"),
            '[' => suffix.push_str("_LB_"),
            ']' => suffix.push_str("_RB_"),
            _ => {
                // Fallback: encode as hex to guarantee uniqueness
                use std::fmt::Write;
                let _ = write!(suffix, "_x{:02X}_", ch as u32);
            }
        }
    }
    if suffix.is_empty() {
        suffix.push('_');
    }
    format!("{TYPE_INVARIANT_METHOD_PREFIX}{suffix}")
}

/// Returns true when `method` denotes an invariant predicate call.
#[must_use]
pub fn is_invariant_method_name(method: &str) -> bool {
    method == "invariant"
        || method == "invariants"
        || method.starts_with(TYPE_INVARIANT_METHOD_PREFIX)
}

/// Convert a logic function name to its SMT identifier.
///
/// This is the canonical way to generate SMT names for logic functions.
/// The format is `logic_<sanitized_name>` where the name is encoded using
/// the same injective character encoding as [`type_invariant_method_name`]
/// to prevent collisions between names like `foo_bar` and `foo::bar` (#1435).
///
/// # Encoding
/// - `_` → `__` (escape underscore so encoding tokens cannot appear in pass-through)
/// - `:` → `_P_` (so `::` becomes `_P__P_`)
/// - Other special characters use the same scheme as `type_invariant_method_name`
/// - Alphanumeric characters pass through unchanged
///
/// # Examples
/// - `"max"` -> `"logic_max"`
/// - `"crate::specs::max"` -> `"logic_crate_P__P_specs_P__P_max"`
/// - `"foo_bar"` != `"foo::bar"` (injective)
#[must_use]
pub fn logic_fn_smt_name(name: &str) -> String {
    let mut suffix = String::with_capacity(name.len() + 16);
    for ch in name.chars() {
        match ch {
            '_' => suffix.push_str("__"),
            ch if ch.is_ascii_alphanumeric() => suffix.push(ch),
            '<' => suffix.push_str("_LT_"),
            '>' => suffix.push_str("_GT_"),
            ',' => suffix.push_str("_C_"),
            ':' => suffix.push_str("_P_"),
            ' ' => suffix.push_str("_S_"),
            '&' => suffix.push_str("_R_"),
            '*' => suffix.push_str("_D_"),
            '(' => suffix.push_str("_LP_"),
            ')' => suffix.push_str("_RP_"),
            '[' => suffix.push_str("_LB_"),
            ']' => suffix.push_str("_RB_"),
            _ => {
                use std::fmt::Write;
                let _ = write!(suffix, "_x{:02X}_", ch as u32);
            }
        }
    }
    format!("logic_{suffix}")
}

#[cfg(test)]
mod tests;
