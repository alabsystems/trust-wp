// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Data types for loop invariant verification.
//!
//! Contains the configuration, context, and input structs used by the loop
//! verification dispatcher and its sub-phases (initialization, preservation,
//! postcondition, variant).

use std::{collections::HashMap, time::Duration};

use trust_wp_core::{
    formula::{NamedBindingValue, PureExpr},
    logic::{LogicFnDef, LogicMode, TypeInvariantDef},
    TrackLevel,
};

/// Configuration for creating loop verification encoders (#791).
///
/// Bundles the six parameters that every loop verification sub-function
/// passes through to `setup_loop_encoder`:
/// - Type invariant definitions (axioms for user-defined types)
/// - Logic function definitions and their mode overrides
/// - Type-level constants (`Self::MIN`, `Self::MAX`)
/// - Memory tracking precision level
/// - Solver timeout
///
/// Using a config struct eliminates 6 positional parameters from each
/// function signature, reducing the `too_many_arguments` suppressions.
#[derive(Default)]
pub struct LoopEncoderConfig<'a> {
    /// Type invariant definitions to register as axioms (#654).
    pub(crate) type_invariants: Option<&'a [TypeInvariantDef]>,
    /// Logic function definitions to register as axioms (#739).
    pub(crate) logic_fns: Option<&'a [LogicFnDef]>,
    /// Per-function mode overrides for logic functions (#757).
    pub(crate) mode_overrides: Option<&'a [LogicMode]>,
    /// Type-level constants (e.g., `Self::MIN`, `Self::MAX`) (#757).
    pub(crate) type_constants: Option<&'a HashMap<String, PureExpr>>,
    /// Memory tracking precision level (#757).
    pub(crate) track: Option<TrackLevel>,
    /// Solver timeout.
    pub(crate) timeout: Option<Duration>,
    /// Additional transition facts asserted during preservation/variant decrease.
    ///
    /// Used for auto-synthesized for-loop iterator-step facts like
    /// `iter_state.produces(seq![x], iter_state_next)`. Kept out of
    /// initialization/postcondition because they describe one loop step,
    /// not the entry or exhausted states. (#2171)
    pub(crate) transition_facts: Vec<PureExpr>,
    /// Additional bridge facts asserted during preservation without step slicing.
    ///
    /// Used for identity bridges that connect yielded loop locals back to
    /// stable pre-loop names, such as `Final(k2) == Final(bor_k)`. These facts
    /// must remain available even when the invariant slice mentions only the
    /// stable side of the bridge. (#2116)
    pub(crate) bridge_facts: Vec<PureExpr>,
    /// Rustc-backed ADT declarations for native datatype encoding (#1982).
    ///
    /// When present, loop verification bootstrap predeclares these datatypes
    /// so user-defined struct/enum constructors and field selectors encode
    /// natively instead of falling back to tuple/UF approximations.
    pub(crate) adt_decls: Option<&'a trust_wp_core::logic::AdtDecls>,
    /// Per-ADT integer field range constraints for loop VCs (#2702).
    ///
    /// Threads the same `AdtFieldRanges` the function-level pipeline uses into
    /// loop verification so unsigned/signed struct fields (e.g. the `u32`
    /// components of a `CustomVariant(u32, u32)` loop variant) carry their
    /// `field(x) >= 0` non-negativity facts. Without this, postcondition and
    /// variant-nonneg loop VCs that depend on `x.0 >= 0` / `x.1 >= 0` are
    /// spuriously SAT.
    pub(crate) adt_field_ranges: Option<&'a trust_wp_core::logic::AdtFieldRanges>,
    /// Variable names whose borrows resolve within the loop body (#2116).
    ///
    /// For consuming iterators (e.g., FMap `into_iter`), the yielded loop
    /// element is consumed at end of each iteration. Deref effects on these
    /// variables produce a borrow resolution constraint in preservation:
    ///   `var_prime_final == var_prime_current`
    /// Without this, the Final (prophecy) of the yielded element is a free
    /// variable in the preservation VC, making invariants referencing `^snap`
    /// of pre-loop borrows unprovable.
    pub(crate) loop_element_borrow_vars: Vec<String>,
}

impl<'a> LoopEncoderConfig<'a> {
    /// Set type invariant definitions to register as axioms.
    #[must_use]
    pub fn with_type_invariants(mut self, invs: &'a [TypeInvariantDef]) -> Self {
        self.type_invariants = Some(invs);
        self
    }

    /// Set logic function definitions to register as axioms.
    #[must_use]
    pub fn with_logic_fns(mut self, fns: &'a [LogicFnDef]) -> Self {
        self.logic_fns = Some(fns);
        self
    }

    /// Set per-function mode overrides for logic functions.
    #[must_use]
    pub fn with_mode_overrides(mut self, modes: &'a [LogicMode]) -> Self {
        self.mode_overrides = Some(modes);
        self
    }

    /// Set type-level constants (e.g., `Self::MIN`, `Self::MAX`).
    #[must_use]
    pub fn with_type_constants(mut self, constants: &'a HashMap<String, PureExpr>) -> Self {
        self.type_constants = Some(constants);
        self
    }

    /// Set memory tracking precision level.
    #[must_use]
    pub fn with_track(mut self, track: TrackLevel) -> Self {
        self.track = Some(track);
        self
    }

    /// Set solver timeout.
    #[must_use]
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// Set preservation/variant transition facts.
    #[must_use]
    pub fn with_transition_facts(mut self, facts: &[PureExpr]) -> Self {
        self.transition_facts = facts.to_vec();
        self
    }

    /// Set preservation bridge facts.
    #[must_use]
    pub fn with_bridge_facts(mut self, facts: &[PureExpr]) -> Self {
        self.bridge_facts = facts.to_vec();
        self
    }

    /// Set rustc-backed ADT declarations for native datatype encoding (#1982).
    #[must_use]
    pub fn with_adt_decls(mut self, decls: &'a trust_wp_core::logic::AdtDecls) -> Self {
        self.adt_decls = Some(decls);
        self
    }

    /// Set per-ADT integer field range constraints for loop VCs (#2702).
    #[must_use]
    pub fn with_adt_field_ranges(
        mut self,
        ranges: &'a trust_wp_core::logic::AdtFieldRanges,
    ) -> Self {
        self.adt_field_ranges = Some(ranges);
        self
    }

    /// Set variables whose borrows resolve within the loop body (#2116).
    #[must_use]
    pub fn with_loop_element_borrow_vars(mut self, vars: Vec<String>) -> Self {
        self.loop_element_borrow_vars = vars;
        self
    }
}

/// Bundled loop body effects for the current iteration step (#2657).
///
/// Groups the three body-effect maps (direct, deref, double-deref) that
/// always travel together when constructing a [`LoopVerificationContext`].
#[derive(Clone, Copy)]
pub struct BodyEffects<'a> {
    /// Direct assignments: `x = expr`.
    pub(crate) direct: &'a HashMap<String, PureExpr>,
    /// Single-deref assignments: `*x = expr`.
    pub(crate) deref: &'a HashMap<String, PureExpr>,
    /// Double-deref assignments: `**x = expr`.
    pub(crate) double_deref: &'a HashMap<String, PureExpr>,
}

impl<'a> BodyEffects<'a> {
    #[must_use]
    pub fn new(
        direct: &'a HashMap<String, PureExpr>,
        deref: &'a HashMap<String, PureExpr>,
        double_deref: &'a HashMap<String, PureExpr>,
    ) -> Self {
        Self {
            direct,
            deref,
            double_deref,
        }
    }

    pub(crate) fn keys(self) -> impl Iterator<Item = &'a String> {
        self.direct
            .keys()
            .chain(self.deref.keys())
            .chain(self.double_deref.keys())
    }

    pub(crate) fn values(self) -> impl Iterator<Item = &'a PureExpr> {
        self.direct
            .values()
            .chain(self.deref.values())
            .chain(self.double_deref.values())
    }
}

/// Inputs specific to loop postcondition verification.
#[derive(Clone, Copy)]
pub(crate) struct PostconditionInputs<'a> {
    pub(crate) ensures: &'a [PureExpr],
    pub(crate) return_expr: Option<&'a PureExpr>,
    pub(crate) pre_loop_assignments: &'a HashMap<String, NamedBindingValue>,
    pub(crate) requires: &'a [PureExpr],
    pub(crate) post_extra_facts: &'a [PureExpr],
}

/// Shared base parameters for loop sub-phase verification conditions (#2657).
///
/// Bundles the six positional parameters that every loop sub-function
/// (preservation, postcondition, variant) accepts: invariants, loop condition,
/// condition mode, modified variables, body effects, and encoder config.
/// Passing a single `&LoopVcBase` instead of 6 positional arguments eliminates
/// `too_many_arguments` suppressions in the sub-phase functions.
#[derive(Clone, Copy)]
pub(crate) struct LoopVcBase<'a> {
    pub(crate) invariants: &'a [PureExpr],
    pub(crate) loop_condition: Option<&'a PureExpr>,
    pub(crate) condition_is_body_break: bool,
    pub(crate) modified_vars: &'a [&'a str],
    pub(crate) effects: BodyEffects<'a>,
    pub(crate) config: &'a LoopEncoderConfig<'a>,
}

/// Complete context for loop invariant verification (#791).
///
/// Bundles all inputs to the inductive loop verification pipeline:
/// expressions (requires, ensures, invariants), loop-specific data
/// (condition, modified variables, body effects, variant), and encoder
/// configuration. Internal sub-functions (`verify_initialization`,
/// `verify_preservation`, etc.) extract the fields they need from this
/// context instead of accepting long positional parameter lists.
pub struct LoopVerificationContext<'a> {
    /// Function preconditions.
    pub(crate) requires: &'a [PureExpr],
    /// Function postconditions.
    pub(crate) ensures: &'a [PureExpr],
    /// Loop invariant expressions.
    pub(crate) invariants: &'a [PureExpr],
    /// Loop continuation condition (if extractable).
    pub(crate) loop_condition: Option<&'a PureExpr>,
    /// Whether the condition is a body-break pattern (checked after body effects).
    ///
    /// When `true`, preservation applies the condition to primed (post-body)
    /// variables. When `false` (header condition), the condition is applied to
    /// the pre-body state. (#1295)
    pub(crate) condition_is_body_break: bool,
    /// Variables modified by the loop body (for priming).
    pub(crate) modified_vars: &'a [&'a str],
    /// Map from variable to its updated expression after one iteration.
    pub(crate) body_effect: &'a HashMap<String, PureExpr>,
    /// Map from variable to the value written through `*var` in the loop body.
    ///
    /// For `*x = 0`, maps `"x"` to `Int(0)`. During preservation, this constrains
    /// `x_prime_current = 0` (the dereference of the primed variable) rather than
    /// havocing `x_prime`. (#1295)
    pub(crate) deref_body_effect: &'a HashMap<String, PureExpr>,
    /// Map from variable to the value written through `**var` in the loop body.
    ///
    /// For `**x = 0` (where `x: &mut &mut i32`), maps `"x"` to `Int(0)`.
    /// During preservation, constrains `x_prime_current_current = 0`. (#1295)
    pub(crate) double_deref_body_effect: &'a HashMap<String, PureExpr>,
    /// Optional loop-local postcondition view of body effects.
    ///
    /// Preservation needs the complete body effect set. The postcondition VC
    /// may need a filtered view when a pointee is written after loop exit: the
    /// loop-local borrow resolution must not claim that the loop-exit current
    /// value is also the function-exit final value. (#1823)
    pub(crate) postcondition_effects: Option<BodyEffects<'a>>,
    /// Optional termination variant expression.
    pub(crate) variant: Option<&'a PureExpr>,
    /// Pre-loop variable assignments (e.g., `let mut i = 0`).
    pub(crate) pre_loop_assignments: &'a HashMap<String, NamedBindingValue>,
    /// Return value expression after loop (binds `result` in postcondition).
    pub(crate) return_expr: Option<&'a PureExpr>,
    /// Extra facts for the initialization check only.
    ///
    /// For Creusot for-loop ghost variables like `produced`, the initial
    /// state (empty sequence) is implicit. These expressions are asserted
    /// alongside pre-loop assignments during init but NOT during
    /// preservation or postcondition checks. (#1295)
    pub(crate) init_extra_facts: &'a [PureExpr],
    /// Extra facts for the postcondition check only.
    ///
    /// For Creusot for-loop iterators, when the loop exits the iterator
    /// is exhausted and `produced` equals the full input sequence. These
    /// expressions are asserted during the postcondition check only — not
    /// during initialization or preservation. (#1581)
    pub(crate) post_extra_facts: &'a [PureExpr],
    /// Encoder configuration (type invariants, logic fns, track level, timeout).
    pub(crate) config: LoopEncoderConfig<'a>,
}

impl<'a> LoopVerificationContext<'a> {
    /// Create a new loop verification context with required fields.
    ///
    /// All optional fields default to empty/None. Use the `with_*` builder
    /// methods to set them. This is the stable construction path — callers
    /// should not depend on struct-literal field order or count.
    ///
    /// Body effects (direct, deref, double-deref assignments) are bundled
    /// via [`BodyEffects`] to reduce positional parameter count (#2657).
    #[must_use]
    pub fn new(
        requires: &'a [PureExpr],
        ensures: &'a [PureExpr],
        invariants: &'a [PureExpr],
        modified_vars: &'a [&'a str],
        effects: BodyEffects<'a>,
        pre_loop_assignments: &'a HashMap<String, NamedBindingValue>,
    ) -> Self {
        Self {
            requires,
            ensures,
            invariants,
            loop_condition: None,
            condition_is_body_break: false,
            modified_vars,
            body_effect: effects.direct,
            deref_body_effect: effects.deref,
            double_deref_body_effect: effects.double_deref,
            postcondition_effects: None,
            variant: None,
            pre_loop_assignments,
            return_expr: None,
            init_extra_facts: &[],
            post_extra_facts: &[],
            config: LoopEncoderConfig::default(),
        }
    }

    /// Set the loop continuation condition.
    #[must_use]
    pub fn with_loop_condition(mut self, cond: &'a PureExpr) -> Self {
        self.loop_condition = Some(cond);
        self
    }

    /// Mark the condition as a body-break pattern.
    #[must_use]
    pub fn with_body_break(mut self) -> Self {
        self.condition_is_body_break = true;
        self
    }

    /// Set the termination variant expression.
    #[must_use]
    pub fn with_variant(mut self, variant: &'a PureExpr) -> Self {
        self.variant = Some(variant);
        self
    }

    /// Set the return value expression after the loop.
    #[must_use]
    pub fn with_return_expr(mut self, expr: &'a PureExpr) -> Self {
        self.return_expr = Some(expr);
        self
    }

    /// Set extra facts for the initialization check only.
    #[must_use]
    pub fn with_init_extra_facts(mut self, facts: &'a [PureExpr]) -> Self {
        self.init_extra_facts = facts;
        self
    }

    /// Set extra facts for the postcondition check only.
    #[must_use]
    pub fn with_post_extra_facts(mut self, facts: &'a [PureExpr]) -> Self {
        self.post_extra_facts = facts;
        self
    }

    /// Set a postcondition-only effect view.
    #[must_use]
    pub fn with_postcondition_effects(mut self, effects: BodyEffects<'a>) -> Self {
        self.postcondition_effects = Some(effects);
        self
    }

    /// Set the encoder configuration.
    #[must_use]
    pub fn with_config(mut self, config: LoopEncoderConfig<'a>) -> Self {
        self.config = config;
        self
    }

    #[must_use]
    pub(crate) fn body_effects(&self) -> BodyEffects<'a> {
        BodyEffects::new(
            self.body_effect,
            self.deref_body_effect,
            self.double_deref_body_effect,
        )
    }

    #[must_use]
    pub(crate) fn postcondition_body_effects(&self) -> BodyEffects<'a> {
        self.postcondition_effects
            .unwrap_or_else(|| self.body_effects())
    }
}
