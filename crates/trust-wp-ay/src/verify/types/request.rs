// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Verification request types: [`VerificationBase`], [`VerificationRequest`],
//! and [`MutBorrowRequest`].
//!
//! These bundles carry the contract clauses (requires/ensures), configuration
//! options, and mutable-borrow-specific fields needed by the verification
//! entry points.

use std::{
    collections::{HashMap, HashSet},
    time::Duration,
};

use trust_wp_core::{
    formula::{BorrowFinality, BorrowIdOrigin, ProjectedFinalPin, PureExpr},
    logic::{AdtDecls, AdtFieldRanges, LogicFnDef, LogicMode, TypeInvariantDef},
    TrackLevel,
};

use super::ClosureCaptureInfo;
use crate::encoder::{unsoundness, LogicGroundInstantiationMode};

/// Shared fields for pure and mutable-borrow verification requests.
///
/// Extracted from [`VerificationRequest`] and [`MutBorrowRequest`] to
/// eliminate duplication of the 14 fields common to both verification
/// paths (#1274). Shared field storage and update logic live here;
/// request types delegate to this internal base so the public API only
/// exposes the request bundles.
#[derive(Debug, Clone)]
pub(crate) struct VerificationBase<'a> {
    pub(crate) requires: &'a [PureExpr],
    pub(crate) ensures: &'a [PureExpr],
    /// Extra ghost facts asserted as ambient context.
    pub(crate) ghost_context: Option<&'a [PureExpr]>,
    pub(crate) return_expr: Option<&'a PureExpr>,
    pub(crate) logic_fns: Option<&'a [LogicFnDef]>,
    /// Logic function bodies available only to local, demand-driven recursive
    /// datatype unfoldings.
    ///
    /// This is intentionally separate from `logic_fns`: fail-closed callers may
    /// filter global solver axioms while still allowing local one-step
    /// definitions for recursive datatype calls that occur in the current VC.
    pub(crate) local_unfolding_logic_fns: Option<&'a [LogicFnDef]>,
    pub(crate) mode_overrides: Option<&'a [LogicMode]>,
    pub(crate) type_invariants: Option<&'a [TypeInvariantDef]>,
    pub(crate) track: Option<TrackLevel>,
    pub(crate) timeout: Option<Duration>,
    pub(crate) type_constants: Option<&'a HashMap<String, PureExpr>>,
    /// Closure struct sort registrations for Layer 2 capture projection.
    ///
    /// When present, the verification encoder registers structural closure sorts
    /// so that capture field accessors are available for postcondition projection
    /// and the `resolve` predicate decomposes structurally.
    pub(crate) closure_captures: Option<&'a [ClosureCaptureInfo]>,
    /// When true, suppress division-by-zero obligations for `Div`/`Mod`.
    ///
    /// SMT-LIB integer `div` and `mod` are total functions — `(mod a 0)` is
    /// well-defined. This flag should be set for ghost functions operating on
    /// mathematical `Int` (Creusot's unbounded integer type), where division
    /// by zero is not a runtime panic but a defined mathematical operation.
    pub(crate) total_int_arithmetic: bool,
    /// Per-ADT field range constraints for unsigned/signed integer fields.
    ///
    /// When populated by the driver from `TyCtxt` ADT definitions, the encoder
    /// injects quantified axioms constraining ADT constructor fields to their
    /// Rust integer ranges. Without this, fields like `u32` are unbounded
    /// `Sort::Int`, allowing the solver to assign negative values and produce
    /// spurious counterexamples. (#2097, RC1)
    pub(crate) adt_field_ranges: Option<AdtFieldRanges>,
    /// Rustc-backed ADT declarations for native datatype registration. (#1982)
    pub(crate) adt_decls: Option<AdtDecls>,
    /// Pre-verification unsoundness snapshot from the driver (#2206).
    ///
    /// When the driver instruments unsoundness categories during MIR extraction
    /// (e.g., `OpaqueCallTrueAssumption` fires in `handle_opaque_call`), those
    /// increments happen *before* `verify_function_with_modes` is called. The
    /// snapshot taken inside `verify_function_with_modes` would miss them
    /// (delta = 0). By passing a snapshot taken before MIR extraction, the
    /// verification function can compute the correct delta spanning both
    /// extraction and encoding phases.
    pub(crate) unsoundness_snapshot: Option<unsoundness::Snapshot>,
    /// Logic ground-pool flushing mode (#1925).
    pub(crate) logic_ground_mode: LogicGroundInstantiationMode,
    /// When true, use ay's native BV theory for bitwise operations instead of
    /// UF approximations. Enabled by default for all functions (#2666).
    /// The `#[bitwise_proof]` annotation is no longer required.
    pub(crate) bitwise_proof: bool,
    /// This VC's goal set carries a fail-closed `false` obligation the DRIVER
    /// injected because it could not model something (an unspecified callee, a
    /// dropped spec clause, an exhausted walk — see
    /// [`crate::verify::goals_carry_fail_closed_marker`]).
    ///
    /// The marker is correct and must never be dropped: it makes the VC
    /// unprovable by construction, which is the fail-closed reading. What it
    /// must NOT do is license a refutation. A SAT model for a goal set
    /// containing `false` refutes a clause TRUST-WP manufactured, not one the
    /// program broke, so the verdict is withheld at the boundary.
    ///
    /// Defaults to `false` — "every goal here is a clause somebody wrote" —
    /// so a caller that does not set it keeps its pre-existing verdicts.
    pub(crate) injected_fail_closed_goal: bool,
}

impl<'a> VerificationBase<'a> {
    /// Create a base with required fields; all optional fields default to None.
    #[must_use]
    pub(crate) fn new(requires: &'a [PureExpr], ensures: &'a [PureExpr]) -> Self {
        Self {
            requires,
            ensures,
            ghost_context: None,
            return_expr: None,
            logic_fns: None,
            local_unfolding_logic_fns: None,
            mode_overrides: None,
            type_invariants: None,
            track: None,
            timeout: None,
            type_constants: None,
            closure_captures: None,
            total_int_arithmetic: false,
            adt_field_ranges: None,
            adt_decls: None,
            unsoundness_snapshot: None,
            logic_ground_mode: LogicGroundInstantiationMode::default(),
            bitwise_proof: true,
            injected_fail_closed_goal: false,
        }
    }

    #[must_use]
    pub(crate) fn ghost_context(mut self, v: Option<&'a [PureExpr]>) -> Self {
        self.ghost_context = v;
        self
    }

    #[must_use]
    pub(crate) fn return_expr(mut self, v: Option<&'a PureExpr>) -> Self {
        self.return_expr = v;
        self
    }

    #[must_use]
    pub(crate) fn logic_fns(mut self, v: Option<&'a [LogicFnDef]>) -> Self {
        self.logic_fns = v;
        self
    }

    #[must_use]
    pub(crate) fn local_unfolding_logic_fns(mut self, v: Option<&'a [LogicFnDef]>) -> Self {
        self.local_unfolding_logic_fns = v;
        self
    }

    #[must_use]
    pub(crate) fn mode_overrides(mut self, v: Option<&'a [LogicMode]>) -> Self {
        self.mode_overrides = v;
        self
    }

    #[must_use]
    pub(crate) fn type_invariants(mut self, v: Option<&'a [TypeInvariantDef]>) -> Self {
        self.type_invariants = v;
        self
    }

    #[must_use]
    pub(crate) fn track(mut self, v: Option<TrackLevel>) -> Self {
        self.track = v;
        self
    }

    #[must_use]
    pub(crate) fn timeout(mut self, v: Option<Duration>) -> Self {
        self.timeout = v;
        self
    }

    #[must_use]
    pub(crate) fn type_constants(mut self, v: Option<&'a HashMap<String, PureExpr>>) -> Self {
        self.type_constants = v;
        self
    }

    #[must_use]
    pub(crate) fn closure_captures(mut self, v: Option<&'a [ClosureCaptureInfo]>) -> Self {
        self.closure_captures = v;
        self
    }

    /// Set total integer arithmetic mode (suppresses division obligations).
    #[must_use]
    pub(crate) fn total_int_arithmetic(mut self, total: bool) -> Self {
        self.total_int_arithmetic = total;
        self
    }

    /// Set ADT field range constraints. (#2097, RC1)
    #[must_use]
    pub(crate) fn adt_field_ranges(mut self, ranges: Option<AdtFieldRanges>) -> Self {
        self.adt_field_ranges = ranges;
        self
    }

    /// Set rustc-backed ADT declarations. (#1982)
    #[must_use]
    pub(crate) fn adt_decls(mut self, decls: Option<AdtDecls>) -> Self {
        self.adt_decls = decls;
        self
    }

    /// Set a pre-verification unsoundness snapshot (#2206).
    #[must_use]
    pub(crate) fn unsoundness_snapshot(mut self, snapshot: Option<unsoundness::Snapshot>) -> Self {
        self.unsoundness_snapshot = snapshot;
        self
    }

    /// Set the logic ground instantiation mode (#1925).
    #[cfg(test)]
    #[must_use]
    pub(crate) fn logic_ground_mode(mut self, mode: LogicGroundInstantiationMode) -> Self {
        self.logic_ground_mode = mode;
        self
    }

    /// Set bitwise proof mode — use ay BV theory for bitwise ops. (#2666)
    #[must_use]
    pub(crate) fn bitwise_proof(mut self, enabled: bool) -> Self {
        self.bitwise_proof = enabled;
        self
    }

    /// Declare that this VC's goals include a driver-injected fail-closed
    /// `false`. See [`VerificationBase::injected_fail_closed_goal`].
    #[must_use]
    pub(crate) fn injected_fail_closed_goal(mut self, injected: bool) -> Self {
        self.injected_fail_closed_goal = injected;
        self
    }
}

// Keep the public request-bundle setters in sync while the actual field
// storage and update logic remain centralized in VerificationBase.
macro_rules! impl_shared_request_builders {
    () => {
        /// Set total integer arithmetic mode (suppresses division obligations). (#1800)
        #[must_use]
        pub fn total_int_arithmetic(mut self, total: bool) -> Self {
            self.base = self.base.total_int_arithmetic(total);
            self
        }

        /// Set ADT field range constraints. (#2097, RC1)
        #[must_use]
        pub fn adt_field_ranges(mut self, ranges: Option<AdtFieldRanges>) -> Self {
            self.base = self.base.adt_field_ranges(ranges);
            self
        }

        /// Set rustc-backed ADT declarations. (#1982)
        #[must_use]
        pub fn adt_decls(mut self, decls: Option<AdtDecls>) -> Self {
            self.base = self.base.adt_decls(decls);
            self
        }

        #[must_use]
        pub fn ghost_context(mut self, ghost_context: Option<&'a [PureExpr]>) -> Self {
            self.base = self.base.ghost_context(ghost_context);
            self
        }

        #[must_use]
        pub fn return_expr(mut self, return_expr: Option<&'a PureExpr>) -> Self {
            self.base = self.base.return_expr(return_expr);
            self
        }

        #[must_use]
        pub fn logic_fns(mut self, logic_fns: Option<&'a [LogicFnDef]>) -> Self {
            self.base = self.base.logic_fns(logic_fns);
            self
        }

        #[must_use]
        pub fn local_unfolding_logic_fns(mut self, logic_fns: Option<&'a [LogicFnDef]>) -> Self {
            self.base = self.base.local_unfolding_logic_fns(logic_fns);
            self
        }

        #[must_use]
        pub fn mode_overrides(mut self, mode_overrides: Option<&'a [LogicMode]>) -> Self {
            self.base = self.base.mode_overrides(mode_overrides);
            self
        }

        #[must_use]
        pub fn type_invariants(mut self, type_invariants: Option<&'a [TypeInvariantDef]>) -> Self {
            self.base = self.base.type_invariants(type_invariants);
            self
        }

        #[must_use]
        pub fn track(mut self, track: Option<TrackLevel>) -> Self {
            self.base = self.base.track(track);
            self
        }

        #[must_use]
        pub fn timeout(mut self, timeout: Option<Duration>) -> Self {
            self.base = self.base.timeout(timeout);
            self
        }

        #[must_use]
        pub fn type_constants(
            mut self,
            type_constants: Option<&'a HashMap<String, PureExpr>>,
        ) -> Self {
            self.base = self.base.type_constants(type_constants);
            self
        }

        #[must_use]
        pub fn closure_captures(mut self, captures: Option<&'a [ClosureCaptureInfo]>) -> Self {
            self.base = self.base.closure_captures(captures);
            self
        }

        /// Set a pre-verification unsoundness snapshot (#2206).
        #[must_use]
        pub fn unsoundness_snapshot(mut self, snapshot: Option<unsoundness::Snapshot>) -> Self {
            self.base = self.base.unsoundness_snapshot(snapshot);
            self
        }

        /// Set bitwise proof mode — use ay BV theory for bitwise ops. (#2666)
        #[must_use]
        pub fn bitwise_proof(mut self, enabled: bool) -> Self {
            self.base = self.base.bitwise_proof(enabled);
            self
        }

        /// Declare that this VC's goal set carries a driver-injected
        /// fail-closed `false` obligation, so no refutation from it may be
        /// published. Off by default.
        #[must_use]
        pub fn injected_fail_closed_goal(mut self, injected: bool) -> Self {
            self.base = self.base.injected_fail_closed_goal(injected);
            self
        }
    };
}

/// Input bundle for [`crate::verify::verify_function_with_modes`].
///
/// Wraps the shared pure-function verification configuration.
///
/// All shared fields live in `base`; this struct has no unique fields.
#[derive(Debug, Clone)]
pub struct VerificationRequest<'a> {
    pub(crate) base: VerificationBase<'a>,
}

impl<'a> VerificationRequest<'a> {
    /// Create a request with required fields; all optional fields default to None.
    #[must_use]
    pub fn new(requires: &'a [PureExpr], ensures: &'a [PureExpr]) -> Self {
        Self {
            base: VerificationBase::new(requires, ensures),
        }
    }

    impl_shared_request_builders!();

    /// Set logic ground instantiation mode (#1925).
    #[cfg(test)]
    #[must_use]
    pub(crate) fn logic_ground_mode(mut self, mode: LogicGroundInstantiationMode) -> Self {
        self.base = self.base.logic_ground_mode(mode);
        self
    }
}

/// Input bundle for [`crate::verify::verify_mut_borrow_function_with_modes`].
///
/// Wraps the shared mutable-borrow verification configuration and adds
/// mutable-borrow-specific fields:
/// `final_values`, `resolve_assumptions`, `prophecy_writebacks`,
/// `borrow_finality`, `borrow_id_origins`, and `mutation_continued_params`.
#[derive(Debug, Clone)]
pub struct MutBorrowRequest<'a> {
    pub(crate) base: VerificationBase<'a>,
    pub(crate) final_values: &'a HashMap<String, PureExpr>,
    /// Parameter names that have dataflow-precise resolve points (#2124).
    ///
    /// When present, for each name in this list the encoder emits an additional
    /// assumption `v_final == v_current` (the resolve assertion). This closes
    /// the prophecy: the final value of the borrow equals its current value at
    /// the point where the borrow is resolved (i.e., goes out of scope).
    pub(crate) resolve_assumptions: Option<Vec<String>>,
    /// Prophecy writeback pairs for intermediate reborrows (#2124 Phase 3).
    ///
    /// Each entry maps a child reborrow name to its parent borrow name.
    /// For a reborrow `z = &mut *y`, the entry is `("z_rb5", "y")`.
    /// The encoder emits `y_current = z_rb5_final` for each pair, which is
    /// the Creusot-style prophecy writeback: after the reborrow is created,
    /// the parent's current value becomes the child's (unknown) final value.
    pub(crate) prophecy_writebacks: Option<HashMap<String, String>>,
    /// Per-reborrow finality from backward dataflow analysis (#2181).
    ///
    /// Maps reborrow child name to its `BorrowFinality`. When a reborrow is
    /// `Final`, the encoder skips the fresh prophecy variable and reuses the
    /// parent's `_final` variable. This reduces O(n) prophecy variables per
    /// reborrow chain to O(1).
    pub(crate) borrow_finality: Option<HashMap<String, BorrowFinality>>,
    /// Per-reborrow borrow-id origin metadata for whole-borrow identity. (#2141)
    pub(crate) borrow_id_origins: Option<HashMap<String, BorrowIdOrigin>>,
    /// Parameters whose mutation was detected but not symbolically advanced (#2124 Phase 5).
    ///
    /// For these parameters, the encoder skips the `v_final == v_current`
    /// identity assertion from `final_values`, letting `call_assumptions`
    /// (which inject the call's postcondition) and `resolve_assertions`
    /// (which close the prophecy at borrow termination) be the sole
    /// constraints on the parameter's final value.
    pub(crate) mutation_continued_params: Option<HashSet<String>>,
    /// Parameter names that are `&mut [T]` slices. A slice's length is
    /// immutable through `&mut [T]` (only elements may change), so the encoder
    /// emits `seq_len(v_final_view) == seq_len(v_view)` linking the slice's
    /// length across all program-point states even when the borrow is NOT
    /// resolved as identity (elements differ). Without it the prophecy length
    /// of a slice param mutated across an inner call is left free, admitting
    /// spurious counterexamples (bitvectors/bitwalker).
    pub(crate) slice_length_stable_vars: Option<Vec<String>>,
    /// Caller-side expiry pins for `&mut` borrows reached by projecting out of
    /// a call result (#prophecy-slots M5).
    ///
    /// Each pin is `^<carrier> == <death value>`, guarded by the tester of
    /// every enum variant on the path. The DRIVER owns the proof that the death
    /// point is real (`mir_analysis::projected_expiry`, conditions R0..R11);
    /// the encoder owns the fail-closed refusal when the projection cannot be
    /// walked exactly. A pin at an unproven death point is a false-accept
    /// factory, so neither side may guess.
    pub(crate) projected_final_pins: Option<Vec<ProjectedFinalPin>>,
}

impl<'a> MutBorrowRequest<'a> {
    /// Create a request with required fields; all optional fields default to None.
    #[must_use]
    pub fn new(
        requires: &'a [PureExpr],
        ensures: &'a [PureExpr],
        final_values: &'a HashMap<String, PureExpr>,
    ) -> Self {
        Self {
            base: VerificationBase::new(requires, ensures),
            final_values,
            resolve_assumptions: None,
            prophecy_writebacks: None,
            borrow_finality: None,
            borrow_id_origins: None,
            mutation_continued_params: None,
            slice_length_stable_vars: None,
            projected_final_pins: None,
        }
    }

    impl_shared_request_builders!();

    /// Set the caller-side projected expiry pins (#prophecy-slots M5).
    #[must_use]
    pub fn projected_final_pins(mut self, pins: Option<Vec<ProjectedFinalPin>>) -> Self {
        self.projected_final_pins = pins;
        self
    }

    /// Set `&mut [T]` slice parameter names for length-preservation axioms.
    #[must_use]
    pub fn slice_length_stable_vars(mut self, names: Option<Vec<String>>) -> Self {
        self.slice_length_stable_vars = names;
        self
    }

    /// Set resolve assumptions for dataflow-precise borrow resolution (#2124).
    ///
    /// Each string is a parameter name whose borrow has a precise resolve point.
    /// The encoder will emit `assume(v_final == v_current)` for each.
    #[must_use]
    pub fn resolve_assumptions(mut self, names: Option<Vec<String>>) -> Self {
        self.resolve_assumptions = names;
        self
    }

    /// Set prophecy writeback pairs for intermediate reborrows (#2124 Phase 3).
    ///
    /// Each entry maps child reborrow name → parent borrow name. The encoder
    /// emits `parent_current = child_final` for each pair.
    #[must_use]
    pub fn prophecy_writebacks(mut self, writebacks: Option<HashMap<String, String>>) -> Self {
        self.prophecy_writebacks = writebacks;
        self
    }

    /// Set per-reborrow finality from backward dataflow analysis (#2181).
    ///
    /// Final borrows inherit the parent's prophecy variable instead of
    /// allocating a fresh one. The encoder skips the writeback constraint
    /// for final borrows.
    #[must_use]
    pub fn borrow_finality(mut self, finality: Option<HashMap<String, BorrowFinality>>) -> Self {
        self.borrow_finality = finality;
        self
    }

    /// Set per-reborrow borrow-id origin metadata. (#2141)
    #[must_use]
    pub fn borrow_id_origins(mut self, origins: Option<HashMap<String, BorrowIdOrigin>>) -> Self {
        self.borrow_id_origins = origins;
        self
    }

    /// Set mutation-continued parameter names (#2124 Phase 5).
    ///
    /// For these parameters, the encoder skips the identity `v_final == v_current`
    /// assertion, letting call_assumptions + resolve_assertions constrain the
    /// final value instead.
    #[must_use]
    pub fn mutation_continued_params(mut self, params: Option<HashSet<String>>) -> Self {
        self.mutation_continued_params = params;
        self
    }

    /// Deprecated compatibility no-op.
    ///
    /// Grounded mut-borrow postconditions are never asserted before the
    /// negated-goal check; assuming the target ensure makes wrong posts verify.
    #[must_use]
    pub fn assert_grounded_ensures(self, _assert_grounded: bool) -> Self {
        self
    }
}
