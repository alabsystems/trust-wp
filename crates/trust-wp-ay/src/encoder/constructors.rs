// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AYEncoder constructors and initialization helpers.
//!
//! ## Constructor → Logic Mapping
//!
//! | Constructor                    | Logic      | UFs | Quantifiers | Arrays |
//! |-------------------------------|------------|:---:|:-----------:|:------:|
//! | `new()` / `try_new()`         | QF_AUFLIA  | Yes | No          | Yes    |
//! | `new_with_quantifiers()`      | AUFLIA     | Yes | Yes         | Yes    |
//! | `new_pure()` / `try_new_pure()` | QF_LIA   | No  | No          | No     |
//! | `new_pure_with_quantifiers()` | UFLIA      | Yes | Yes         | No     |
//! | `new_all()`                   | ALL        | Yes | Yes         | Yes    |
//!
//! **Selection guide:**
//! - Pure arithmetic only → `new_pure()` (fastest)
//! - Uninterpreted functions or Seq/Array operations → `new()`
//! - Forall/Exists quantifiers without arrays → `new_pure_with_quantifiers()`
//! - Quantifiers + arrays/Seq → `new_with_quantifiers()`
//! - Custom sorts (datatypes, Seq sort) + quantifiers → `new_all()` (#994, #1944)
//!
//! The production verification pipeline selects the correct `try_new*()`
//! constructor automatically via `detect_logic_requirements` in `verify/setup.rs`,
//! propagating solver init failures as `EncodingError`. The panicking `new*()`
//! variants are convenience wrappers for test code only (#1088).
//! Tests must manually choose the right constructor for their formula.

use ay_dpll::api::{Logic, Solver};

#[cfg(any(test, feature = "sep-logic"))]
use super::SepConjCache;
use super::{
    ground_pool::GroundTermPool, replay_artifact::ReplayRecorder, AYEncoder, AdtState,
    ArithmeticModeState, AssertionPipelineState, ClosureState, DeclarationState,
    EncodingCacheState, QuantifierState, SeqState, SortResolverState, TraversalState, VarEnv,
};
use crate::{
    error::EncodingError,
    memory_model::{BaseMemoryModel, MemState},
};

impl AYEncoder {
    /// Create a new encoder with quantifier-free logic (panics on failure).
    ///
    /// # Panics
    ///
    /// Panics if the ay solver cannot be created (e.g., OOM, configuration error).
    /// **Production code should use [`try_new()`](Self::try_new) instead**, which
    /// returns `Result<Self, EncodingError>` and allows callers to handle init
    /// failures gracefully (e.g., returning `VerificationResult::Unknown`).
    ///
    /// This convenience constructor is intended for test code where solver
    /// creation failure is not a recoverable condition.
    pub fn new() -> Self {
        Self::try_new().expect("failed to create ay solver for QF_AUFLIA logic in AYEncoder::new()")
    }

    /// Try to create a new encoder with quantifier-free logic.
    pub fn try_new() -> Result<Self, EncodingError> {
        Self::try_new_internal(Logic::QfAuflia)
    }

    /// Create a new encoder with quantified logic support (panics on failure).
    ///
    /// # Panics
    ///
    /// Panics if the ay solver cannot be created. **Production code should use
    /// [`try_new_with_quantifiers()`](Self::try_new_with_quantifiers) instead.**
    ///
    /// This convenience constructor is intended for test and bench code.
    #[cfg(test)]
    pub fn new_with_quantifiers() -> Self {
        Self::try_new_with_quantifiers().expect(
            "failed to create ay solver for AUFLIA logic in AYEncoder::new_with_quantifiers()",
        )
    }

    /// Try to create a new encoder with quantified logic support.
    pub fn try_new_with_quantifiers() -> Result<Self, EncodingError> {
        Self::try_new_internal(Logic::Auflia)
    }

    /// Create a new encoder with `ALL` logic (panics on failure).
    ///
    /// # Panics
    ///
    /// Panics if the ay solver cannot be created. **Production code should use
    /// [`try_new_all()`](Self::try_new_all) instead.**
    ///
    /// This convenience constructor is intended for test and bench code.
    #[cfg(test)]
    pub fn new_all() -> Self {
        Self::try_new_all()
            .expect("failed to create ay solver for ALL logic in AYEncoder::new_all()")
    }

    /// Try to create a new encoder with `ALL` logic.
    pub fn try_new_all() -> Result<Self, EncodingError> {
        Self::try_new_internal(Logic::All)
    }

    /// Create a new encoder for pure formulas with quantifier support (panics on failure).
    ///
    /// # Panics
    ///
    /// Panics if the ay solver cannot be created. **Production code should use
    /// [`try_new_pure_with_quantifiers()`](Self::try_new_pure_with_quantifiers) instead.**
    ///
    /// This convenience constructor is intended for test and bench code.
    #[cfg(test)]
    pub fn new_pure_with_quantifiers() -> Self {
        Self::try_new_pure_with_quantifiers().expect(
            "failed to create ay solver for UFLIA logic in AYEncoder::new_pure_with_quantifiers()",
        )
    }

    /// Try to create a new encoder for pure formulas with quantifier support.
    pub fn try_new_pure_with_quantifiers() -> Result<Self, EncodingError> {
        Self::try_new_pure_internal(Logic::Uflia)
    }

    /// Create a new encoder for pure arithmetic formulas only (panics on failure).
    ///
    /// # Panics
    ///
    /// Panics if the ay solver cannot be created. **Production code should use
    /// [`try_new_pure()`](Self::try_new_pure) instead.**
    ///
    /// This convenience constructor is intended for test and bench code.
    #[cfg(test)]
    pub fn new_pure() -> Self {
        Self::try_new_pure()
            .expect("failed to create ay solver for QF_LIA logic in AYEncoder::new_pure()")
    }

    /// Try to create a new encoder for pure arithmetic formulas only.
    pub fn try_new_pure() -> Result<Self, EncodingError> {
        Self::try_new_pure_internal(Logic::QfLia)
    }

    fn from_solver_and_mem_state(
        solver: Solver,
        mem_state: MemState,
        logic: Logic,
        supports_quantifiers: bool,
        #[cfg(test)] _solver_permit: super::test_solver_limiter::SolverPermit,
    ) -> Self {
        let mut seq_state = SeqState::new();
        // The Seq carrier chosen here is the encoder's single answer to "what
        // sort is a sequence". It has to be, because two paths mint Seq sorts:
        // `ensure_seq_theory` declares `seq_len`/`seq_index_logic`/… over
        // `SeqState`'s carrier, while the sort plan (plan/preseed/
        // var_collection) declares the *variables* those projectors are
        // applied to. When they disagree, `Solver::apply` fails its
        // domain-sort check.
        //
        // They no longer can. `SeqCarrier` is threaded from here to the
        // stateless converter (`expr_sort_to_ay_sort_for_carrier`) and to the
        // plan's declaration boundary (`SortPlan::apply`), so choosing a
        // carrier here chooses it for the whole encoding session. Before that
        // threading existed the stateless side hard-coded native `(Seq Int)`,
        // which is why 8f30b1b's attempt to put UFLIA on the uninterpreted
        // carrier split the sort and had to be reverted.
        //
        // `Logic::All` is the one lane whose carrier is decided by the *logic*:
        // ay-dpll rejects native `Seq` + native datatypes as an unsupported
        // mixed collection fragment, so a mixed VC cannot use the native sort
        // at all. That is also why it withholds the array-backed `index_logic`
        // bridge axiom — see `SeqState::force_uninterpreted_sort`.
        //
        // The certifiability-driven carrier choice does NOT belong here, even
        // though UFLIA is the lane that needs it. `new_pure_with_quantifiers()`
        // is UFLIA, and it is also the bench the encoder's own unit tests build
        // Seq terms on by hand with a literal `Sort::seq(Sort::Int)`. Choosing
        // the carrier by logic therefore breaks those tests no matter how
        // completely the carrier is threaded, because the sort they construct
        // is a hard-coded literal in the test body. The choice belongs to the
        // verification track instead: see
        // `AYEncoder::use_certifiable_seq_carrier`.
        if matches!(logic, Logic::All) {
            seq_state.force_uninterpreted_sort();
        }
        Self {
            solver,
            mem_state,
            var_env: VarEnv::new(),
            decls: DeclarationState::new(),
            #[cfg(any(test, feature = "sep-logic"))]
            sep_cache: SepConjCache::new(),
            assertion_pipeline: AssertionPipelineState::new(),
            sort_resolver: SortResolverState::new(),
            quantifier_state: QuantifierState::new(),
            seq_state,
            traversal: TraversalState::with_logic(logic, supports_quantifiers),
            ground_pool: GroundTermPool::new(),
            fmap_quantified_coverage:
                super::ground_pool::retirement::FmapQuantifiedCoverage::default(),
            retirement_stage_override: None,
            adt_state: AdtState::new(),
            struct_field_alias_axioms: std::collections::HashSet::new(),
            permutation_exchange_axioms: std::collections::HashSet::new(),
            struct_field_ground_applications: Vec::new(),
            closure_mapping_axioms: Vec::new(),
            enum_payload_bridge_forall_terms: Vec::new(),
            datatype_selector_bridges: std::collections::HashMap::new(),
            injective_bridge_ground_terms: std::collections::HashMap::new(),
            closure_state: ClosureState::new(),
            direct_view_fns: Vec::new(),
            view_return_fns: Vec::new(),
            arithmetic_mode: ArithmeticModeState::new(),
            encoding_cache: EncodingCacheState::new(),
            replay_recorder: ReplayRecorder::new("trust-wp-ay"),
            #[cfg(test)]
            _solver_permit,
        }
    }

    fn try_new_with_memory(
        logic: Logic,
        init_memory: impl FnOnce(&mut Solver) -> MemState,
    ) -> Result<Self, EncodingError> {
        // In test builds, acquire a permit from the global solver limiter
        // BEFORE creating the solver. This blocks if the concurrent solver
        // limit has been reached, preventing OOM from too many simultaneous
        // solver instances. The permit is stored in the encoder and released
        // on drop. (#2710)
        #[cfg(test)]
        let solver_permit = super::test_solver_limiter::acquire_solver_permit();

        let supports_quantifiers = matches!(logic, Logic::Auflia | Logic::Uflia | Logic::All);
        let mut solver = Solver::try_new(logic).map_err(|err| {
            EncodingError::solver_error(format!(
                "failed to create solver for logic {logic:?}: {err}"
            ))
        })?;
        // Enable unsat-core production so vacuity checking can inspect
        // which named assertions participated in an UNSAT proof. (#2414)
        solver
            .try_set_option(":produce-unsat-cores", "true")
            .map_err(|err| {
                EncodingError::solver_error(format!(
                    "failed to enable unsat-core production for logic {logic:?}: {err}"
                ))
            })?;
        // Keep proof production opt-in on the long-lived incremental encoder:
        // proof reconstruction can dominate ordinary queries. Authority lanes
        // use isolated strict replay and attach its artifact; an uncertified
        // `Verified(None)` is downgraded at every public boundary. (#2629)
        solver.set_produce_proofs(false);
        // Raise the E-matching round budget for quantifier-bearing proof
        // obligations. Iterator/permutation specs chain quantifier
        // instantiations several axioms deep (the output of round N only
        // becomes matchable in round N+1), so the default budget truncates
        // before the chain saturates. ay clamps to its ceiling and the solve
        // deadline still bounds wall-clock time, so this stays terminating.
        if supports_quantifiers {
            solver.set_ematching_round_limit(32);
        }
        let mem_state = init_memory(&mut solver);
        Ok(Self::from_solver_and_mem_state(
            solver,
            mem_state,
            logic,
            supports_quantifiers,
            #[cfg(test)]
            solver_permit,
        ))
    }

    /// Internal constructor with configurable logic and default memory model.
    fn try_new_internal(logic: Logic) -> Result<Self, EncodingError> {
        Self::try_new_with_memory(logic, BaseMemoryModel::init)
    }

    /// Internal constructor for pure encoders that don't declare heap arrays.
    fn try_new_pure_internal(logic: Logic) -> Result<Self, EncodingError> {
        Self::try_new_with_memory(logic, |solver| {
            // Create dummy array terms (won't actually be used for pure formulas).
            // These placeholders keep the encoder struct consistent.
            BaseMemoryModel::init_pure(solver)
        })
    }
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::{Logic, SolveResult, Sort};
    use ntest::timeout;

    use super::*;

    // ── QF_AUFLIA constructors ───────────────────────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_new_creates_qf_auflia_encoder() {
        let encoder = AYEncoder::new();
        assert_eq!(
            encoder.traversal.logic,
            Logic::QfAuflia,
            "new() should create a QF_AUFLIA encoder"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_try_new_returns_ok() {
        let result = AYEncoder::try_new();
        assert!(result.is_ok(), "try_new() should succeed");
        let encoder = result.unwrap();
        assert_eq!(encoder.traversal.logic, Logic::QfAuflia);
    }

    #[test]
    #[timeout(30000)]
    fn test_new_does_not_support_quantifiers() {
        let encoder = AYEncoder::new();
        assert!(
            !encoder.traversal.supports_quantifiers,
            "QF_AUFLIA encoder should not support quantifiers"
        );
    }

    // ── AUFLIA (quantifier) constructors ─────────────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_new_with_quantifiers_creates_auflia_encoder() {
        let encoder = AYEncoder::new_with_quantifiers();
        assert_eq!(
            encoder.traversal.logic,
            Logic::Auflia,
            "new_with_quantifiers() should create an AUFLIA encoder"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_try_new_with_quantifiers_returns_ok() {
        let result = AYEncoder::try_new_with_quantifiers();
        assert!(result.is_ok(), "try_new_with_quantifiers() should succeed");
        let encoder = result.unwrap();
        assert!(
            encoder.traversal.supports_quantifiers,
            "AUFLIA encoder should support quantifiers"
        );
    }

    // ── ALL logic constructors ───────────────────────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_new_all_creates_all_logic_encoder() {
        let encoder = AYEncoder::new_all();
        assert_eq!(
            encoder.traversal.logic,
            Logic::All,
            "new_all() should create an ALL-logic encoder"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_new_all_supports_quantifiers() {
        let encoder = AYEncoder::new_all();
        assert!(
            encoder.traversal.supports_quantifiers,
            "ALL-logic encoder should support quantifiers"
        );
    }

    // ── Pure (QF_LIA) constructors ───────────────────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_new_pure_creates_qf_lia_encoder() {
        let encoder = AYEncoder::new_pure();
        assert_eq!(
            encoder.traversal.logic,
            Logic::QfLia,
            "new_pure() should create a QF_LIA encoder"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_new_pure_does_not_support_quantifiers() {
        let encoder = AYEncoder::new_pure();
        assert!(
            !encoder.traversal.supports_quantifiers,
            "QF_LIA encoder should not support quantifiers"
        );
    }

    // ── Pure with quantifiers (UFLIA) constructors ───────────────────────

    #[test]
    #[timeout(30000)]
    fn test_new_pure_with_quantifiers_creates_uflia_encoder() {
        let encoder = AYEncoder::new_pure_with_quantifiers();
        assert_eq!(
            encoder.traversal.logic,
            Logic::Uflia,
            "new_pure_with_quantifiers() should create a UFLIA encoder"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_new_pure_with_quantifiers_supports_quantifiers() {
        let encoder = AYEncoder::new_pure_with_quantifiers();
        assert!(
            encoder.traversal.supports_quantifiers,
            "UFLIA encoder should support quantifiers"
        );
    }

    // ── Functional validation ────────────────────────────────────────────

    #[test]
    #[timeout(30000)]
    fn test_new_encoder_check_sat_is_sat() {
        let mut encoder = AYEncoder::new();
        assert_eq!(
            encoder.check_sat(),
            SolveResult::Sat,
            "fresh encoder with no assertions should be SAT"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_pure_encoder_can_do_arithmetic() {
        let mut encoder = AYEncoder::new_pure();
        let x = encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declaring Int var should succeed");
        let five = encoder.solver.int_const(5);
        let eq = encoder.solver.eq(x, five);
        encoder.solver.assert_term(eq);
        assert_eq!(
            encoder.check_sat(),
            SolveResult::Sat,
            "x == 5 should be SAT in pure arithmetic encoder"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_encoder_contradiction_is_unsat() {
        let mut encoder = AYEncoder::new();
        let t = encoder.solver.bool_const(true);
        let f = encoder.solver.bool_const(false);
        encoder.solver.assert_term(t);
        encoder.solver.assert_term(f);
        assert_eq!(
            encoder.check_sat(),
            SolveResult::unsat(),
            "true AND false should be UNSAT"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_encoder_initial_state_clean() {
        let encoder = AYEncoder::new();
        assert_eq!(
            encoder.traversal.recursion_depth, 0,
            "fresh encoder should have zero recursion depth"
        );
        assert!(
            encoder.traversal.path_conditions.is_empty(),
            "fresh encoder should have empty path conditions"
        );
        assert!(
            encoder.arithmetic_mode.division_obligations().is_empty(),
            "fresh encoder should have no division obligations"
        );
        assert!(
            !encoder.arithmetic_mode.total_int_arithmetic(),
            "fresh encoder should not have total_int_arithmetic set"
        );
    }
}
