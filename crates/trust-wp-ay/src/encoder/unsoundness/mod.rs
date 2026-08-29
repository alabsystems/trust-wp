// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unsoundness tracking for encoding approximations (#2106).
//!
//! When the encoder falls back to an approximation (sort fallback, panic recovery,
//! opaque call assumption, etc.), it increments a thread-local counter for the
//! relevant category. The verification layer snapshots counters before each function,
//! computes the delta after, and demotes `Verified` results to `Unknown` when
//! demoting categories fired.
//!
//! Design: `designs/2026-03-08-unsoundness-demotion-pipeline.md`
//! Reference: trust-mc's `unsoundness_fields.rs` + `unsoundness_per_harness.rs`

use std::{cell::RefCell, collections::HashMap, fmt};

use tracing::debug;

/// Risk level for an unsoundness category.
///
/// Formalizes the HIGH/MEDIUM/LOW/ELIMINATED classification that was
/// previously only tracked in comments. Used by `UnsoundnessCategory::risk_level()`
/// and test assertions to prevent silent reclassification. (#2663)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RiskLevel {
    /// Can produce false proofs. Demotes `Verified` to `Unknown`.
    High,
    /// Can produce false proofs in edge cases. Also demoting.
    Medium,
    /// Conservative approximation — can cause false counterexamples but not false proofs.
    /// Non-demoting.
    Low,
    /// No production code increments this category. Retained for backward compat.
    /// Non-demoting.
    Eliminated,
}

impl RiskLevel {
    /// Whether this risk level causes demotion of `Verified` results.
    #[must_use]
    pub fn is_demoting(self) -> bool {
        matches!(self, Self::High | Self::Medium)
    }
}

impl fmt::Display for RiskLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::High => write!(f, "HIGH"),
            Self::Medium => write!(f, "MEDIUM"),
            Self::Low => write!(f, "LOW"),
            Self::Eliminated => write!(f, "ELIMINATED"),
        }
    }
}

/// Categories of encoding approximations that may affect proof validity.
///
/// Categories are split into three risk levels:
/// - **HIGH** (demoting): Can produce false proofs (Verified → Unknown)
/// - **MEDIUM** (demoting): Can produce false proofs in edge cases
/// - **LOW** (conservative): Can produce false counterexamples but not false proofs
///
/// See R1-189 audit for the full category catalog with file locations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UnsoundnessCategory {
    // --- HIGH risk (DEMOTING) ---
    /// Call postcondition assumption failed to encode; return value unconstrained.
    /// Site: `encoder/pure_encoding.rs` LetAssume error path.
    LetAssumeDropped,
    /// Logic function postcondition axiom failed to encode; callers unconstrained.
    /// Site: `encoder/logic_fn/mod.rs` spec axiom error path.
    SpecAxiomDropped,
    /// Variable sort resolved to `Sort::Int` when a more specific sort was expected.
    /// Bool→Int causes `eq` instead of `iff`, making equality unconstrained.
    /// Sites: `encoder/sep_logic.rs`, `verify/mut_borrow/resolve.rs`, `encoder/operators.rs`.
    SortFallbackToInt,
    /// ELIMINATED (#2541): closure body no longer defaults to `Bool(true)`.
    /// Missing bodies are stored as `None` and ensures-only inlining is used
    /// when the contract constrains `result`; otherwise the UF fallback runs.
    /// Retained in the enum for test backward compatibility only.
    /// Reclassified non-demoting: no production code increments this category.
    /// Former site: `encoder/closure_inline.rs`.
    ClosureBodyTrueDefault,
    /// ELIMINATED (#2666): BV mode is now always-on in production
    /// (`per_contract.rs` hardcodes `bitwise_proof: true`). Bitwise operations
    /// use ay's native BV theory via `encode_int_binop_bv` instead of UF
    /// approximations. The legacy UF fallback path (`encode_int_binop_uf`)
    /// still exists for test backward compatibility but is unreachable in
    /// production. Retained in the enum for backward compat only.
    /// Reclassified non-demoting: no production code increments this category.
    /// Former site: `encoder/operators.rs` shift/bitwise handlers.
    BitwiseUfApproximation,
    /// Opaque function call with no spec available.
    ///
    /// **Historical name:** "TrueAssumption" reflects the original behavior where
    /// opaque calls assumed `postcondition = true`. The current implementation
    /// uses Creusot's `requires(false)` pattern: a `Bool(false)` obligation is
    /// injected, making the caller's proof impossible (fail-closed).
    ///
    /// **Encoding-level guard (#2663):** `encode_let_obligation` now detects
    /// constant-false obligations and returns an `EncodingError`, preventing the
    /// non-Bool body path from asserting `false` as a solver fact (which would
    /// make the context trivially UNSAT → false "Verified"). This blocks the
    /// primary unsoundness vector. The counter is retained for demotion as a
    /// defense-in-depth measure — the encoding guard is the primary safety net.
    ///
    /// Site: `trust-wp-driver/.../call_spec/fallback.rs` handle_opaque_call.
    OpaqueCallTrueAssumption,
    /// A `Final` (`^x`) collapse to the current-value carrier was REFUSED
    /// because the carrier's sort (transitively) embeds a mutable reference —
    /// or could not be proven not to (fail-closed). Collapsing `^x` to `x` is
    /// exact only for pure values; on `&mut`-embedding carriers (match binders
    /// over `Option<&mut T>` payloads, ADT-embedded `&mut` fields) no prophecy
    /// slot exists and the collapse would assert the false premise/goal
    /// `^x == *x` — the take_first_mut adjudicated false accept (Final-collapse
    /// audit 2026-08-05). The refusal produces an `EncodingError::unsupported`
    /// (premise-side: assumption dropped via the LetAssumeDropped /
    /// requires-error lane; goal-side: honest obligation failure) and this
    /// counter guarantees demotion even if some path absorbs the error.
    /// Site: `encoder/final_collapse_guard.rs` refuse_final_collapse (called
    /// from the wrapper.rs Phase-1/Phase-1b Final guards).
    FinalCollapseRefused,
    /// Integer cast (`as u8`, `as i32`, etc.) treated as identity in the SMT
    /// encoding. trust-wp models all integers as unbounded mathematical integers,
    /// so narrowing casts (e.g., `300_u32 as u8`) silently drop truncation /
    /// wrapping semantics. This can produce false proofs when a postcondition
    /// depends on the cast target's bit width.
    ///
    /// **Partially addressed by #2666:** When the target type is known at
    /// MIR extraction time (the common case), the driver now emits a
    /// `__trust_wp_int_truncate_{s|u}{bits}` LogicFnCall that the encoder
    /// intercepts and routes to `encode_int_truncation_bv`, giving exact
    /// modular truncation semantics via BV theory. This counter only fires
    /// for the fallback case where the target type cannot be determined.
    ///
    /// Previously unsound patterns (now handled by BV truncation):
    /// - **Narrowing**: `x as u8` where `x > 255` — real Rust truncates to `x % 256`.
    /// - **Sign change**: `(-1_i32) as u32` — real Rust wraps to `u32::MAX`.
    /// - **Widening** (benign): `x as u32` where `x: u8` — value-preserving.
    ///
    /// Site: `trust-wp-driver/src/mir_analysis/translate/rvalue.rs` CastKind::IntToInt fallback.
    /// Tracked: #938, #2666.
    IntegerCastIdentity,
    /// A closure in logic context had no faithful encoding, so an OPAQUE
    /// `Bool`-sorted constant was substituted for the closure *value*
    /// (`encode_closure_in_logic`'s last-resort fallback: multi-parameter
    /// closures, and single-parameter closures outside Mapping context).
    ///
    /// The substituted constant is unconstrained — which by itself is only a
    /// weakening — but its `Bool` sort is ARBITRARY (chosen because logic-context
    /// closures are usually predicates) and it propagates: applying the closure
    /// yields a `Bool`-returning UF, and any arithmetic use of that application
    /// is then promoted through `bool_to_int`'s `ite(b, 1, 0)`. That promotion
    /// FABRICATES the premise "this value is in {0, 1}" for a closure whose real
    /// return type is unbounded, which makes FALSE postconditions valid.
    ///
    /// Demonstrated on `lang/unsized_quant` (`let len = |x: [i32]| x@.len()`):
    /// `forall<x> len[x] <= 1` — flatly false — encodes to
    /// `(forall ((x U_Seq)) (<= (ite (idx closure x) 1 0) 1))`, which is valid.
    /// Live trust-wp does not currently accept it only because ay declines the
    /// nested-quantifier shape; that masking is being removed upstream by ay's
    /// trust-to-zero programme, so this is a LATENT FALSE ACCEPT, not a
    /// hypothetical. Booked as HIGH so no obligation encoded on top of a
    /// fabricated closure value can ever be reported `Verified`.
    ///
    /// Previously this site incremented the LOW / non-demoting
    /// `UnsupportedConstructSkip`, which does not demote — the only
    /// `UnsupportedConstructSkip` site that continued encoding with a
    /// synthesized value instead of returning an `EncodingError`.
    ///
    /// Site: `encoder/pure_encoding/mod.rs` encode_closure_in_logic fallback.
    OpaqueClosureValueFallback,

    // --- MEDIUM risk (DEMOTING in edge cases) ---
    /// `eq_or_iff` panic recovery inserted `bool_const(false)`.
    /// In negated-postcondition context, `false` in a conjunct → trivially UNSAT → false Verified.
    /// Site: `encoder/solver.rs` eq_or_iff catch_unwind.
    PanicRecoveryFalse,
    /// Postcondition references `result` but no `return_expr` was provided by
    /// the driver. The SMT variable `result` is auto-declared as an
    /// unconstrained free variable, allowing the solver to pick any value that
    /// satisfies the postcondition — producing false proofs.
    ///
    /// Reclassified from `SortFallbackToInt` (HIGH) to MEDIUM: the unsoundness
    /// requires a specific precondition (missing return_expr + result-referencing
    /// postcondition), unlike the general sort fallback which is pervasive. The
    /// demotion still fires, preventing false proofs. (#2663)
    ///
    /// Sites: `verify/function/result_binding.rs`(1), `verify/mut_borrow/mod.rs`(1).
    UnconstrainedResultVar,
    /// Logic function call without return-type annotation defaulted to `Sort::Int`.
    /// Bool-returning user logic functions can escape name-based detection,
    /// so the remaining fallback can still change `eq` into `iff`-sensitive
    /// behavior at call sites. Reclassified MEDIUM-demoting after #2320 added
    /// explicit return-sort threading but left the fallback path for truly
    /// unknown calls.
    /// Site: `sort_context/sort_inference.rs` LogicFnCall catch-all.
    SortFallbackToIntFromLogicFn,

    // --- LOW risk (conservative approximations) ---
    /// Unsupported MIR construct silently skipped with warning.
    /// Sites: `encoder/mod.rs` unsupported feature handlers,
    /// `encoder/match_enc/mod.rs` datatype declare-collision skip (#2706).
    UnsupportedConstructSkip,
    /// `catch_solver_panic_with_reason()` caught a ay panic during encoding.
    /// Site: `encoder/type_resolve.rs` catch_unwind wrapper.
    CatchUnwindFallback,
    /// Closure law / resolve axiom construction was skipped after a selector or
    /// `axiom_apply` mismatch. This weakens premises (more Unknowns) but does
    /// not synthesize stronger proof obligations.
    /// Sites: `encoder/closure_axioms/*.rs`.
    ClosureAxiomSkipped,
    /// Variable without explicit sort annotation defaulted to `Sort::Int`.
    /// For integer-valued variables (the vast majority), this is correct.
    /// Only risky for Bool-sorted variables where `eq` vs `iff` matters,
    /// but those are typically caught by `register_formula_sort_hints`.
    /// Split from `SortFallbackToInt` per #2202.
    /// Sites: `sort_context/sort_inference.rs` Var(_, None), `verify/mod.rs` param_sort None.
    SortFallbackToIntFromVar,
    /// Type invariant short-circuited to `true` when all registered invariants trivial.
    /// Provably sound identity transform: if body IS `true`, constant `true` is exact.
    /// Reclassified LOW per #2201.
    /// Site: `encoder/method_call/mod.rs` invariant handler.
    InvariantTrueShortCircuit,
    /// Known Int-returning method call (`len`, `get`, `index_logic`, etc.) defaulted
    /// to `Sort::Int`. These methods provably return integer values; the fallback is
    /// the correct sort inference, not an approximation.
    /// Split from `SortFallbackToInt` per #2202 AC2.
    /// Site: `sort_context/sort_inference.rs` MethodCall known-Int arm.
    SortFallbackToIntFromMethodCall,
    /// Non-Bool term coerced to Bool for logical operators (And, Or, Not, Implies).
    /// Int→Bool via `!= 0` is the C/Rust convention; non-Int/non-Bool → fresh Bool
    /// constant is a sound over-approximation. Neither path can produce false proofs:
    /// Int→Bool preserves truthiness, fresh Bool is unconstrained (conservative).
    /// Split from `SortFallbackToIntFromLogicFn` per #2359 — Bool coercion is
    /// benign and common, sharing a demoting counter caused massive false demotions.
    /// Site: `encoder/operators.rs` coerce_bool_operand.
    BoolCoercionFromNonBool,
    /// Variable sort was upgraded/downgraded mid-encoding, creating a phantom
    /// `{name}__upgraded` SMT constant. Prior assertions against the old constant
    /// are disconnected from the new one. Weakens proof search but does not
    /// directly produce false proofs.
    /// Sites: `encoder/var_declare.rs` upgrade/downgrade paths. (#2567)
    PhantomVariableUpgrade,
    /// Sort coercion bridge created a fresh unconstrained constant to bridge
    /// between heterogeneous sorts in `ite`/`eq` expressions. The fresh
    /// constant is unconstrained — the solver cannot derive any conclusions
    /// from it — so this is strictly conservative (weakens proof search but
    /// cannot produce false proofs). Examples: Unit vs Tuple2 branch sorts,
    /// Bool vs Datatype comparison, Int vs complex sort in match arms.
    /// Reclassified from `SortFallbackToInt` (HIGH) to LOW per #2231.
    /// Sites: `encoder/sort_context/sort_coercion.rs` coerce_ite_sorts.
    SortCoercionBridge,
    /// An equality in ASSUMPTION position (precondition, `LetAssume`
    /// assumption, path-condition fact) could not be encoded and was replaced
    /// by a polarity-neutral fresh Bool (`__trust_wp_unencodable_eq_*`) —
    /// i.e. a premise was fabricated away. The weakened assumption base is
    /// strictly conservative for PROOFS (a proof from fewer premises is still
    /// a proof — non-demoting for `Verified`), but any subsequent
    /// `Failed(Counterexample)` verdict is untrustworthy: the model may only
    /// exist because a real premise vanished (arc_and_rc `rc3@ == 2` false
    /// reject). `demote_if_unsound` has a dedicated fail-closed arm that
    /// converts `Failed` to `Unknown(Demoted)` when this category fired.
    /// Goal-side (negated-postcondition) fabrications do NOT increment this
    /// category — the placeholder is unprovable there, which is exactly the
    /// conservative behavior, and expected-failure verdicts must survive.
    /// Site: `encoder/solver.rs` `fresh_unencodable_eq_bool` (gated on
    /// assumption position).
    PremiseNeutralizedEq,
    /// `#[non_exhaustive]` catch-all guard in sort inference. Currently
    /// unreachable — all variants of BinOp, UnOp, PureExpr, and ExprSort
    /// are matched explicitly. Retained as defense-in-depth: a new variant
    /// without sort inference would silently default to Int.
    /// Reclassified from `SortFallbackToInt` (HIGH) to LOW per #2663
    /// Phase 1a audit — the catch-all is future-proofing, not a current risk.
    /// Sites: `sort_context/sort_inference.rs`(3) BinOp/UnOp/PureExpr,
    ///        `sort_context/sort_mapping.rs`(1) ExprSort.
    SortFallbackToIntFromCatchAll,
}

impl UnsoundnessCategory {
    /// Whether this category can produce false-positive increments during
    /// encoder bootstrap (sort-hint registration, logic function declaration,
    /// type invariant registration) — before precondition encoding begins.
    ///
    /// Bootstrap runs `infer_expr_sort` on `LogicFnCall` nodes before the
    /// corresponding declarations exist, triggering harmless fallback
    /// increments. These false positives must be absorbed into the demotion
    /// baseline so they do not cause spurious demotions. (#2623)
    ///
    /// Add new categories here as they are identified (currently only
    /// `SortFallbackToIntFromLogicFn`). This replaces the hardcoded
    /// single-category check in `merge_pre_verification_and_post_bootstrap_snapshots`.
    #[must_use]
    pub fn has_bootstrap_false_positives(self) -> bool {
        matches!(self, Self::SortFallbackToIntFromLogicFn)
    }

    /// Formal risk level for this category. (#2663)
    ///
    /// Returns the risk classification that determines demotion behavior.
    /// HIGH and MEDIUM are demoting; LOW and ELIMINATED are not.
    #[must_use]
    pub fn risk_level(self) -> RiskLevel {
        match self {
            // --- HIGH risk (DEMOTING) ---
            Self::LetAssumeDropped
            | Self::SpecAxiomDropped
            | Self::SortFallbackToInt
            | Self::OpaqueCallTrueAssumption
            | Self::FinalCollapseRefused
            | Self::IntegerCastIdentity
            | Self::OpaqueClosureValueFallback => RiskLevel::High,

            // --- MEDIUM risk (DEMOTING in edge cases) ---
            Self::PanicRecoveryFalse
            | Self::SortFallbackToIntFromLogicFn
            | Self::UnconstrainedResultVar => RiskLevel::Medium,

            // --- ELIMINATED (no production sites) ---
            Self::ClosureBodyTrueDefault | Self::BitwiseUfApproximation => RiskLevel::Eliminated,

            // --- LOW risk (conservative approximations) ---
            Self::UnsupportedConstructSkip
            | Self::CatchUnwindFallback
            | Self::ClosureAxiomSkipped
            | Self::SortFallbackToIntFromVar
            | Self::InvariantTrueShortCircuit
            | Self::SortFallbackToIntFromMethodCall
            | Self::BoolCoercionFromNonBool
            | Self::PhantomVariableUpgrade
            | Self::SortCoercionBridge
            // PremiseNeutralizedEq weakens premises: conservative for proofs
            // (non-demoting for Verified) but poisons counterexample verdicts
            // — handled by the dedicated Failed arm in demote_if_unsound.
            | Self::PremiseNeutralizedEq
            | Self::SortFallbackToIntFromCatchAll => RiskLevel::Low,
        }
    }

    /// Whether this category can produce false proofs (vs only false counterexamples).
    ///
    /// All HIGH and MEDIUM risk categories are demoting. LOW risk categories
    /// are conservative — they may cause false failures but not false proofs.
    #[must_use]
    pub fn is_demoting(self) -> bool {
        self.risk_level().is_demoting()
    }

    /// Whether this category has been eliminated (no production increment sites).
    ///
    /// Eliminated categories are retained in the enum for backward compatibility
    /// but should never fire in production. A test asserts this invariant. (#2663)
    #[must_use]
    pub fn is_eliminated(self) -> bool {
        self.risk_level() == RiskLevel::Eliminated
    }

    /// Expected number of production `unsoundness::increment()` call sites
    /// for this category. (#2663)
    ///
    /// This is a soundness lock: adding a new increment site for a demoting
    /// category requires explicit acknowledgment by updating this count.
    /// Tests validate that the actual count in the source matches this value.
    ///
    /// Counts exclude test files -- only production code paths are tracked.
    #[must_use]
    pub fn expected_production_sites(self) -> usize {
        match self {
            // HIGH demoting — each site can produce false proofs
            Self::LetAssumeDropped => 2, // pure_encoding/bindings.rs(1), path_conditions.rs(1)
            Self::SpecAxiomDropped => 3, // logic_fn/registration.rs(2): :786, :807
            // + verify/function/mod.rs(1): :1282 (coerced one-step unfolding
            // guard). The previous count of 1 was stale — the extra sites
            // already existed, only the lock lagged.
            Self::SortFallbackToInt => 2, // 2 GENUINE: operators.rs Eq/Ne fallback
            // (4 former catch-all guards reclassified to
            // SortFallbackToIntFromCatchAll per #2663)
            Self::OpaqueCallTrueAssumption => 1, // NEUTRALIZED: requires(false) injected
            // trust-wp-driver: call_spec/fallback.rs(1)
            Self::FinalCollapseRefused => 2, // final_collapse_guard.rs: refuse_final_collapse
            // (sort-based arm; wrapper.rs Phase-1/1b Final guards route through
            // it) + refuse_prophecy_over_constant (constant-carrier arm,
            // tract19: `^<literal>` in encode_wrapper_rewrite; the sort guard
            // cannot see it because a literal's sort is a pure value)
            Self::IntegerCastIdentity => 1, // PARTIALLY ADDRESSED: BV truncation
            // trust-wp-driver: translate/rvalue.rs(1)
            Self::OpaqueClosureValueFallback => 1, // GENUINE: pure_encoding/mod.rs(1)
            // encode_closure_in_logic last-resort opaque Bool closure value
            // MEDIUM demoting — edge-case false proofs
            Self::PanicRecoveryFalse => 3, // solver.rs(3): eq_term, eq_or_iff, safe_ite
            Self::SortFallbackToIntFromLogicFn => 2, // logic_fn_sort.rs(1), resolution.rs(1)
            Self::UnconstrainedResultVar => 2, // result_binding.rs(1), mut_borrow/mod.rs(1)
            // ELIMINATED — zero production sites
            Self::ClosureBodyTrueDefault | Self::BitwiseUfApproximation => 0,
            // LOW — non-demoting, tracked for observability
            Self::UnsupportedConstructSkip => 4, // error.rs(3 factory methods),
            // match_enc/mod.rs(1) declare-collision skip. (Was 5: the
            // pure_encoding/mod.rs closure-value fallback moved to the
            // demoting OpaqueClosureValueFallback — vacfix.)
            Self::CatchUnwindFallback => 1,      // type_resolve.rs(1)
            Self::ClosureAxiomSkipped => 1,      // closure_axioms/mod.rs(1)
            Self::SortFallbackToIntFromVar => 8, // sort_inference.rs(1), resolution.rs(2),
            // verify/mod.rs(1), mut_borrow/resolve.rs(4)
            Self::InvariantTrueShortCircuit => 3, // method_call/bool_uf.rs(3)
            Self::SortFallbackToIntFromMethodCall => 13, // method_call_sort.rs(13)
            Self::BoolCoercionFromNonBool => 1,   // operators.rs(1)
            Self::PhantomVariableUpgrade => 8,    // var_declare.rs(7), seq_synth.rs(1)
            Self::SortCoercionBridge => 15,       // sort_coercion.rs(10), placeholder.rs(1),
            // match_enc/pattern_condition(2), seq/operations.rs(1),
            // verify/loops/variant.rs(1)
            Self::PremiseNeutralizedEq => 1, // solver.rs fresh_unencodable_eq_bool
            // (assumption-position gated)
            Self::SortFallbackToIntFromCatchAll => 4, // sort_inference.rs(3) BinOp/UnOp/PureExpr
                                                      // + sort_mapping.rs(1) ExprSort catch-alls
        }
    }

    /// Total expected production sites across all demoting categories. (#2663)
    ///
    /// This is a global soundness budget. Reducing this number means fewer
    /// places where false proofs can originate. The goal is to drive this
    /// to zero for each category over time.
    #[must_use]
    pub fn total_demoting_production_sites() -> usize {
        Self::ALL
            .iter()
            .filter(|c| c.is_demoting())
            .map(|c| c.expected_production_sites())
            .sum()
    }

    /// Mitigation status for each demoting category. (#2663 Phase 1 audit)
    ///
    /// Returns a human-readable summary of how each HIGH/MEDIUM category is
    /// mitigated in the current codebase. Used by soundness lock tests and
    /// audit reports to track progress toward eliminating false-proof vectors.
    ///
    /// Categories with `NEUTRALIZED` status have active mitigations that
    /// prevent false proofs even when the counter fires. Categories with
    /// `GENUINE` status represent real unsoundness vectors.
    #[must_use]
    pub fn mitigation_status(self) -> &'static str {
        match self {
            // --- HIGH ---
            Self::LetAssumeDropped => {
                "GENUINE: dropped let-assume leaves return value unconstrained. \
                 2 sites. No encoding-level mitigation — demotion is the safety net."
            }
            Self::SpecAxiomDropped => {
                "GENUINE: dropped spec axiom leaves callers unconstrained. \
                 1 site. No encoding-level mitigation — demotion is the safety net."
            }
            Self::SortFallbackToInt => {
                "GENUINE: 2 sites (operators.rs Eq/Ne) where \
                 select_structural_sort_target fails and Bool→Int causes eq \
                 instead of iff. Previously MIXED (4 of 6 sites were \
                 #[non_exhaustive] catch-all guards, now reclassified to \
                 SortFallbackToIntFromCatchAll per #2663 Phase 1a)."
            }
            Self::OpaqueCallTrueAssumption => {
                "NEUTRALIZED: requires(false) obligation injected at call site \
                 (#2663) makes caller's proof impossible (fail-closed). The counter \
                 still fires for demotion as defense-in-depth, but the encoding-level \
                 guard is the primary safety net. 1 site."
            }
            Self::IntegerCastIdentity => {
                "PARTIALLY ADDRESSED: BV truncation (#2666) handles narrowing/sign \
                 casts when target type is known (the common case). Counter only \
                 fires for the fallback where target type cannot be determined. \
                 1 site (translate/rvalue.rs)."
            }
            Self::OpaqueClosureValueFallback => {
                "GENUINE: the fallback substitutes an opaque Bool constant for a \
                 closure VALUE whose real return sort is unknown; downstream \
                 arithmetic use is promoted via ite(b,1,0), fabricating a {0,1} \
                 bound (lang/unsized_quant makes `forall<x> len[x] <= 1` valid). \
                 No encoding-level mitigation yet — demotion is the safety net. \
                 1 site (pure_encoding/mod.rs)."
            }
            Self::FinalCollapseRefused => {
                "NEUTRALIZED: the refusal sites themselves return an \
                 EncodingError::unsupported instead of performing the unsound \
                 ^x -> x collapse (fail-closed). The counter fires for demotion \
                 as defense-in-depth in case an intermediate layer absorbs the \
                 error. 2 sites (final_collapse_guard.rs): the sort-based arm \
                 and the constant-carrier arm (tract19), which closed a LIVE \
                 false accept where `^<literal>` folded to the literal."
            }
            // --- MEDIUM ---
            Self::PanicRecoveryFalse => {
                "GENUINE: panic recovery inserts bool(false) which in negated- \
                 postcondition context makes formula trivially UNSAT. 3 sites. \
                 Rare in practice — requires ay panic during encoding."
            }
            Self::SortFallbackToIntFromLogicFn => {
                "GENUINE with FALSE POSITIVES: logic fn sort inference catch-all. \
                 Bootstrap runs fire harmless increments that are absorbed into \
                 baseline. 2 sites. has_bootstrap_false_positives() returns true."
            }
            Self::UnconstrainedResultVar => {
                "GENUINE: missing return_expr with result-referencing postcondition \
                 leaves result unconstrained. 2 sites. Requires specific precondition \
                 (missing return_expr), hence MEDIUM not HIGH."
            }
            // Non-demoting categories
            _ => "N/A: non-demoting category",
        }
    }

    /// All defined categories, for exhaustive iteration in tests and cross-crate consumers.
    pub const ALL: &'static [UnsoundnessCategory] = &[
        Self::LetAssumeDropped,
        Self::SpecAxiomDropped,
        Self::SortFallbackToInt,
        Self::ClosureBodyTrueDefault,
        Self::BitwiseUfApproximation,
        Self::OpaqueCallTrueAssumption,
        Self::PanicRecoveryFalse,
        Self::UnconstrainedResultVar,
        Self::UnsupportedConstructSkip,
        Self::CatchUnwindFallback,
        Self::ClosureAxiomSkipped,
        Self::SortFallbackToIntFromVar,
        Self::InvariantTrueShortCircuit,
        Self::SortFallbackToIntFromLogicFn,
        Self::SortFallbackToIntFromMethodCall,
        Self::BoolCoercionFromNonBool,
        Self::PhantomVariableUpgrade,
        Self::IntegerCastIdentity,
        Self::SortCoercionBridge,
        Self::SortFallbackToIntFromCatchAll,
        Self::PremiseNeutralizedEq,
        Self::FinalCollapseRefused,
        Self::OpaqueClosureValueFallback,
    ];
}

impl fmt::Display for UnsoundnessCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LetAssumeDropped => write!(f, "let_assume_dropped"),
            Self::SpecAxiomDropped => write!(f, "spec_axiom_dropped"),
            Self::SortFallbackToInt => write!(f, "sort_fallback_to_int"),
            Self::ClosureBodyTrueDefault => write!(f, "closure_body_true_default"),
            Self::BitwiseUfApproximation => write!(f, "bitwise_uf_approximation"),
            Self::OpaqueCallTrueAssumption => write!(f, "opaque_call_true_assumption"),
            Self::PanicRecoveryFalse => write!(f, "panic_recovery_false"),
            Self::UnsupportedConstructSkip => write!(f, "unsupported_construct_skip"),
            Self::CatchUnwindFallback => write!(f, "catch_unwind_fallback"),
            Self::ClosureAxiomSkipped => write!(f, "closure_axiom_skipped"),
            Self::SortFallbackToIntFromVar => write!(f, "sort_fallback_to_int_from_var"),
            Self::InvariantTrueShortCircuit => write!(f, "invariant_true_short_circuit"),
            Self::SortFallbackToIntFromLogicFn => {
                write!(f, "sort_fallback_to_int_from_logic_fn")
            }
            Self::SortFallbackToIntFromMethodCall => {
                write!(f, "sort_fallback_to_int_from_method_call")
            }
            Self::BoolCoercionFromNonBool => write!(f, "bool_coercion_from_non_bool"),
            Self::PhantomVariableUpgrade => write!(f, "phantom_variable_upgrade"),
            Self::IntegerCastIdentity => write!(f, "integer_cast_identity"),
            Self::UnconstrainedResultVar => write!(f, "unconstrained_result_var"),
            Self::SortCoercionBridge => write!(f, "sort_coercion_bridge"),
            Self::SortFallbackToIntFromCatchAll => {
                write!(f, "sort_fallback_to_int_from_catch_all")
            }
            Self::PremiseNeutralizedEq => write!(f, "premise_neutralized_eq"),
            Self::FinalCollapseRefused => write!(f, "final_collapse_refused"),
            Self::OpaqueClosureValueFallback => {
                write!(f, "opaque_closure_value_fallback")
            }
        }
    }
}

/// Snapshot of unsoundness counters at a point in time.
pub type Snapshot = HashMap<UnsoundnessCategory, usize>;

thread_local! {
    static COUNTERS: RefCell<HashMap<UnsoundnessCategory, usize>> = RefCell::new(HashMap::new());
}

/// Increment the counter for an unsoundness category.
///
/// Call this at each encoding approximation site.
/// With `TRUST_WP_DEBUG=1`, prints caller location for base `SortFallbackToInt`
/// to help trace demoting fallback sites during compat harness runs (#994).
#[track_caller]
pub fn increment(category: UnsoundnessCategory) {
    COUNTERS.with(|c| *c.borrow_mut().entry(category).or_insert(0) += 1);
    if matches!(
        category,
        UnsoundnessCategory::SortFallbackToInt | UnsoundnessCategory::SortFallbackToIntFromLogicFn
    ) {
        let loc = std::panic::Location::caller();
        debug!(
            "[TRUST_WP_DEBUG] {category} at {}:{}:{}",
            loc.file(),
            loc.line(),
            loc.column()
        );
        // Unit tests run without a tracing subscriber, so `debug!` above is
        // invisible there. `TRUST_WP_UNSOUND_STDERR=1` routes the same caller
        // location to stderr for fallback-site triage in test binaries.
        if let Some(value) = std::env::var_os("TRUST_WP_UNSOUND_STDERR") {
            eprintln!(
                "[TRUST_WP_UNSOUND] {category} at {}:{}:{}",
                loc.file(),
                loc.line(),
                loc.column()
            );
            if value == "backtrace" {
                eprintln!("{}", std::backtrace::Backtrace::force_capture());
            }
        }
    }
}

/// Take a snapshot of current counter values.
///
/// Call before function verification to establish a baseline.
#[must_use]
pub fn snapshot() -> Snapshot {
    COUNTERS.with(|c| c.borrow().clone())
}

/// Reset all counters to zero.
///
/// Call at the start of a verification session.
pub fn reset() {
    COUNTERS.with(|c| c.borrow_mut().clear());
}

/// Merge counter increments from another thread into the current thread.
///
/// `run_with_hard_timeout` executes solver work on a fresh worker thread, so
/// the worker snapshot is itself the delta that must be applied back onto the
/// caller thread before `demote_if_unsound` computes its post-verification
/// snapshot. (#2431)
pub(crate) fn apply_delta(delta: &Snapshot) {
    COUNTERS.with(|c| {
        let mut counters = c.borrow_mut();
        for (category, count) in delta {
            if *count > 0 {
                *counters.entry(*category).or_insert(0) += count;
            }
        }
    });
}

/// Restore counters to a previous snapshot.
///
/// Used to roll back false-positive increments from analytical code paths
/// (e.g., `result_is_bool_by_postcondition`) that call `infer_expr_sort`
/// for structural analysis but should not affect demotion decisions. (#994)
pub fn restore(snapshot: &Snapshot) {
    COUNTERS.with(|c| {
        (*c.borrow_mut()).clone_from(snapshot);
    });
}

/// Restore a single counter category to its value in a previous snapshot.
///
/// Used to roll back false-positive increments from hint collection code paths
/// that call Tier 3 sort inference (which fires `SortFallbackToIntFromLogicFn`
/// on `LogicFnCall` nodes) without access to encoder declarations. The actual
/// encoding goes through Tier 1 where declarations are checked. (#2062)
pub(crate) fn restore_category(snapshot: &Snapshot, category: UnsoundnessCategory) {
    COUNTERS.with(|c| {
        let mut counters = c.borrow_mut();
        if let Some(&val) = snapshot.get(&category) {
            counters.insert(category, val);
        } else {
            counters.remove(&category);
        }
    });
}

/// Absorb bootstrap-phase false-positive increments from a SECONDARY encoder
/// setup.
///
/// The primary solve's demotion baseline already forgives bootstrap-phase
/// increments of categories with [`UnsoundnessCategory::has_bootstrap_false_positives`]
/// via `merge_pre_verification_and_post_bootstrap_snapshots` (#994, #2623).
/// Probe paths that bootstrap a *second* encoder over the same clause set
/// (e.g. the non-vacuity fresh-base recheck) re-fire the same declaration-scan
/// fallbacks AFTER that baseline was taken, so those repeats would count as
/// genuine deltas and demote obligations the primary path deliberately
/// forgave. Subtract exactly the bootstrap-phase increments of the secondary
/// setup — the delta between its pre-setup snapshot and its own
/// post-bootstrap snapshot — leaving any genuine post-bootstrap increments
/// (e.g. precondition-phase fallbacks) counted.
pub(crate) fn absorb_secondary_bootstrap_false_positives(
    before_setup: &Snapshot,
    post_bootstrap: &Snapshot,
) {
    COUNTERS.with(|c| {
        let mut counters = c.borrow_mut();
        for (cat, &post_count) in post_bootstrap {
            if !cat.has_bootstrap_false_positives() {
                continue;
            }
            let before_count = before_setup.get(cat).copied().unwrap_or(0);
            let bootstrap_fp = post_count.saturating_sub(before_count);
            if bootstrap_fp == 0 {
                continue;
            }
            if let Some(live) = counters.get_mut(cat) {
                *live = live.saturating_sub(bootstrap_fp);
            }
        }
    });
}

/// Compute the delta between two snapshots.
///
/// Returns only categories whose count increased between `before` and `after`.
#[must_use]
pub fn delta(before: &Snapshot, after: &Snapshot) -> Snapshot {
    let mut result = HashMap::new();
    for (cat, &after_count) in after {
        let before_count = before.get(cat).copied().unwrap_or(0);
        if after_count > before_count {
            result.insert(*cat, after_count - before_count);
        }
    }
    result
}

/// Check if a delta contains any demoting categories.
#[must_use]
pub(crate) fn has_demoting(delta: &Snapshot) -> bool {
    delta
        .iter()
        .any(|(cat, &count)| cat.is_demoting() && count > 0)
}

/// Format demoting categories from a delta for diagnostic messages.
#[must_use]
pub(crate) fn format_demoting(delta: &Snapshot) -> String {
    let mut demoting: Vec<_> = delta
        .iter()
        .filter(|(cat, &count)| cat.is_demoting() && count > 0)
        .collect();
    demoting.sort_by_key(|(cat, _)| format!("{cat}"));
    demoting
        .iter()
        .map(|(cat, count)| format!("{cat}({count})"))
        .collect::<Vec<_>>()
        .join(", ")
}

#[cfg(test)]
mod tests;
