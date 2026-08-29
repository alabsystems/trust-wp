// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
//! INTERFACE-v1 — the frozen specification-language interface (reference implementation).
//!
//! Normative document: `INTERFACE-v1.md` (repo root). This crate is the freeze made EXECUTABLE:
//! the carrier record (`UOb`), the three-axis grade (`ClauseStatus`), the lane contract
//! (`Lane` / `LaneVerdict`), the single grading entry point (`grade_verdict` — invariant
//! I1's enforcement site), and the invariants I1–I7 as tests. "Frozen" means: consumers
//! written against these types keep compiling and keep MEANING the same thing — evolution
//! is additive (`#[non_exhaustive]`); anything breaking is a v2.

pub use cert_meter::{grade as meter_grade, Grade, FOUNDATIONAL_AXIOMS};
/// The carrier crate, re-exported: consumers of the interface need exactly one dep.
pub use clean_kernel;
use clean_kernel::{Environment, Expr};

// ─────────────────────────── §1 The carrier record ───────────────────────────

/// The kind of a clause-level obligation. `#[non_exhaustive]`: new kinds are additive.
/// `Temporal` freezes the SLOT for ty's temporal lane (design §10); semantics deferred.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObKind {
    Postcondition,
    Refinement,
    UbCheck,
    Invariant,
    GiveBackRefinement,
    TranslationValidation,
    Temporal,
}

/// Routing hint — advisory ONLY; never affects what a grade means.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SolverMode {
    #[default]
    Auto,
    Euf,
    Lia,
    Lra,
    Bv,
    Nia,
}

#[derive(Debug, Clone, Default)]
pub struct RoutingHint {
    pub solver: SolverMode,
    pub note: Option<String>,
}

/// Elaborator-TV status carried per design §8-2: until per-compile translation
/// validation runs, Certified is "relative to a trusted elaborator" and UB-elision
/// is forbidden on un-TV'd goals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CertTaint {
    ElaboratorTrusted,
    ElaboratorTv,
}

/// The one obligation carrier (design §3 L3). `goal` is PROVED; `hypotheses` are
/// ASSUMED (invariant I3) — they fold into the goal as premises, never as obligations.
#[derive(Debug, Clone)]
pub struct UOb {
    pub goal: Expr,
    pub hypotheses: Vec<Expr>,
    pub kind: ObKind,
    pub routing: RoutingHint,
    pub taint: CertTaint,
}

impl UOb {
    pub fn new(goal: Expr, kind: ObKind) -> Self {
        UOb {
            goal,
            hypotheses: Vec::new(),
            kind,
            routing: RoutingHint::default(),
            taint: CertTaint::ElaboratorTrusted,
        }
    }

    /// I3 made concrete: the checked goal is `h1 → h2 → … → goal` — hypotheses are
    /// premises a proof may USE and can never be asked to PROVE.
    #[must_use]
    pub fn elaborated_goal(&self) -> Expr {
        self.hypotheses
            .iter()
            .rev()
            .fold(self.goal.clone(), |acc, h| Expr::arrow(h.clone(), acc))
    }
}

// ──────────────────────── §2 The three-axis grade record ────────────────────────

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LogicTier {
    /// Kernel-checked term whose root judgment and complete reachable
    /// declaration/provenance graph pass the strict audit. Only exact canonical
    /// foundations are admitted. `auto` records only HOW the term was produced.
    Certified { auto: bool },
    /// Type-checks but the closure names genuine assumptions or trust markers.
    Trusted { closure: Vec<String> },
    /// Legacy solver verdict retained as an explicit grade (P0) — no term exists.
    SolverValidated,
    /// No evidence yet (the total-elaboration resting state, I4) or lane declined.
    Pending,
    /// The obligation is refuted or the candidate term is ill-typed.
    Rejected { why: String },
}

/// The spec-to-program link (design §8-3): Certified only where the step relation
/// covers the construct; everything else fails closed to Trusted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProgramTier {
    CertifiedReflection,
    TrustedReflection,
}

/// Coverage of the best evidence (design §10) — the trust-mc landing slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundTier {
    Unbounded,
    BoundedChecked(u64),
    FiniteModelChecked(u64),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClauseStatus {
    pub logic: LogicTier,
    pub program: ProgramTier,
    pub bound: BoundTier,
}

impl ClauseStatus {
    /// Legacy UB-elision query.
    ///
    /// This is deliberately hard-blocked during the direct Rust/Clean-to-
    /// Trust-IR transition. The three grade axes describe a checked Clean term
    /// and a reflection claim, but this record carries no canonical typed
    /// Trust-IR obligation identity or semantic digest. Consequently it cannot
    /// prove that the checked `(goal, term)` is the obligation guarding the
    /// machine check a caller wants to remove. A future authority API must take
    /// an unforgeable, validator-produced obligation binding; grade combinations
    /// alone must never regain elision authority.
    #[must_use]
    pub fn licenses_ub_elision(&self) -> bool {
        false
    }
}

// ───────────────────────────── §3 The lane contract ─────────────────────────────

/// What a lane may return. `#[non_exhaustive]`: new verdicts are additive.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum LaneVerdict {
    /// A kernel-checkable candidate term — the meter grades it (I1).
    Term { term: Expr, auto: bool },
    /// Accept-on-trust wrapper (P2): hard-capped at Trusted even if the closure is clean.
    AxiomCapped { term: Expr, axioms: Vec<String> },
    /// Solver refutation with no reconstructed term (the P0 legacy grade).
    SolverValidated { evidence: String },
    /// Model checker: property checked to bound N; no term. Lands on the BOUND axis (I7).
    Bounded { n: u64, evidence: String },
    /// The obligation is FALSE — surfaced as an error with the witness.
    Counterexample { witness: String },
    /// Outside this lane's fragment — always legal, always safe (I5).
    Decline { reason: String },
}

/// A prover peer (design §3 L4: "peers racing to inhabit the SAME goal").
/// ay, WP, VC (trust-vc), clean-auto, ty, trust-mc, authored/AI terms all implement this.
pub trait Lane {
    fn name(&self) -> &'static str;
    fn attempt(&self, env: &Environment, ob: &UOb) -> LaneVerdict;
}

// ───────────────────── §4 The grading entry point (I1's home) ─────────────────────

/// Grade a lane verdict. THIS is the only path to a `ClauseStatus` — no lane
/// self-grades (I1). `program` is supplied by the reflection layer, not the lane.
#[must_use]
pub fn grade_verdict(
    env: &Environment,
    ob: &UOb,
    verdict: &LaneVerdict,
    program: ProgramTier,
) -> ClauseStatus {
    let goal = ob.elaborated_goal();
    let (logic, bound) = match verdict {
        LaneVerdict::Term { term, auto } => (
            match meter_grade(env, &goal, term) {
                Grade::Certified => LogicTier::Certified { auto: *auto },
                Grade::Trusted { closure } => LogicTier::Trusted { closure },
                Grade::Rejected { error } => LogicTier::Rejected { why: error },
            },
            BoundTier::Unbounded,
        ),
        LaneVerdict::AxiomCapped { term, axioms } => (
            // P2 cap: even a clean-closure term is held at Trusted when the lane
            // declares axiom dependence — the wrapper's honesty beats the accident.
            match meter_grade(env, &goal, term) {
                Grade::Certified => LogicTier::Trusted {
                    closure: axioms.clone(),
                },
                Grade::Trusted { closure } => {
                    let mut all = closure;
                    all.extend(axioms.iter().cloned());
                    all.sort();
                    all.dedup();
                    LogicTier::Trusted { closure: all }
                }
                Grade::Rejected { error } => LogicTier::Rejected { why: error },
            },
            BoundTier::Unbounded,
        ),
        LaneVerdict::SolverValidated { .. } => (LogicTier::SolverValidated, BoundTier::Unbounded),
        // I7: bounded evidence lands on the bound axis; the logic axis stays Pending.
        LaneVerdict::Bounded { n, .. } => (LogicTier::Pending, BoundTier::BoundedChecked(*n)),
        LaneVerdict::Counterexample { witness } => (
            LogicTier::Rejected {
                why: format!("counterexample: {witness}"),
            },
            BoundTier::Unbounded,
        ),
        LaneVerdict::Decline { .. } => (LogicTier::Pending, BoundTier::Unbounded),
        // Future additive verdicts fail closed (I5). Unreachable inside this crate
        // (the match is locally exhaustive); load-bearing for downstream matches.
        #[allow(unreachable_patterns)]
        _ => (LogicTier::Pending, BoundTier::Unbounded),
    };
    ClauseStatus {
        logic,
        bound,
        program,
    }
}

// ───────────────────────── §6 proof! — the authored-term surface (P3) ─────────────────────────

/// The interface-level `proof!` surface (design §3 L1's `proof!{ … := by tac }`, at the
/// kernel-facing layer): an authored term enters the portfolio as a first-class
/// [`LaneVerdict`] — never as a self-graded result (I1). Forms:
/// `proof!(by <Expr>)` → `Term{auto:false}`; `proof!(assume [<axioms>], by <Expr>)` →
/// `AxiomCapped` (hard-capped ≤ Trusted, P2). The Verus-shaped in-source macro that
/// desugars to this lives with the fork-toolchain proc macros (trust-wp-macros); this is
/// the stable target it desugars TO.
#[macro_export]
macro_rules! proof {
    (by $term:expr) => {
        $crate::LaneVerdict::Term { term: $term, auto: false }
    };
    (assume [$($ax:expr),* $(,)?], by $term:expr) => {
        $crate::LaneVerdict::AxiomCapped { term: $term, axioms: vec![$($ax.to_string()),*] }
    };
}

// ─────────────── §7 The proof_by payload evaluator (the lane, v1 vocabulary) ───────────────

/// Evaluate a `trust-wp:proof_by:` payload supplied by a consumer into a
/// [`LaneVerdict`] — the authored lane's entry point.
///
/// v1 tactic vocabulary (extending it is an additive interface change):
/// - `by refl`                      — `Eq.refl` on the goal's own lhs (ground equalities
///                                    close by kernel computation);
/// - `assume [a, b, …], by refl`    — the accept-on-trust form: same term, hard-capped
///                                    at `Trusted` with the named axioms (P2/I1).
/// Anything else returns `Decline` (I5 — fail closed, never a wrong verdict).
#[must_use]
pub fn evaluate_proof_payload(ob: &UOb, payload: &str) -> LaneVerdict {
    use clean_kernel::expr::ExprKind;
    let compact: String = payload.chars().filter(|c| !c.is_whitespace()).collect();
    let (axioms, tactic) = if let Some(rest) = compact.strip_prefix("assume[") {
        match rest.split_once("],by") {
            Some((axes, tac)) => (
                axes.split(',')
                    .filter(|a| !a.is_empty())
                    .map(str::to_string)
                    .collect::<Vec<_>>(),
                tac.to_string(),
            ),
            None => {
                return LaneVerdict::Decline {
                    reason: "malformed assume form".into(),
                }
            }
        }
    } else if let Some(tac) = compact.strip_prefix("by") {
        (Vec::new(), tac.to_string())
    } else {
        return LaneVerdict::Decline {
            reason: "payload must start with `by` or `assume [` ".into(),
        };
    };
    match tactic.as_str() {
        "refl" => {
            // goal shape Eq T a b — build Eq.refl T a; the kernel decides by computation.
            let goal = ob.elaborated_goal();
            let mut cur = &goal;
            let mut args: Vec<&Expr> = Vec::new();
            while let ExprKind::App(f, a) = cur.kind() {
                args.push(a);
                cur = f;
            }
            args.reverse();
            if args.len() != 3 {
                return LaneVerdict::Decline {
                    reason: "refl needs a ground `Eq T a b` goal".into(),
                };
            }
            let term = Expr::apps(
                Expr::const_str_levels(
                    "Eq.refl",
                    vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
                ),
                [args[0].clone(), args[1].clone()],
            );
            if axioms.is_empty() {
                LaneVerdict::Term { term, auto: false }
            } else {
                LaneVerdict::AxiomCapped { term, axioms }
            }
        }
        other => LaneVerdict::Decline {
            reason: format!("unknown tactic `{other}` (v1 vocabulary: refl)"),
        },
    }
}

// ──────────────────── §5 The syntactic auto-fragment checker (P3) ────────────────────

/// Why a goal is OUTSIDE the auto fragment. `#[non_exhaustive]`: reasons are additive.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeepReason {
    /// Binders (Pi/Lam) — universally-quantified or higher-order content routes to the
    /// deep lanes (induction / authored terms), never silently to "auto".
    Quantifier,
    /// A constant outside the interpreted whitelist (uninterpreted or recursive symbol).
    UninterpretedConst(String),
    /// Sorts/universes and other structural forms the auto lanes do not decide.
    Structural,
}

/// The interpreted whitelist — the constants the auto fragment's decision procedures
/// actually compute with (kernel-literal arithmetic + Bool + equality). Extending this
/// list is an INTERFACE change (deliberate, reviewed), never an emergent solver behavior.
pub const AUTO_FRAGMENT_CONSTS: [&str; 21] = [
    "Nat",
    "Bool",
    "Eq",
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.mod",
    "Nat.div",
    "Nat.beq",
    "Nat.ble",
    "Nat.blt",
    "Nat.le",
    "Nat.lt",
    "Bool.true",
    "Bool.false",
    // Boolean structure the in-driver kernel lane emits for && || ! ==> and !=/</>:
    // every const the lane can emit MUST classify Auto (predictability rule; the
    // whitelist is the interface, extending it is a reviewed change — this one closes
    // the audited lane/checker mismatch of 2026-07-07).
    "Bool.and",
    "Bool.or",
    "Bool.not",
    "Bool.beq",
    "And",
    "Not",
];

/// The design §6 predictability rule, made decidable: an AUTHOR-TIME syntactic check
/// that classifies a goal as inside the hands-free auto fragment or outside it —
/// "never 'auto for whatever the solver happens to close'". Conservative by
/// construction: quantifier-free goals over the interpreted whitelist (literals, bound
/// variables already discharged, computable Nat/Bool atoms) are Auto; anything with
/// binders, unknown constants, or structural forms routes Deep. Session-validated: the
/// ground facts clean-auto closed all session are Auto; every goal that needed
/// authored/inductive terms (universal wsub equivalence, 0+n=n, safety laws) is Deep.
#[must_use]
pub fn classify_auto_fragment(goal: &Expr) -> Result<(), DeepReason> {
    use clean_kernel::expr::ExprKind;
    match goal.kind() {
        ExprKind::Pi(..) | ExprKind::Lam(..) => Err(DeepReason::Quantifier),
        ExprKind::Const(name, _levels) => {
            let n = name.to_string();
            if AUTO_FRAGMENT_CONSTS.contains(&n.as_str()) {
                Ok(())
            } else {
                Err(DeepReason::UninterpretedConst(n))
            }
        }
        ExprKind::App(f, a) => {
            classify_auto_fragment(f)?;
            classify_auto_fragment(a)
        }
        ExprKind::Lit(_) | ExprKind::BVar(_) => Ok(()),
        _ => Err(DeepReason::Structural),
    }
}

// ─────────────────────────── The invariants, as tests ───────────────────────────

#[cfg(test)]
mod tests {
    use clean_kernel::{expr::BinderInfo, Level, Name};

    use super::*;

    fn c(n: &str) -> Expr {
        Expr::const_(Name::from_string(n), vec![])
    }
    fn nat() -> Expr {
        c("Nat")
    }
    fn eq_nat(a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
            [nat(), a, b],
        )
    }
    fn refl(x: Expr) -> Expr {
        Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![Level::succ(Level::zero())]),
            [nat(), x],
        )
    }
    fn trivial_ob() -> UOb {
        UOb::new(
            eq_nat(Expr::nat_lit(1), Expr::nat_lit(1)),
            ObKind::Postcondition,
        )
    }

    /// I1 (positive): a clean term grades Certified — through the meter only.
    #[test]
    fn i1_term_reaches_certified_via_meter() {
        let env = Environment::with_prelude();
        let ob = trivial_ob();
        let v = LaneVerdict::Term {
            term: refl(Expr::nat_lit(1)),
            auto: true,
        };
        let s = grade_verdict(&env, &ob, &v, ProgramTier::CertifiedReflection);
        assert_eq!(s.logic, LogicTier::Certified { auto: true });
    }

    /// I1 (marker): a @sorry term can NEVER be Certified.
    #[test]
    fn i1_sorry_is_trusted_never_certified() {
        let env = Environment::with_prelude();
        let ob = trivial_ob();
        let term = Expr::app(
            Expr::const_str_levels("sorry", vec![Level::zero()]),
            ob.elaborated_goal(),
        );
        let s = grade_verdict(
            &env,
            &ob,
            &LaneVerdict::Term { term, auto: false },
            ProgramTier::CertifiedReflection,
        );
        match s.logic {
            LogicTier::Trusted { closure } => assert!(closure.iter().any(|n| n.contains("sorry"))),
            other => panic!("sorry must grade Trusted, got {other:?}"),
        }
    }

    /// I1/P2 (cap): a lane declaring axiom dependence is capped at Trusted even when
    /// the term's own closure is clean — no self-grading past the wrapper.
    #[test]
    fn i1_axiom_capped_never_certified() {
        let env = Environment::with_prelude();
        let ob = trivial_ob();
        let v = LaneVerdict::AxiomCapped {
            term: refl(Expr::nat_lit(1)),
            axioms: vec!["nia_sound".into()],
        };
        let s = grade_verdict(&env, &ob, &v, ProgramTier::CertifiedReflection);
        assert_eq!(
            s.logic,
            LogicTier::Trusted {
                closure: vec!["nia_sound".into()]
            }
        );
        assert!(!s.licenses_ub_elision());
    }

    /// I2: even the strongest three-axis grade is statement-only until it is
    /// bound to the exact typed Trust-IR obligation.
    #[test]
    fn i2_unbound_grade_never_licenses_elision() {
        let cert = LogicTier::Certified { auto: true };
        let all = ClauseStatus {
            logic: cert.clone(),
            program: ProgramTier::CertifiedReflection,
            bound: BoundTier::Unbounded,
        };
        assert!(!all.licenses_ub_elision());
        let bad_prog = ClauseStatus {
            program: ProgramTier::TrustedReflection,
            ..all.clone()
        };
        assert!(!bad_prog.licenses_ub_elision());
        let bad_bound = ClauseStatus {
            bound: BoundTier::BoundedChecked(1 << 20),
            ..all.clone()
        };
        assert!(!bad_bound.licenses_ub_elision());
        let bad_logic = ClauseStatus {
            logic: LogicTier::SolverValidated,
            ..all
        };
        assert!(!bad_logic.licenses_ub_elision());
    }

    /// I3: hypotheses are PREMISES — the proof term may use them (λh. h) and is never
    /// asked to prove them.
    #[test]
    fn i3_hypotheses_fold_as_premises() {
        let env = Environment::with_prelude();
        let h = eq_nat(Expr::nat_lit(2), Expr::nat_lit(2));
        let mut ob = UOb::new(h.clone(), ObKind::Postcondition);
        ob.hypotheses.push(h.clone());
        // elaborated goal is h → h; the identity lambda inhabits it.
        let term = Expr::lam(BinderInfo::Default, h, Expr::bvar(0));
        let s = grade_verdict(
            &env,
            &ob,
            &LaneVerdict::Term { term, auto: false },
            ProgramTier::CertifiedReflection,
        );
        assert_eq!(s.logic, LogicTier::Certified { auto: false });
    }

    /// I4/I5: before any lane succeeds — and on Decline — the state is Pending. Safe.
    #[test]
    fn i4_i5_decline_is_pending_and_safe() {
        let env = Environment::with_prelude();
        let ob = trivial_ob();
        let s = grade_verdict(
            &env,
            &ob,
            &LaneVerdict::Decline {
                reason: "outside fragment".into(),
            },
            ProgramTier::TrustedReflection,
        );
        assert_eq!(s.logic, LogicTier::Pending);
        assert!(!s.licenses_ub_elision());
    }

    /// I7: bounded evidence lands on the bound axis, leaves logic Pending, and can
    /// never launder into Certified or elision.
    #[test]
    fn i7_bounded_never_launders() {
        let env = Environment::with_prelude();
        let ob = trivial_ob();
        let v = LaneVerdict::Bounded {
            n: 4096,
            evidence: "kani harness, unwind 4096".into(),
        };
        let s = grade_verdict(&env, &ob, &v, ProgramTier::CertifiedReflection);
        assert_eq!(s.logic, LogicTier::Pending);
        assert_eq!(s.bound, BoundTier::BoundedChecked(4096));
        assert!(!s.licenses_ub_elision());
    }

    /// A counterexample rejects the obligation with the witness surfaced.
    #[test]
    fn counterexample_rejects_with_witness() {
        let env = Environment::with_prelude();
        let ob = trivial_ob();
        let v = LaneVerdict::Counterexample {
            witness: "a=4294967296, b=0".into(),
        };
        let s = grade_verdict(&env, &ob, &v, ProgramTier::CertifiedReflection);
        assert!(matches!(s.logic, LogicTier::Rejected { ref why } if why.contains("a=4294967296")));
    }

    /// The proof_by evaluator: `by refl` certifies a ground equality; the assume form
    /// caps at Trusted; unknown tactics and non-Eq goals fail closed to Decline/Pending.
    #[test]
    fn proof_payload_evaluator_v1() {
        let env = Environment::with_prelude();
        let ob = UOb::new(
            eq_nat(Expr::nat_lit(6), Expr::nat_lit(6)),
            ObKind::Postcondition,
        );
        let s = grade_verdict(
            &env,
            &ob,
            &evaluate_proof_payload(&ob, "by refl"),
            ProgramTier::CertifiedReflection,
        );
        assert_eq!(s.logic, LogicTier::Certified { auto: false });
        let s2 = grade_verdict(
            &env,
            &ob,
            &evaluate_proof_payload(&ob, "assume [nia_sound], by refl"),
            ProgramTier::CertifiedReflection,
        );
        assert_eq!(
            s2.logic,
            LogicTier::Trusted {
                closure: vec!["nia_sound".into()]
            }
        );
        let s3 = grade_verdict(
            &env,
            &ob,
            &evaluate_proof_payload(&ob, "by hammer"),
            ProgramTier::CertifiedReflection,
        );
        assert_eq!(s3.logic, LogicTier::Pending);
    }

    /// P3 `proof!`: an authored term enters as a verdict and grades through the ONE
    /// meter — Certified for a clean term, capped at Trusted under `assume`.
    #[test]
    fn proof_macro_routes_through_the_meter() {
        let env = Environment::with_prelude();
        let goal = eq_nat(Expr::nat_lit(4), Expr::nat_lit(4));
        let ob = UOb::new(goal, ObKind::Postcondition);
        let v = proof!(by refl(Expr::nat_lit(4)));
        let s = grade_verdict(&env, &ob, &v, ProgramTier::CertifiedReflection);
        assert_eq!(s.logic, LogicTier::Certified { auto: false });
        let v2 = proof!(assume ["nia_sound"], by refl(Expr::nat_lit(4)));
        let s2 = grade_verdict(&env, &ob, &v2, ProgramTier::CertifiedReflection);
        assert_eq!(
            s2.logic,
            LogicTier::Trusted {
                closure: vec!["nia_sound".into()]
            }
        );
    }

    /// P3 predictability: ground interpreted goals are Auto; binders and unknown
    /// constants route Deep — decidably, at author time.
    #[test]
    fn auto_fragment_checker_is_predictable() {
        // ground: beq 3 3 = true — inside.
        let ground = Expr::apps(
            Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
            [
                c("Bool"),
                Expr::apps(c("Nat.beq"), [Expr::nat_lit(3), Expr::nat_lit(3)]),
                c("Bool.true"),
            ],
        );
        assert_eq!(classify_auto_fragment(&ground), Ok(()));
        // universal: ∀ x, x = x — Deep(Quantifier), even though trivially true.
        let univ = Expr::pi(
            BinderInfo::Default,
            nat(),
            eq_nat(Expr::bvar(0), Expr::bvar(0)),
        );
        assert_eq!(classify_auto_fragment(&univ), Err(DeepReason::Quantifier));
        // uninterpreted symbol: sum_to 3 = 6 — Deep(UninterpretedConst).
        let rec = eq_nat(Expr::app(c("sum_to"), Expr::nat_lit(3)), Expr::nat_lit(6));
        assert!(matches!(
            classify_auto_fragment(&rec),
            Err(DeepReason::UninterpretedConst(ref n)) if n == "sum_to"
        ));
    }

    /// The lane contract end-to-end: two peers race the same goal; the meter, not the
    /// lanes, decides. (A Decline peer and a Term peer.)
    #[test]
    fn lanes_race_the_same_goal() {
        struct Declines;
        impl Lane for Declines {
            fn name(&self) -> &'static str {
                "wp"
            }
            fn attempt(&self, _env: &Environment, _ob: &UOb) -> LaneVerdict {
                LaneVerdict::Decline {
                    reason: "outside fragment".into(),
                }
            }
        }
        struct Authored;
        impl Lane for Authored {
            fn name(&self) -> &'static str {
                "authored"
            }
            fn attempt(&self, _env: &Environment, ob: &UOb) -> LaneVerdict {
                let _ = ob;
                LaneVerdict::Term {
                    term: refl(Expr::nat_lit(1)),
                    auto: false,
                }
            }
        }
        let env = Environment::with_prelude();
        let ob = trivial_ob();
        let lanes: Vec<Box<dyn Lane>> = vec![Box::new(Declines), Box::new(Authored)];
        let best = lanes
            .iter()
            .map(|l| {
                grade_verdict(
                    &env,
                    &ob,
                    &l.attempt(&env, &ob),
                    ProgramTier::CertifiedReflection,
                )
            })
            .fold(None::<ClauseStatus>, |acc, s| match acc {
                Some(a) if matches!(a.logic, LogicTier::Certified { .. }) => Some(a),
                _ if matches!(s.logic, LogicTier::Certified { .. }) => Some(s),
                Some(a) => Some(a),
                None => Some(s),
            })
            .unwrap();
        assert!(matches!(best.logic, LogicTier::Certified { .. }));
    }
}
