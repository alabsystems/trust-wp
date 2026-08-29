// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CONTROL: the strict-proof trust gate.
//!
//! # What this file protects
//!
//! An UNSAT verdict whose *terminal derivation chain is not trust-free* — it
//! reaches the empty clause through an unverified `trust`/`hole` step, or an
//! `assume` leaf that no problem assertion backs — is **not** a proof. Under
//! strict-proof mode such a verdict must be **REJECTED**, and the rejection
//! must stay **DISTINGUISHABLE** from a clean UNSAT that closed through
//! semantically checked steps.
//!
//! That is the soundness gate originally described in ay's #8759. It is the
//! single behaviour this file exists to hold fixed across ay version bumps.
//!
//! # Why it is written as a control and not a unit test
//!
//! The gate is enforced at four separate boundaries, and a bump can break any
//! one of them without touching the others. All four are asserted here so
//! that "the gate survived" is one test target, not an archaeology exercise:
//!
//! * **L1 — the ay boundary.** Best-effort proof collection retains a real
//!   diagnostic proof without making it verdict authority. AY's independently
//!   certified UNSAT stays definite while
//!   `Solver::last_strict_proof_quality()` rejects the trust-bearing artifact.
//!   A clean explicit proof remains definite and strictly accepted.
//! * **L1b — explicit artifact authority.** `set_produce_proofs(true)` is an
//!   authority demand, not a diagnostic request. If AY cannot present a strict
//!   proof for the same independently checked theorem, it must publish typed
//!   `Unknown(SelfCheckRejected)` and revoke proof access.
//! * **L2 — the trust-wp gate.** `VerificationResult::apply_strict_trust(true)`
//!   is trust-wp's own downgrade, driven off the same live `ProofQuality`. A
//!   trust-bearing proof must land on `Unknown(UnknownReason::ProofTrusted)`;
//!   a clean proof must stay `Verified`.
//! * **L3 — the ay-CLI reason lane.** The strict CLI publishes terminal-trust
//!   rejection as `(incomplete proof-trusted)`, and AY now also carries the
//!   typed `ay_dpll::UnknownReason::ProofTrusted` on that path. trust-wp's
//!   subprocess lane parses the string to its non-retryable policy verdict.
//!
//! An optional L4 end-to-end layer drives a real `ay` binary when `AY_BIN`
//! points at one. It is opt-in because trust-wp links ay as a library and does
//! not otherwise need the binary built; L1 already exercises the same ay code.
//!
//! # Reading a failure
//!
//! If L1 fails: AY stopped separating diagnostic proof quality from verdict
//! authority. If L1b fails: an explicit artifact demand ceased to fail closed.
//! Do not weaken either control. If L2 or L3 fails, the consumer stopped
//! honouring a rejection AY still reports.

use ay_dpll::api::{Logic, ProofQuality, Solver, Sort};
use trust_wp_ay::{ProofCertificateSummary, UnknownReason, VerificationResult};

// ---------------------------------------------------------------------------
// Fixtures — two real solves, one trust-bearing and one clean.
// ---------------------------------------------------------------------------

/// A QF_NIA refutation ay closes with an unverified step: `x * x = 2` has no
/// integer solution, but the nonlinear refutation is not reconstructed into
/// semantically checked Alethe — the terminal chain carries a `hole`/`trust`
/// step. This is exactly the shape #8759 fences.
fn trust_bearing_unsat_quality() -> ProofQuality {
    let mut solver = Solver::try_new(Logic::QfNia).expect("QF_NIA solver");
    solver.set_best_effort_produce_proofs(1_000_000);

    let x = solver.declare_const("x", Sort::Int);
    let x_sq = solver.try_mul(x, x).expect("x * x");
    let two = solver.int_const(2);
    let eq = solver.try_eq(x_sq, two).expect("x * x = 2");
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert!(
        details.result.result().is_unsat(),
        "fixture precondition: the independently certified `x * x = 2` theorem \
         must refute over the integers; got {:?}",
        details.result.result()
    );

    let quality = solver
        .last_proof_quality()
        .expect("best-effort collection must retain this diagnostic proof");

    // L1a: the proof really is trust-bearing. If this stops holding the fixture
    // has drifted (ay learned to prove it properly) and must be replaced with a
    // still-trust-bearing one — NOT deleted.
    assert!(
        !quality.is_complete(),
        "fixture drift: `x * x = 2` no longer produces a trust/hole-bearing proof \
         (trust_count={}, hole_count={}). Replace the fixture with one that still \
         exercises an unverified terminal step; do not weaken the control.",
        quality.trust_count,
        quality.hole_count
    );

    // L1b: ay's own strict-proof checker REJECTS it.
    let strict = solver
        .last_strict_proof_quality()
        .expect("the retained diagnostic proof must expose a strict verdict");
    assert!(
        strict.is_err(),
        "SOUNDNESS GATE LOST (#8759): ay's strict-proof checker ACCEPTED a proof \
         whose terminal chain is not trust-free (trust_count={}, hole_count={}). \
         A trust-bearing UNSAT must be rejected under strict proofs.",
        quality.trust_count,
        quality.hole_count
    );

    quality
}

/// Explicit proof production is a presentation authority demand. The exact
/// nonlinear theorem is independently certified, but AY cannot translate its
/// accepted semantic certificate into a strict authored-scope proof yet. It
/// must therefore withhold UNSAT as a typed self-check rejection and revoke
/// access to any non-authoritative proof state.
#[test]
fn explicit_artifact_demand_withholds_unpresentable_unsat_and_revokes_proof() {
    let mut solver = Solver::try_new(Logic::QfNia).expect("QF_NIA solver");
    solver.set_produce_proofs(true);

    let x = solver.declare_const("explicit_artifact_x", Sort::Int);
    let x_sq = solver.try_mul(x, x).expect("x * x");
    let two = solver.int_const(2);
    let eq = solver.try_eq(x_sq, two).expect("x * x = 2");
    solver.assert_term(eq);

    let details = solver.check_sat_with_details();
    assert!(
        details.result.result().is_unknown(),
        "SOUNDNESS GATE LOST: an explicit proof-artifact request published \
         an UNSAT whose strict authored-scope proof is unavailable; got {:?}",
        details.result.result()
    );
    assert_eq!(
        details.unknown_reason,
        Some(ay_dpll::UnknownReason::SelfCheckRejected),
        "the mandatory verdict-certification rejection must stay typed and \
         distinguishable"
    );
    assert_eq!(
        solver.unknown_reason(),
        Some(ay_dpll::UnknownReason::SelfCheckRejected),
        "the solver-level typed reason must agree with CheckSatDetails"
    );
    assert!(
        solver.last_proof_quality().is_none(),
        "an Unknown publication must revoke access to the rejected proof"
    );
    assert!(
        solver.last_strict_proof_quality().is_none(),
        "an Unknown publication must not retain an authority-looking strict result"
    );
}

/// A plain QF_LIA contradiction: `x < 0 && x > 1`. Farkas closes it and the
/// terminal chain is `th_resolution` over checked steps — the clean UNSAT the
/// gate must NOT reject.
fn clean_unsat_quality() -> ProofQuality {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA solver");
    solver.set_produce_proofs(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let lt = solver.try_lt(x, zero).expect("x < 0");
    let gt = solver.try_gt(x, one).expect("x > 1");
    solver.assert_term(lt);
    solver.assert_term(gt);

    let details = solver.check_sat_with_details();
    assert!(
        details.result.result().is_unsat(),
        "fixture precondition: `x < 0 && x > 1` must be UNSAT; got {:?}",
        details.result.result()
    );

    let quality = solver
        .last_proof_quality()
        .expect("UNSAT with proofs enabled must expose proof quality");

    assert!(
        quality.is_complete(),
        "fixture drift: the clean QF_LIA refutation acquired trust/hole steps \
         (trust_count={}, hole_count={}); it can no longer serve as the \
         clean-UNSAT side of the control.",
        quality.trust_count,
        quality.hole_count
    );

    quality
}

fn summary_from(quality: &ProofQuality, strict_verified: bool) -> ProofCertificateSummary {
    ProofCertificateSummary {
        strict_verified,
        restricted_rule_subset: false,
        trust_count: quality.trust_count,
        trust_fallback_count: quality.trust_fallback_count,
        hole_count: quality.hole_count,
        theory_lemma_count: quality.theory_lemma_count,
        resolution_count: quality.resolution_count,
        farkas_certificate_count: 0,
        lrat_present: false,
        alethe_text: None,
    }
}

// ---------------------------------------------------------------------------
// L1 — the ay boundary: rejected, and distinguishable from a clean UNSAT.
// ---------------------------------------------------------------------------

/// A trust-bearing UNSAT is REJECTED by ay's strict-proof checker while a clean
/// UNSAT is ACCEPTED — the two verdicts are distinguishable at the ay boundary.
///
/// This is the load-bearing assertion of the whole file: both sides are real
/// solves, so it fails if an ay bump either stops rejecting trust-bearing
/// proofs or starts rejecting clean ones.
#[test]
fn ay_strict_checker_rejects_trust_bearing_unsat_and_accepts_clean_unsat() {
    let tainted = trust_bearing_unsat_quality();
    let clean = clean_unsat_quality();

    assert!(
        !tainted.is_complete() && clean.is_complete(),
        "the two sides of the control collapsed into the same shape: \
         tainted(trust={},hole={}) clean(trust={},hole={})",
        tainted.trust_count,
        tainted.hole_count,
        clean.trust_count,
        clean.hole_count,
    );

    // Re-run the clean side through the strict checker explicitly: rejection
    // must be *specific to* the trust-bearing proof, not blanket.
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA solver");
    solver.set_produce_proofs(true);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let lt = solver.try_lt(x, zero).expect("x < 0");
    let gt = solver.try_gt(x, one).expect("x > 1");
    solver.assert_term(lt);
    solver.assert_term(gt);
    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_unsat());

    let strict = solver
        .last_strict_proof_quality()
        .expect("clean UNSAT must expose a strict verdict");
    assert!(
        strict.is_ok(),
        "OVER-REJECTION: the strict-proof gate rejected a clean UNSAT whose \
         terminal chain is trust-free. Widening the gate is as much a failure \
         as losing it. error: {:?}",
        strict.err()
    );
}

// ---------------------------------------------------------------------------
// L2 — the trust-wp gate: the rejection reaches a typed consumer verdict.
// ---------------------------------------------------------------------------

/// trust-wp's own strict-trust gate downgrades a live trust-bearing proof to
/// `Unknown(ProofTrusted)` and leaves a live clean proof `Verified`.
#[test]
fn trust_wp_strict_gate_downgrades_trust_bearing_proof_only() {
    let tainted = summary_from(&trust_bearing_unsat_quality(), false);
    let clean = summary_from(&clean_unsat_quality(), true);

    assert!(
        !tainted.is_fully_verified(),
        "a trust-bearing ProofCertificateSummary must not read as fully verified"
    );
    assert!(
        clean.is_fully_verified(),
        "a clean ProofCertificateSummary must read as fully verified"
    );

    let rejected = VerificationResult::verified_with_proof(tainted).apply_strict_trust(true);
    assert!(
        matches!(
            rejected,
            VerificationResult::Unknown(UnknownReason::ProofTrusted)
        ),
        "SOUNDNESS GATE LOST (#8759): trust-wp accepted an UNSAT whose terminal \
         chain carries unverified trust steps. expected \
         Unknown(ProofTrusted), got {rejected:?}"
    );

    let accepted = VerificationResult::verified_with_proof(clean).apply_strict_trust(true);
    assert!(
        matches!(accepted, VerificationResult::Verified(Some(_))),
        "OVER-REJECTION: a clean UNSAT was downgraded by the strict-trust gate; \
         got {accepted:?}"
    );

    assert_ne!(
        std::mem::discriminant(&rejected),
        std::mem::discriminant(&accepted),
        "the rejected and the clean verdict must remain distinguishable: \
         rejected={rejected:?} accepted={accepted:?}"
    );
}

// ---------------------------------------------------------------------------
// L3 — the ay-CLI reason lane: the string that carries the distinction.
// ---------------------------------------------------------------------------

/// The `ay` driver publishes the strict-proof rejection as the reason string
/// `(incomplete proof-trusted)`. AY's executor now also retains the typed
/// `ay_dpll::UnknownReason::ProofTrusted`; the subprocess lane must preserve
/// the same distinction by mapping its wire spelling to `ProofTrusted`.
#[test]
fn ay_cli_proof_trusted_reason_string_maps_to_proof_trusted() {
    for spelling in ["(incomplete proof-trusted)", "proof-trusted"] {
        let parsed = UnknownReason::from_solver_reason(Some(spelling.to_string()));
        assert_eq!(
            parsed,
            UnknownReason::ProofTrusted,
            "SOUNDNESS GATE LOST (#8759): the ay strict-proof rejection reason \
             {spelling:?} no longer parses to ProofTrusted"
        );
        assert_ne!(
            parsed,
            UnknownReason::Incomplete,
            "the strict-proof rejection must not collapse into the generic \
             `Incomplete` — that is the distinction the gate exists to keep"
        );
        assert_ne!(parsed, UnknownReason::Unspecified);
        assert_ne!(parsed, UnknownReason::SolverMessage(spelling.to_string()));
    }
}

// ---------------------------------------------------------------------------
// L4 (opt-in) — end to end through a real `ay` binary.
// ---------------------------------------------------------------------------

/// Drive a real `ay --strict-proofs` when `AY_BIN` names one.
///
/// Not run by default: trust-wp consumes ay as a library, so the binary is not
/// otherwise built here, and L1 already exercises the same strict checker. Run
/// it explicitly across an ay pin bump:
///
/// ```sh
/// AY_BIN=/path/to/ay cargo test -p trust-wp-ay --test strict_proof_trust_gate
/// ```
#[test]
fn ay_binary_strict_proofs_downgrades_trust_bearing_unsat() {
    let Some(bin) = std::env::var_os("AY_BIN") else {
        eprintln!("AY_BIN unset: skipping the end-to-end ay-binary layer (L1-L3 still ran)");
        return;
    };

    const TRUST_BEARING: &str = "(set-logic QF_NIA)\n\
                                 (declare-const x Int)\n\
                                 (assert (= (* x x) 2))\n\
                                 (check-sat)\n";
    const CLEAN: &str = "(set-logic QF_LIA)\n\
                         (declare-const x Int)\n\
                         (assert (< x 0))\n\
                         (assert (> x 1))\n\
                         (check-sat)\n";

    let dir = std::env::temp_dir().join(format!(
        "trust-wp-strict-proof-gate-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock")
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");

    let run = |name: &str, body: &str, strict: bool| -> (String, String) {
        let path = dir.join(name);
        std::fs::write(&path, body).expect("write smt2");
        let mut cmd = std::process::Command::new(&bin);
        if strict {
            cmd.arg("--strict-proofs");
        }
        let out = cmd
            .arg("-t:20000")
            .arg(&path)
            .output()
            .expect("spawn ay binary");
        let stdout = String::from_utf8_lossy(&out.stdout).to_string();
        let stderr = String::from_utf8_lossy(&out.stderr).to_string();
        let verdict = stdout
            .lines()
            .find(|l| !l.starts_with("c "))
            .unwrap_or("")
            .trim()
            .to_string();
        (verdict, stderr)
    };

    // Default CLI proof collection is best-effort. The exact theorem is
    // independently certified, so a rejected diagnostic artifact cannot erase
    // its UNSAT verdict.
    let (default_verdict, _) = run("tainted_default.smt2", TRUST_BEARING, false);
    assert_eq!(
        default_verdict, "unsat",
        "fixture drift: best-effort CLI proof collection no longer preserves \
         this independently certified UNSAT"
    );

    let (strict_verdict, strict_stderr) = run("tainted_strict.smt2", TRUST_BEARING, true);
    assert_ne!(
        strict_verdict, "unsat",
        "SOUNDNESS GATE LOST (#8759): `ay --strict-proofs` accepted an UNSAT \
         whose required strict artifact was rejected.\nstderr:\n{strict_stderr}"
    );
    assert_eq!(
        strict_verdict, "unknown",
        "expected the strict-proof downgrade to `unknown`; got {strict_verdict:?}"
    );
    assert!(
        strict_stderr.contains("(:reason-unknown (incomplete self-check-rejected))"),
        "the artifact-authority rejection must stay distinguishable: expected \
         `(:reason-unknown (incomplete self-check-rejected))` on stderr, got:\n{strict_stderr}"
    );
    let self_check_rejected =
        UnknownReason::from_solver_reason(Some("(incomplete self-check-rejected)".to_string()));
    assert_eq!(
        self_check_rejected,
        UnknownReason::SelfCheckRejected,
        "mandatory certification rejection must retain its structured, \
         non-retryable identity"
    );
    assert_ne!(
        self_check_rejected,
        UnknownReason::ProofTrusted,
        "mandatory certification rejection must not be widened into \
         trust-wp's narrower ProofTrusted policy lane"
    );

    let (clean_verdict, clean_stderr) = run("clean_strict.smt2", CLEAN, true);
    assert_eq!(
        clean_verdict, "unsat",
        "OVER-REJECTION: `ay --strict-proofs` rejected a clean UNSAT.\n\
         stderr:\n{clean_stderr}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
