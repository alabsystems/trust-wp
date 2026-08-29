// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
//! The ONE honesty meter (review R2, `docs/design-review-2026-07-06.md`).
//!
//! Before this crate, 31 of 36 spikes carried private copies of the certification gate,
//! and most checked `axiom closure == ∅` — stricter than, and different from, the design:
//!
//! > Certified ⟺ the root judgment and complete reachable declaration/
//! > provenance graph pass the strict Clean audit, with only exact canonical
//! > foundations admitted and sorry/trusted* always in the meter.
//! >   — design-trust-spec-language.md §8 (mirroring §3 L5)
//!
//! This crate preserves the spike-facing grade API while delegating all authority
//! decisions to Clean's expression-rooted certification audit. Trust markers
//! (`sorry`, `trusted*`) and genuine domain axioms cap a proof at Trusted. Invalid
//! provenance, non-canonical foundations, unsafe/partial declarations, and kernel
//! failures are rejected rather than being mistaken for an empty axiom closure.

use clean_kernel::{CertificationIssue, Environment, Expr};

/// The design's canonical foundational axioms.
///
/// Kept as part of the public compatibility API. Certification does not trust these
/// strings: Clean validates the exact canonical declaration kind, universe arity,
/// and statement.
pub const FOUNDATIONAL_AXIOMS: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];

/// The grade of a (goal, term) pair under the design's §6/§8 meter.
///
/// `SolverValidated` and `Pending` are states of an *obligation* (no term yet), so they
/// are out of scope here: this meter grades terms. `Certified-auto` vs `Certified` is a
/// routing distinction (how the term was produced), not a gate distinction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Grade {
    /// Clean's certification audit found a kernel or authority-integrity failure.
    Rejected { error: String },
    /// Type-checks, but the closure reaches genuine trust markers or
    /// non-foundational axioms.
    /// The offending names are listed, sorted, deduplicated.
    Trusted { closure: Vec<String> },
    /// The strict root/declaration/provenance audit passes with only exact
    /// canonical foundations and no trust markers. This is a term grade only;
    /// it never licenses check elision without an exact typed Trust-IR
    /// obligation binding.
    Certified,
}

impl Grade {
    #[must_use]
    pub fn is_certified(&self) -> bool {
        matches!(self, Grade::Certified)
    }
}

/// Grade `term` against `goal` using Clean's strict expression-rooted audit.
///
/// Only genuine trust markers and non-foundational axioms map to `Trusted`. Every
/// other issue, including any future issue unknown to this compatibility wrapper,
/// fails closed to `Rejected`.
#[must_use]
pub fn grade(env: &Environment, goal: &Expr, term: &Expr) -> Grade {
    let audit = env.audit_certification(goal, term);
    if audit.is_certified() {
        return Grade::Certified;
    }

    let mut closure = Vec::new();
    let mut rejected = false;
    for issue in &audit.issues {
        match issue {
            CertificationIssue::TrustMarker { name }
            | CertificationIssue::NonFoundationalAxiom { name } => {
                closure.push(name.to_string());
            }
            _ => rejected = true,
        }
    }

    if rejected {
        return Grade::Rejected {
            error: format!("certification audit rejected proof: {:#?}", audit.issues),
        };
    }

    closure.sort();
    closure.dedup();
    Grade::Trusted { closure }
}

#[cfg(test)]
mod tests {
    use clean_kernel::{expr::BinderInfo, Declaration, Level, Name};

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
    fn true_env() -> Environment {
        let mut env = Environment::new();
        env.init_true_false().expect("initialize True/False");
        env
    }

    /// ∀ x:Nat, x = x  via λ x. Eq.refl x — pure, foundational-free → Certified.
    #[test]
    fn clean_proof_is_certified() {
        let env = Environment::with_prelude();
        let goal = Expr::pi(
            BinderInfo::Default,
            nat(),
            eq_nat(Expr::bvar(0), Expr::bvar(0)),
        );
        let term = Expr::lam(BinderInfo::Default, nat(), refl(Expr::bvar(0)));
        assert_eq!(grade(&env, &goal, &term), Grade::Certified);
    }

    /// A @sorry-discharged goal must NEVER be Certified — markers are always fatal.
    #[test]
    fn sorry_is_trusted_not_certified() {
        let env = Environment::with_prelude();
        let goal = eq_nat(Expr::nat_lit(1), Expr::nat_lit(1));
        let term = Expr::app(
            Expr::const_str_levels("sorry", vec![Level::zero()]),
            goal.clone(),
        );
        let g = grade(&env, &goal, &term);
        match g {
            Grade::Trusted { closure } => assert!(
                closure.iter().any(|n| n.contains("sorry")),
                "closure must name sorry, got {closure:?}"
            ),
            other => panic!("sorry must grade Trusted, got {other:?}"),
        }
    }

    /// A foundation-shaped name is not authority. The declaration must exactly match
    /// the canonical declaration installed by Clean.
    #[test]
    fn foundational_name_spoof_is_rejected() {
        let mut env = true_env();
        let goal = c("True");
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("propext"),
            level_params: vec![],
            type_: goal.clone(),
        })
        .expect("declare well-formed foundation-name spoof");

        let Grade::Rejected { error } = grade(&env, &goal, &c("propext")) else {
            panic!("a foundation-name spoof must be Rejected");
        };
        assert!(error.contains("NonCanonicalFoundation"), "error: {error}");
    }

    /// A DOMAIN axiom (same shape, non-foundational name) caps at Trusted.
    #[test]
    fn domain_axiom_caps_at_trusted() {
        let mut env = Environment::with_prelude();
        let goal_prop = eq_nat(Expr::nat_lit(3), Expr::nat_lit(3));
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("nia_sound"),
            level_params: vec![],
            type_: goal_prop.clone(),
        })
        .expect("declare nia_sound");
        assert_eq!(
            grade(&env, &goal_prop, &c("nia_sound")),
            Grade::Trusted {
                closure: vec!["nia_sound".to_string()]
            }
        );
    }

    /// A well-typed proof inserted through the structural lane has no certification
    /// authority, even though the old synthetic-theorem closure looked empty.
    #[test]
    fn structural_proof_is_rejected() {
        let mut env = true_env();
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("structuralProof"),
            level_params: vec![],
            type_: c("True"),
            value: c("True.intro"),
        })
        .expect("declare structurally valid proof");

        let Grade::Rejected { error } = grade(&env, &c("True"), &c("structuralProof")) else {
            panic!("a structural proof must be Rejected");
        };
        assert!(error.contains("StructuralOnly"), "error: {error}");
    }

    /// Unsafe and partial reachability are authority failures, not Trusted grades.
    #[test]
    fn unsafe_and_partial_proofs_are_rejected() {
        let mut env = true_env();
        for name in ["unsafeProof", "partialProof"] {
            env.add_decl(Declaration::Theorem {
                name: Name::from_string(name),
                level_params: vec![],
                type_: c("True"),
                value: c("True.intro"),
            })
            .expect("declare checked proof");
        }
        env.mark_unsafe(Name::from_string("unsafeProof"));
        env.mark_partial(Name::from_string("partialProof"));

        let Grade::Rejected { error } = grade(&env, &c("True"), &c("unsafeProof")) else {
            panic!("an unsafe proof must be Rejected");
        };
        assert!(error.contains("Unsafe"), "error: {error}");

        let Grade::Rejected { error } = grade(&env, &c("True"), &c("partialProof")) else {
            panic!("a partial proof must be Rejected");
        };
        assert!(error.contains("Partial"), "error: {error}");
    }

    /// An ill-typed term is Rejected.
    #[test]
    fn ill_typed_is_rejected() {
        let env = Environment::with_prelude();
        let goal = eq_nat(Expr::nat_lit(1), Expr::nat_lit(2));
        let term = refl(Expr::nat_lit(1)); // proves 1=1, not 1=2
        assert!(matches!(grade(&env, &goal, &term), Grade::Rejected { .. }));
    }
}
