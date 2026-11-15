// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A logic function's credit rests on the axioms its proof environment held.
//!
//! The logic pass proves each logic function with the other functions' spec
//! axioms in scope. One whose obligation was already lost when that
//! environment was built is neutralized there, as every downstream consumer
//! reads it. One lost LATER was still in the environment: a callee checked
//! after its caller, or a trait logic method's grant the implementation
//! discharge withdraws after the pass
//! (logic_fn_credit_on_trait_grant_refuted_by_impl.rs). The grant and the
//! obligation are the same axiom, so the credit cannot outlive it: a credit
//! whose goal reaches an axiom lost after its proof is withdrawn, the
//! function's own axiom with it, and the withdrawal repeats until nothing more
//! is lost (D-159).

use std::collections::HashSet;

use trust_wp_core::logic::LogicFnDef;

use super::super::{super::reporting::VerificationCounters, prep::neutralized_axiom_reached};

/// Which printed line a credit is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum LogicCreditKind {
    /// `<path> verified ✓`, counted in `verified`.
    Function,
    /// `proof_assert in <path> verified ✓`, counted in `logic_assertions_verified`.
    Assertions,
}

#[derive(Debug)]
struct LogicCredit {
    /// Index into the logic-function slice the pass ran over.
    index: usize,
    kinds: Vec<LogicCreditKind>,
    /// The axioms the proof environment had already neutralized.
    excluded: HashSet<String>,
    withdrawn: bool,
}

/// The credits one logic pass granted.
#[derive(Debug, Default)]
pub(in crate::callbacks) struct LogicCredits {
    credits: Vec<LogicCredit>,
}

impl LogicCredits {
    pub(super) fn record(
        &mut self,
        index: usize,
        kind: LogicCreditKind,
        excluded: &HashSet<String>,
    ) {
        if let Some(credit) = self.credits.iter_mut().find(|credit| credit.index == index) {
            credit.kinds.push(kind);
            return;
        }
        self.credits.push(LogicCredit {
            index,
            kinds: vec![kind],
            excluded: excluded.clone(),
            withdrawn: false,
        });
    }

    /// Withdraw every standing credit whose goal (the function's body and
    /// clauses) reaches an axiom lost since its proof environment was built,
    /// record the function's own axiom as lost, and repeat until a round
    /// withdraws nothing. `logic_fns` is the slice the pass ran over.
    ///
    /// Reachability is `neutralized_axiom_reached`'s, over-approximate in the
    /// refusal direction; a spurious hit costs a credit in a run that already
    /// holds an unproved axiom, and so already exits non-zero.
    pub(in crate::callbacks) fn withdraw_stale(
        &mut self,
        logic_fns: &[LogicFnDef],
        unverified_axioms: &mut HashSet<String>,
        counters: &mut VerificationCounters,
    ) -> Vec<String> {
        let mut printed = Vec::new();
        loop {
            let mut withdrew = false;
            for credit in self.credits.iter_mut().filter(|credit| !credit.withdrawn) {
                let Some(logic_fn) = logic_fns.get(credit.index) else {
                    continue;
                };
                let own = logic_fn.full_path();
                let lost: HashSet<String> = unverified_axioms
                    .iter()
                    .filter(|path| path.as_str() != own && !credit.excluded.contains(*path))
                    .cloned()
                    .collect();
                let goal = std::iter::once(logic_fn.body())
                    .chain(logic_fn.requires())
                    .chain(logic_fn.ensures());
                let Some(reached) = neutralized_axiom_reached(logic_fns, &lost, goal) else {
                    continue;
                };
                credit.withdrawn = true;
                withdrew = true;
                for kind in &credit.kinds {
                    match kind {
                        LogicCreditKind::Function => {
                            counters.verified = counters.verified.saturating_sub(1);
                        }
                        LogicCreditKind::Assertions => {
                            counters.logic_assertions_verified =
                                counters.logic_assertions_verified.saturating_sub(1);
                        }
                    }
                    counters.errors += 1;
                }
                // `it reaches` is a withdrawal the adversarial gate also reads
                // as taking back the function's assertion credit.
                let line = format!(
                    "trust-wp: {own} error: verdict withdrawn - it reaches `{reached}`, whose \
                     axiom was withdrawn after this proof assumed it"
                );
                eprintln!("{line}");
                printed.push(line);
                unverified_axioms.insert(own.to_owned());
            }
            if !withdrew {
                return printed;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use trust_wp_core::{formula::PureExpr, logic::LogicFnDef};

    use super::{LogicCreditKind, LogicCredits};
    use crate::callbacks::reporting::VerificationCounters;

    fn logic_fn(name: &str, body: PureExpr) -> LogicFnDef {
        LogicFnDef::new(
            name.to_string(),
            format!("test::{name}"),
            vec!["x".to_string()],
            body,
        )
    }

    fn call(name: &str) -> PureExpr {
        PureExpr::LogicFnCall {
            name: name.to_string(),
            args: vec![PureExpr::Var("x".to_string(), None)],
        }
    }

    /// `f`'s body calls `g`, `g`'s calls `h`; `k` calls nothing.
    fn chain() -> Vec<LogicFnDef> {
        vec![
            logic_fn("f", call("g")),
            logic_fn("g", call("h")),
            logic_fn("h", PureExpr::Int(0)),
            logic_fn("k", PureExpr::Int(1)),
        ]
    }

    #[test]
    fn a_credit_whose_callee_is_lost_after_its_proof_is_withdrawn_and_cascades() {
        let fns = chain();
        let mut credits = LogicCredits::default();
        let mut counters = VerificationCounters::default();
        let excluded = HashSet::new();
        // g and k proved first, f after them, each on an environment that lost nothing.
        credits.record(1, LogicCreditKind::Function, &excluded);
        credits.record(3, LogicCreditKind::Function, &excluded);
        credits.record(0, LogicCreditKind::Function, &excluded);
        credits.record(0, LogicCreditKind::Assertions, &excluded);
        counters.verified = 3;
        counters.logic_assertions_verified = 1;
        // h's obligation is lost afterwards.
        let mut unverified = HashSet::from(["test::h".to_string()]);
        let printed = credits.withdraw_stale(&fns, &mut unverified, &mut counters);
        assert_eq!(printed.len(), 2, "g and then f: {printed:?}");
        let withdrew = |head: &str| printed.iter().any(|line| line.starts_with(head));
        assert!(withdrew(
            "trust-wp: test::g error: verdict withdrawn - it reaches `test::h`"
        ));
        assert!(withdrew(
            "trust-wp: test::f error: verdict withdrawn - it reaches"
        ));
        assert_eq!(counters.verified, 1, "only k's credit stands");
        assert_eq!(counters.logic_assertions_verified, 0);
        assert_eq!(counters.errors, 3);
        assert!(unverified.contains("test::g") && unverified.contains("test::f"));
        assert!(!unverified.contains("test::k"));
        // Nothing more to withdraw.
        assert!(credits
            .withdraw_stale(&fns, &mut unverified, &mut counters)
            .is_empty());
    }

    #[test]
    fn a_callee_already_neutralized_in_the_proof_environment_withdraws_nothing() {
        let fns = chain();
        let mut credits = LogicCredits::default();
        let mut counters = VerificationCounters::default();
        // g was proved on an environment in which h was already lost (and
        // neutralized): its proof never had h's axiom to lean on.
        let excluded = HashSet::from(["test::h".to_string()]);
        credits.record(1, LogicCreditKind::Function, &excluded);
        counters.verified = 1;
        let mut unverified = excluded.clone();
        assert!(credits
            .withdraw_stale(&fns, &mut unverified, &mut counters)
            .is_empty());
        assert_eq!(counters.verified, 1);
        assert!(!unverified.contains("test::g"));
    }

    #[test]
    fn a_function_losing_its_own_axiom_does_not_withdraw_its_own_credit() {
        let fns = chain();
        let mut credits = LogicCredits::default();
        let mut counters = VerificationCounters::default();
        // k's assertions were credited, then its own ensures lane failed.
        credits.record(3, LogicCreditKind::Assertions, &HashSet::new());
        counters.logic_assertions_verified = 1;
        let mut unverified = HashSet::from(["test::k".to_string()]);
        assert!(credits
            .withdraw_stale(&fns, &mut unverified, &mut counters)
            .is_empty());
        assert_eq!(counters.logic_assertions_verified, 1);
    }
}
