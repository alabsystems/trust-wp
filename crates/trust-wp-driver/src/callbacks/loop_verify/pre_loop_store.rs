// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Whether a model of a loop VC is a run of the program, given the stores
//! through a reference before loop entry that no loop VC states.

use std::collections::HashSet;

use trust_wp_core::formula::PureExpr;

use super::expr_utils::expr_referenced_vars;

/// The names a store through a reference before loop entry may have changed
/// (`LoopBodyExpr::pre_loop_deref_stored_names`), and the names each premise
/// of a loop VC links.
///
/// No loop VC states such a store: each reads the name at its entry value,
/// under premises stated of the entry state (the precondition, a pre-loop
/// binding, a frame inferred from them). A model of a VC is a run of the
/// program only when no chain of premises links a stale name to what the
/// refuted goal reads: the program's own value for the name then satisfies
/// every premise the model's value did, and the goal is false either way
/// (loop_preservation_after_local_store_false). A chain that does link one may
/// be what rules the model in (loop_preservation_after_local_store_control).
/// Every name in one premise counts as linked, `old(..)` and `^p` included, so
/// the links over-approximate, and all they ever withhold is a refutation.
pub(in crate::callbacks) struct PreLoopStoreLinks<'a> {
    stored: &'a HashSet<String>,
    links: Vec<HashSet<String>>,
}

impl<'a> PreLoopStoreLinks<'a> {
    /// `premises` are the VC's assumptions; each of `bindings` is a
    /// variable and the value an effect or a pre-loop binding gives it.
    pub(in crate::callbacks) fn new<'e>(
        stored: &'a HashSet<String>,
        premises: impl IntoIterator<Item = &'e PureExpr>,
        bindings: impl IntoIterator<Item = (&'e String, &'e PureExpr)>,
    ) -> Self {
        let mut links: Vec<HashSet<String>> = if stored.is_empty() {
            Vec::new()
        } else {
            premises.into_iter().map(expr_referenced_vars).collect()
        };
        if !stored.is_empty() {
            links.extend(bindings.into_iter().map(|(name, value)| {
                let mut link = expr_referenced_vars(value);
                link.insert(name.clone());
                link
            }));
        }
        Self { stored, links }
    }

    /// Why a refutation of `goals` is no run of the program, when a chain of
    /// premises links what they read to a stale name.
    pub(in crate::callbacks) fn reason<'e>(
        &self,
        goals: impl IntoIterator<Item = &'e PureExpr>,
    ) -> Option<String> {
        self.linked(goals).map(|name| {
            format!(
                "the loop VC does not state a store through a reference before loop entry (`{name}`)"
            )
        })
    }

    /// The first stale name (in name order) a chain of premises links to what
    /// `goals` read. The links do not depend on why a name is stale, so a
    /// caller with another set of names the VC leaves free (a havoc standing
    /// for a value code before the loop fixed) asks the same question.
    pub(in crate::callbacks) fn linked<'e>(
        &self,
        goals: impl IntoIterator<Item = &'e PureExpr>,
    ) -> Option<&'a String> {
        if self.stored.is_empty() {
            return None;
        }
        let mut reached: HashSet<String> =
            goals.into_iter().flat_map(expr_referenced_vars).collect();
        loop {
            let before = reached.len();
            for link in &self.links {
                if link.iter().any(|name| reached.contains(name)) {
                    reached.extend(link.iter().cloned());
                }
            }
            if reached.len() == before {
                break;
            }
        }
        let stored: &'a HashSet<String> = self.stored;
        stored
            .iter()
            .filter(|name| reached.contains(name.as_str()))
            .min()
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{HashMap, HashSet},
        sync::Arc,
    };

    use trust_wp_core::formula::{BinOp, PureExpr};

    use super::PreLoopStoreLinks;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn bin(lhs: PureExpr, op: BinOp, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs))
    }

    /// A refutation stands when no premise links what its goal reads to a
    /// name a store before the loop changed, and is withheld when the goal
    /// reads the name or a premise chain reaches it
    /// (loop_preservation_after_local_store_{control,false}).
    #[test]
    fn a_stale_name_withholds_only_what_a_premise_chain_links_it_to() {
        let stored = HashSet::from(["k".to_string()]);
        let binding_k = bin(var("k"), BinOp::Eq, PureExpr::Int(0));
        let binding_j = bin(var("j"), BinOp::Eq, var("k"));
        let i_bound = bin(var("i"), BinOp::Lt, PureExpr::Int(3));
        let body = HashMap::from([("i".to_string(), bin(var("i"), BinOp::Add, PureExpr::Int(1)))]);
        let links = PreLoopStoreLinks::new(&stored, [&binding_k, &i_bound], body.iter());
        let independent = bin(var("i"), BinOp::Le, PureExpr::Int(2));
        assert_eq!(links.reason([&independent]), None);
        let guarded = bin(binding_k.clone(), BinOp::Implies, independent.clone());
        assert!(links
            .reason([&guarded])
            .is_some_and(|reason| reason.contains("`k`")));

        let chained = PreLoopStoreLinks::new(&stored, [&binding_k, &binding_j], body.iter());
        let reads_j = bin(var("i"), BinOp::Lt, var("j"));
        assert!(chained.reason([&reads_j]).is_some());
        assert_eq!(chained.reason([&independent]), None);

        let through_effect = HashMap::from([("s".to_string(), var("k"))]);
        let effect_links = PreLoopStoreLinks::new(&stored, [], through_effect.iter());
        let reads_s = bin(var("s"), BinOp::Eq, PureExpr::Int(7));
        assert!(effect_links.reason([&reads_s]).is_some());
    }

    /// With nothing stored before the loop no refutation is withheld, and a
    /// pointee or prophecy of a stored reference counts as reading it.
    #[test]
    fn nothing_stored_withholds_nothing_and_a_pointee_reads_its_reference() {
        let nothing = HashSet::new();
        let k_zero = bin(var("k"), BinOp::Eq, PureExpr::Int(0));
        assert_eq!(
            PreLoopStoreLinks::new(&nothing, [&k_zero], []).reason([&k_zero]),
            None
        );
        let stored = HashSet::from(["a".to_string()]);
        let links = PreLoopStoreLinks::new(&stored, [], []);
        let pointee = PureExpr::Deref(Arc::new(var("a")));
        let prophecy = PureExpr::Final(Arc::new(var("a")));
        assert!(links.reason([&pointee]).is_some());
        assert!(links.reason([&prophecy]).is_some());
        assert_eq!(links.reason([&var("b")]), None);
    }
}
