// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Which binders of a claim a summary fact is about, decided on the claim as
//! written.
//!
//! A fact relates the values its names have at the obligation's binders: a
//! name free in the claim, or bound by the universal quantifiers the claim
//! opens with (`forall<p: &T> forall<q: &T> p != q`), each at its first
//! binding there. Any other binder of a fact's name binds another value: one
//! under an `exists` (`forall<q> !(exists<p> p == q)` holds for the `p` that
//! is `q`), under a connective, a `let` or a `match` arm, or one shadowing a
//! name the prefix already bound. Replay matches a fact by name, so each such
//! binder is renamed to a fresh name no fact spells.
//!
//! The prefix is the one the TEXT opens with. Alias resolution
//! ([`super::resolve_aliases`]) substitutes a `let` or an irrefutable `match`
//! away, which moves the quantifiers under it to the front: `{ let r = q;
//! forall<p: &Int> p != r }` resolves to `forall<p: &Int> p != q`, whose
//! opening `p` a disjointness fact on `p`, `q` then bound, proving a claim
//! the `p` that is `q` falsifies. So the parser binds a claim's facts before
//! it resolves aliases.

use std::{collections::HashSet, sync::Arc};

use crate::formula::PureExpr;

/// `claim`, as written, with every binder of a name in `fact_names` other
/// than the opening universal quantifiers' first binding of it renamed apart.
#[must_use]
pub fn bind_facts_to_the_written_prefix(
    claim: &PureExpr,
    fact_names: &HashSet<String>,
) -> PureExpr {
    if fact_names.is_empty() {
        return claim.clone();
    }
    bind_under_prefix(claim, fact_names, &mut HashSet::new())
}

/// [`bind_facts_to_the_written_prefix`] below the universal prefix: `seen`
/// holds the names the prefix has bound so far.
fn bind_under_prefix(
    expr: &PureExpr,
    fact_names: &HashSet<String>,
    seen: &mut HashSet<String>,
) -> PureExpr {
    if let PureExpr::Forall {
        var,
        var_sort,
        body,
        triggers,
    } = expr
    {
        if seen.insert(var.clone()) {
            return PureExpr::Forall {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(bind_under_prefix(body, fact_names, seen)),
                triggers: triggers.clone(),
            };
        }
    }
    expr.rename_binders_apart(|name| fact_names.contains(name))
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::contract_parser::parse_claim_binding_facts;

    fn bound(text: &str) -> String {
        let names: HashSet<String> = ["p", "q"].map(String::from).into_iter().collect();
        parse_claim_binding_facts(text, &names)
            .expect("parses")
            .0
            .to_string()
    }

    #[test]
    fn a_fact_binds_only_the_prefix_the_text_opens_with() {
        // The prefix: bound.
        let prefix = bound("forall<p: &Int> forall<q: &Int> p != q");
        assert!(!prefix.contains('$'), "{prefix}");
        // A quantifier under a `let`, a `match` or an `if let` is another
        // value, even when resolution substitutes the binder away.
        for text in [
            "{ let r = q; forall<p: &Int> p != r }",
            "match q { r => forall<p: &Int> p != r }",
            "if let r = q { forall<p: &Int> p != r } else { false }",
            "match (q,) { (r,) => forall<p: &Int> p != r }",
            "match (q, 0) { (r, _) => forall<p: &Int> p != r }",
            "forall<q: &Int> { let r = q; forall<p: &Int> p != r }",
        ] {
            let read = bound(text);
            assert!(read.contains("p$b"), "{text}: {read}");
        }
    }
}
