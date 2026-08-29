// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use trust_wp_core::formula::{ExprSort, PureExpr};

/// Program-point substitutions plus authoritative base-name sorts from MIR.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct NameSubstitutions {
    pub(crate) exprs: HashMap<String, PureExpr>,
    pub(crate) name_sorts: HashMap<String, Option<ExprSort>>,
}

impl NameSubstitutions {
    pub(crate) fn new(
        exprs: HashMap<String, PureExpr>,
        name_sorts: HashMap<String, Option<ExprSort>>,
    ) -> Self {
        Self { exprs, name_sorts }
    }

    pub(crate) fn extend(&mut self, other: Self) {
        self.exprs.extend(other.exprs);
        self.name_sorts.extend(other.name_sorts);
    }
}

impl From<HashMap<String, PureExpr>> for NameSubstitutions {
    fn from(exprs: HashMap<String, PureExpr>) -> Self {
        Self::new(exprs, HashMap::new())
    }
}

impl Deref for NameSubstitutions {
    type Target = HashMap<String, PureExpr>;

    fn deref(&self) -> &Self::Target {
        &self.exprs
    }
}

impl DerefMut for NameSubstitutions {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.exprs
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(ExprSort::Int))
    }

    #[test]
    fn test_new_creates_with_both_maps() {
        let mut exprs = HashMap::new();
        exprs.insert("x".to_string(), int_var("x"));
        let mut sorts = HashMap::new();
        sorts.insert("x".to_string(), Some(ExprSort::Int));

        let ns = NameSubstitutions::new(exprs.clone(), sorts.clone());
        assert_eq!(ns.exprs, exprs);
        assert_eq!(ns.name_sorts, sorts);
    }

    #[test]
    fn test_default_is_empty() {
        let ns = NameSubstitutions::default();
        assert!(ns.exprs.is_empty());
        assert!(ns.name_sorts.is_empty());
    }

    #[test]
    fn test_from_hashmap_sets_exprs_only() {
        let mut exprs = HashMap::new();
        exprs.insert("y".to_string(), PureExpr::Int(42));
        let ns: NameSubstitutions = exprs.clone().into();
        assert_eq!(ns.exprs, exprs);
        assert!(ns.name_sorts.is_empty());
    }

    #[test]
    fn test_extend_merges_both_maps() {
        let mut ns1 = NameSubstitutions::default();
        ns1.exprs.insert("a".to_string(), PureExpr::Int(1));
        ns1.name_sorts.insert("a".to_string(), Some(ExprSort::Int));

        let mut ns2 = NameSubstitutions::default();
        ns2.exprs.insert("b".to_string(), PureExpr::Int(2));
        ns2.name_sorts.insert("b".to_string(), Some(ExprSort::Bool));

        ns1.extend(ns2);
        assert_eq!(ns1.exprs.len(), 2);
        assert_eq!(ns1.name_sorts.len(), 2);
        assert_eq!(ns1.exprs.get("b"), Some(&PureExpr::Int(2)));
        assert_eq!(ns1.name_sorts.get("b"), Some(&Some(ExprSort::Bool)));
    }

    #[test]
    fn test_extend_overwrites_on_conflict() {
        let mut ns1 = NameSubstitutions::default();
        ns1.exprs.insert("x".to_string(), PureExpr::Int(1));
        ns1.name_sorts.insert("x".to_string(), Some(ExprSort::Int));

        let mut ns2 = NameSubstitutions::default();
        ns2.exprs.insert("x".to_string(), PureExpr::Bool(true));
        ns2.name_sorts.insert("x".to_string(), Some(ExprSort::Bool));

        ns1.extend(ns2);
        assert_eq!(ns1.exprs.len(), 1);
        assert_eq!(ns1.exprs.get("x"), Some(&PureExpr::Bool(true)));
        assert_eq!(ns1.name_sorts.get("x"), Some(&Some(ExprSort::Bool)));
    }

    #[test]
    fn test_deref_accesses_exprs() {
        let mut exprs = HashMap::new();
        exprs.insert("z".to_string(), PureExpr::Int(99));
        let ns: NameSubstitutions = exprs.into();
        // Deref should give us the exprs HashMap
        assert_eq!(ns.get("z"), Some(&PureExpr::Int(99)));
        assert_eq!(ns.len(), 1);
    }

    #[test]
    fn test_deref_mut_modifies_exprs() {
        let mut ns = NameSubstitutions::default();
        // DerefMut lets us insert directly via HashMap methods
        ns.insert("w".to_string(), PureExpr::Bool(false));
        assert_eq!(ns.exprs.get("w"), Some(&PureExpr::Bool(false)));
    }

    #[test]
    fn test_eq_compares_both_maps() {
        let mut ns1 = NameSubstitutions::default();
        ns1.exprs.insert("a".to_string(), PureExpr::Int(1));
        ns1.name_sorts.insert("a".to_string(), Some(ExprSort::Int));

        let mut ns2 = NameSubstitutions::default();
        ns2.exprs.insert("a".to_string(), PureExpr::Int(1));
        ns2.name_sorts.insert("a".to_string(), Some(ExprSort::Int));

        assert_eq!(ns1, ns2);

        // Change name_sorts only — should differ
        ns2.name_sorts.insert("a".to_string(), Some(ExprSort::Bool));
        assert_ne!(ns1, ns2);
    }
}
