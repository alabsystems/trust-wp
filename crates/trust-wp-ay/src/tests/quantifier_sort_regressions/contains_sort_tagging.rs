// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::encoder::sort_context::{collect_all_sort_hints, SortHintAccumulator};

/// Bare Var receiver of `.contains()` must NOT be tagged as Seq. (#967)
///
/// `contains` is ambiguous between Seq and FSet. When a bare Var (not
/// View-wrapped) calls `.contains()` without `produces` context that would
/// indicate Seq, the variable must not be added to `acc.seqs`. Tagging it
/// as Seq would misroute FSet.contains to the Seq encoding path, causing
/// sort mismatch crashes in fmap_indexing tests.
///
/// Regression test for W1-942 fix (a65fbd63). The integration-level
/// fmap_indexing harness test catches this, but this unit test validates
/// the sort-hint-collection invariant directly.
#[test]
#[timeout(30000)]
fn fset_contains_does_not_tag_bare_var_as_seq() {
    // Build: fset_var.contains(x)
    // Bare Var receiver calling `.contains()` — ambiguous method.
    let contains_call = method_call(var("fset_var"), "contains", vec![var("x")]);

    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&contains_call, &mut acc);

    assert!(
        !acc.seqs.contains("fset_var"),
        "bare Var receiver of .contains() should NOT be tagged as Seq; seqs={:?}",
        acc.seqs,
    );
}

/// View-wrapped receiver of `.contains()` SHOULD be tagged as Seq. (#967)
///
/// Positive control: when `.contains()` is called on a View-wrapped
/// receiver, that indicates Seq (view coercion). This complements
/// `fset_contains_does_not_tag_bare_var_as_seq` by testing the
/// allowed tagging path.
#[test]
#[timeout(30000)]
fn view_wrapped_contains_tags_as_seq() {
    // Build: s.view().contains(x)
    // View-wrapped receiver — indicates Seq.
    let contains_call = method_call(view(var("s")), "contains", vec![var("x")]);

    let mut acc = SortHintAccumulator::new();
    collect_all_sort_hints(&contains_call, &mut acc);

    assert!(
        acc.seqs.contains("s_view"),
        "View-wrapped receiver of .contains() should be tagged as Seq; seqs={:?}",
        acc.seqs,
    );
}
