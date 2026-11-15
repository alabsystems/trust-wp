// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::common::collect_type_invariant_clauses;

#[test]
fn an_impl_of_a_foreign_traits_method_holds_no_parameter_premise_and_keeps_its_goals() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

impl Clone for Sum10 {
    fn clone(&self) -> Sum10 {
        Sum10(self.0, self.1)
    }
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses(source, "clone", &["self"]);
    assert!(
        reqs.is_empty(),
        "std runs `clone` from code no lane walks, so no call can owe a premise: {reqs:?}"
    );
    assert!(
        !enss.is_empty(),
        "`inv(result)` stays a goal of the body: {enss:?}"
    );
}

#[test]
fn an_impl_of_a_local_traits_method_keeps_its_parameter_premise() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

pub trait Local {
    fn take(&self, s: Sum10) -> i32;
}

impl Local for Sum10 {
    fn take(&self, s: Sum10) -> i32 {
        s.0
    }
}
"#;
    let (reqs, _) = collect_type_invariant_clauses(source, "take", &["self", "s"]);
    assert!(
        !reqs.is_empty(),
        "every route into a local trait's impl is a call a lane walks: {reqs:?}"
    );
}
