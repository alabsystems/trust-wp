// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The driver lane reads a reference level, a pattern's bindings and a binder
//! where a contract writes them: a borrow a `let` binds, a binding by
//! reference, a reference pattern, `^` of a borrow, the view of a `&mut`, a
//! binder that shadows a parameter, a const generic argument. The contract
//! parser is the one the bundle lane uses, so both lanes read these alike.

use std::path::Path;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> (bool, String) {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/reference_level_contract_tests");
    let output = nested_cargo("check")
        .current_dir(fixture_dir("reference_level_contracts"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["--quiet", "--locked", "--bin", bin])
        .output()
        .expect("failed to run targo check for the reference-level fixture");
    (
        output.status.success(),
        trust_wp_test_utils::fixture_stderr(&output),
    )
}

/// Each was refuted (a counterexample to a true contract) or unknown while
/// the text was read another way: `let r = &x; *r` read `*x`, `let &mut t =
/// p` bound `p`, `let x @ y = x + 1` read `y` as the new `x` plus one, `let
/// (a, b) = (b, a)` read the new `b` as the new `a`, `p@` of a `&mut` was read
/// at entry where `*p` was the final value, a `&mut` parameter bound or
/// branched before `*` was read at entry, a destructuring closure parameter
/// bound the wrong fields, and `(a)` was a one-element tuple.
#[test]
#[timeout(600_000)]
fn a_true_contract_is_read_where_the_contract_writes_it() {
    let (success, stderr) = run_fixture("should_verify");
    let names = [
        "id",
        "id_by_reference",
        "id_by_reference_alias",
        "read_through",
        "inc",
        "succ",
        "inc_view",
        "entry_value",
        "alias_reads_the_value_once",
        "swap_binds_the_old_values",
        "logic_unfolding_at_a_negative",
        "let_shadows_a_mut_ref_view",
        "match_rebinds_the_param",
        "if_let_binds_the_param",
        "deref_of_a_branch",
        "alias_of_a_branch",
        "final_of_an_alias",
        "closure_alias_reads_the_first_field",
        "parenthesized_pattern",
    ];
    for name in names {
        assert!(
            stderr.contains(&format!("trust-wp: {name} verified")),
            "`{name}` is not verified; stderr: {stderr}"
        );
    }
    assert!(
        success
            && stderr.contains(&format!(
                "trust-wp: {} verified, 0 failed, 0 errors",
                names.len()
            )),
        "stderr: {stderr}"
    );
}

/// Each false contract was verified at exit 0, or would be under the reading
/// it names: a reference pattern read as the matched value, `p@` read at
/// entry beside a final `*p`, an alias
/// or a tuple pattern reading a name it rebinds, a const generic argument
/// read as a type and dropped, a substitution capturing a binder's name
/// (`result := y` under `forall<y>`, a logic function unfolded at `i@` under
/// its `forall<i>`), and a binder that shadows a `&mut` param read as it.
#[test]
#[timeout(600_000)]
fn a_false_contract_is_not_verified() {
    assert_no_false_contract_verifies(
        "should_not_verify",
        &[
            "inc_let",
            "inc_match",
            "star_plus_one_and_view_unchanged",
            "star_plus_one_and_view_call_unchanged",
            "view_unchanged_and_referent_view_plus_one",
            "star_plus_one_and_view_is_entry",
            "alias_rereads_the_value",
            "swap_reads_the_new_names",
            "const_block_arguments_differ",
            "logic_unfolding_captures",
            "result_substitution_captures",
            "forall_shadows_a_param",
            "let_shadows_a_mut_ref",
            "let_shadows_a_mut_ref_view",
            "forall_shadows_a_mut_ref",
        ],
    );
}

/// Each binds or branches a `&mut` parameter before reading its referent, in
/// a clause that reads `old`: a `match`, `let`, `if let` or tuple pattern, a
/// branch of an `if` or `match`, a field of a tuple. The `*p -> ^p` rewrite
/// was keyed by the spelling `p`, so each read stayed the entry value and the
/// false contract verified at exit 0.
#[test]
#[timeout(600_000)]
fn a_bound_or_branched_mut_ref_param_is_read_at_the_clause_state() {
    assert_no_false_contract_verifies(
        "mut_ref_param_bindings",
        &[
            "match_rebinds_the_param",
            "match_rebinds_the_param_u8",
            "match_rebinds_the_param_in_a_conjunction",
            "let_rebinds_the_param",
            "if_let_rebinds_the_param",
            "tuple_pattern_rebinds_the_param",
            "match_rebinds_the_param_view",
            "match_binds_the_param",
            "if_let_binds_the_param",
            "let_binds_the_param_view",
            "deref_of_a_branch",
            "deref_of_a_branch_of_two",
            "deref_of_a_branch_on_old",
            "deref_of_a_match",
            "deref_of_a_match_on_a_param",
            "deref_of_a_tuple_field",
        ],
    );
}

/// A destructuring closure parameter's names were bound to the fields at
/// their flattened positions, and two calls differing only in a type argument
/// were read as one call; each false contract verified at exit 0.
#[test]
#[timeout(600_000)]
fn a_closure_parameter_and_a_type_argument_bind_what_they_name() {
    assert_no_false_contract_verifies(
        "closure_and_type_arguments",
        &[
            "closure_alias_reads_the_first_field",
            "closure_nested_tuple_reads_the_inner_field",
            "type_arguments_differ",
        ],
    );
}

fn assert_no_false_contract_verifies(bin: &str, names: &[&str]) {
    let (success, stderr) = run_fixture(bin);
    assert!(!success, "{bin}: {stderr}");
    for name in names {
        assert!(
            stderr.contains(&format!("trust-wp: {name} ")),
            "{bin}: `{name}` has no verdict; stderr: {stderr}"
        );
        assert!(
            !stderr.contains(&format!("trust-wp: {name} verified")),
            "{bin}: `{name}` verified a false contract; stderr: {stderr}"
        );
    }
    assert!(stderr.contains("trust-wp: 0 verified"), "{bin}: {stderr}");
}

/// `^` of a shared borrow has no reading, however the borrow reaches it: a
/// `let` binding it, a branch of an `if` or a `match`. Each was read as `^p`
/// (the branches' mismatched level was dropped, and the driver reads a
/// dropped borrow as its operand) and verified. Each clause is refused by
/// name before any verdict; the chained comparison keeps it from the Rust
/// type-check.
#[test]
#[timeout(600_000)]
fn the_final_value_of_a_borrow_is_refused() {
    for (bin, refusal) in [
        (
            "final_of_bound_borrow",
            "`^` of `r`, bound to the borrow `&p`, has no reading",
        ),
        (
            "final_of_a_branch_borrow",
            "`^` of a value that is the borrow `&p` in one branch and not in another has no \
             reading",
        ),
        (
            "final_of_a_match_borrow",
            "`^` of the borrow `&p` has no reading",
        ),
    ] {
        let (success, stderr) = run_fixture(bin);
        assert!(!success, "{bin}: {stderr}");
        assert!(stderr.contains(refusal), "{bin}: {stderr}");
        assert!(!stderr.contains("verified"), "{bin}: {stderr}");
    }
}

/// A read of a parameter at a reference level its type does not have (`*x`
/// of an `x: i32`, however spelled; `^y` of a `y: &i32`), and a read of a
/// `&mut` parameter's referent through a value that holds the parameter
/// other than by its name (a `let` of a tuple, a constructor pattern), are
/// refused by name before any verdict. `*t` of `let ref a @ t = x` was
/// unknown while the same `*x` spelled directly was read as `x`; the state
/// rule is keyed by the parameter's name and read the entry value where it
/// could not see it.
#[test]
#[timeout(600_000)]
fn a_read_the_state_rule_cannot_place_is_refused() {
    let (success, stderr) = run_fixture("unplaced_mut_ref_read");
    assert!(!success, "{stderr}");
    for (clause, through) in [
        ("{ let t = (p, 0); *t.0 == old(*p) }", "reads through `t`"),
        (
            "match Some(p) { Some(q) => *q == old(*p), None => true }",
            "reads through `q`",
        ),
        (
            "{ let ref a @ t = x; *t == result && 0 < 1 < 2 }",
            "`*x` reads through the parameter `x`, which is not a reference",
        ),
        (
            "*x == result && 0 < 1 < 2",
            "`*x` reads through the parameter `x`, which is not a reference",
        ),
        (
            "^y == result && 0 < 1 < 2",
            "`^y` is the final value of the parameter `y`, which is a shared reference",
        ),
    ] {
        assert!(
            stderr.contains(&format!("failed to parse ensures '{clause}'"))
                && stderr.contains(through),
            "`{clause}` is not refused: {stderr}"
        );
    }
    assert!(!stderr.contains("verified ✓"), "{stderr}");
}
