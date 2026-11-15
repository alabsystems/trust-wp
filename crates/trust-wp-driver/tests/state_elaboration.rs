// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The state each read of a parameter denotes is decided once
//! (`formula::elaborate::state`) and read alike by a function's own lane, by
//! every call of the function and by a closure's contract: the lane that
//! proves a clause and the call credited with it cannot read it apart.

use std::path::Path;

use ntest::timeout;
use trust_wp_test_utils::{fixture_dir, nested_cargo, trust_wp_rustc_path};

fn run_fixture(bin: &str) -> String {
    let target_dir =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../target/state_elaboration_tests");
    let output = nested_cargo("check")
        .current_dir(fixture_dir("state_elaboration"))
        .env("CARGO_TARGET_DIR", target_dir)
        .env("RUSTC_WRAPPER", trust_wp_rustc_path())
        .env("TRUST_WP_ARGS", "--verify")
        .args(["--quiet", "--locked", "--bin", bin])
        .output()
        .expect("failed to run targo check for the state-elaboration fixture");
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// Each name has a verdict, or a refusal of its contract naming it, and none
/// is verified.
fn assert_none_verified(bin: &str, stderr: &str, names: &[&str]) {
    for name in names {
        assert!(
            stderr.contains(&format!("trust-wp: {name} "))
                || stderr.contains(&format!("' of `{name}`: ")),
            "{bin}: `{name}` has no verdict; stderr: {stderr}"
        );
        assert!(
            !stderr.contains(&format!("trust-wp: {name} verified")),
            "{bin}: `{name}` verified a false contract; stderr: {stderr}"
        );
    }
}

fn assert_all_verified(bin: &str, stderr: &str, names: &[&str]) {
    for name in names {
        assert!(
            stderr.contains(&format!("trust-wp: {name} verified")),
            "{bin}: `{name}` is not verified; stderr: {stderr}"
        );
    }
}

/// A callee's pre-Creusot postcondition (`*a == old(*b)` on `swap`) was
/// proved by the callee's lane with `*a` the value `a` is left with, and
/// read at the call with `*a` the value at the call: each caller verified a
/// false claim about its entry values (swap's two arguments equal, replace's
/// result the value it stores, a method's field read, a set's entry value, a
/// closure-style postcondition's twin).
#[test]
#[timeout(600_000)]
fn a_call_reads_a_callee_clause_as_the_callee_proves_it() {
    let bin = "call_old_dialect_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &[
            "swap_caller",
            "replace_caller",
            "put_caller",
            "set_caller",
            "inc_caller",
            "local_inc_false",
            "five_caller",
        ],
    );
}

/// The true readings: each caller is credited with the post-state the
/// callee's lane proved. Each was unknown, vacuous or FAILED before.
#[test]
#[timeout(600_000)]
fn a_caller_is_credited_with_the_callee_post_state() {
    let bin = "call_old_dialect_true";
    let stderr = run_fixture(bin);
    assert_all_verified(
        bin,
        &stderr,
        &[
            "swap_caller_control",
            "replace_caller_control",
            "put_caller_control",
            "set_caller_control",
            "inc_caller_control",
            "local_inc_true",
            "local_inc_view_true",
            "five_caller_control",
            "pair_caller_control",
        ],
    );
}

/// A callee's entry state is the call's pre-state: `old(e)` was read at the
/// CALLER's entry, and an argument read through a reference after a store
/// the translation does not see as the pointee's entry value.
#[test]
#[timeout(600_000)]
fn a_call_reads_the_callee_entry_state_at_the_call() {
    let bin = "call_pre_state_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &[
            "get_caller_false",
            "get_creusot_caller_false",
            "take_false",
            "swap_after_write_false",
            "succ_after_write_false",
        ],
    );
}

/// A closure's `&mut` parameter read through a binder under `old(..)`, and a
/// dereference of a closure's value parameter, verified: D-100's alias
/// resolution and refusals returned early for a closure.
#[test]
#[timeout(600_000)]
fn a_closure_parameter_is_read_as_a_function_parameter_is() {
    let bin = "closure_contracts_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &[
            "let_alias::{closure#0}",
            "match_alias::{closure#0}",
            "if_let_alias::{closure#0}",
        ],
    );
    for (clause, reason) in [
        (
            "*x == result && 0 < 1 < 2",
            "`*x` reads through the parameter `x`, which is not a reference",
        ),
        (
            "{ let t = (p, 0); *t.0 == old(*p) }",
            "reads through `t`, which holds a `&mut` parameter",
        ),
    ] {
        assert!(
            stderr.contains(&format!("failed to parse ensures '{clause}'"))
                && stderr.contains(reason),
            "{bin}: `{clause}` is not refused: {stderr}"
        );
    }
    assert!(
        !stderr.contains("deref_of_a_value::{closure#0} verified")
            && !stderr.contains("unplaced::{closure#0} verified"),
        "{bin}: {stderr}"
    );

    let bin = "closure_contracts_true";
    let stderr = run_fixture(bin);
    assert_all_verified(
        bin,
        &stderr,
        &[
            "let_alias_control::{closure#0}",
            "plain_control::{closure#0}",
        ],
    );
}

/// A `&mut` a parameter holds without being it has no placement, in either
/// dialect: `*p == old(*p)` of a destructured `p` verified. A destructured
/// binding is its parameter's projection (D-179), so its clauses reach this
/// rule as a tuple parameter's field does, spelled over the positional name.
#[test]
#[timeout(600_000)]
fn a_mut_ref_a_parameter_holds_is_refused() {
    let bin = "held_mut_ref_params";
    let stderr = run_fixture(bin);
    for clause in [
        "*(__twp_arg0.0) == old(*(__twp_arg0.0))",
        "(^(__twp_arg0.0))@ == (*(__twp_arg0.0))@ + 1",
        "*t.0 == old(*t.0)",
        "^a[0] == *a[0] + 1i32",
    ] {
        let refusal = format!("failed to parse ensures '{clause}'");
        assert!(
            stderr.lines().any(|line| line.contains(&refusal)
                && line.contains("a `&mut` a parameter holds without being it has no placement")),
            "{bin}: `{clause}` is not refused by the placement rule: {stderr}"
        );
    }
    assert!(
        !stderr.contains("names a parameter pattern binding it cannot be stated over"),
        "{bin}: a destructured `&mut`'s `requires` is its projection, read at entry: {stderr}"
    );
    assert!(!stderr.contains("verified ✓"), "{bin}: {stderr}");
    assert!(!stderr.contains("FAILED"), "{bin}: {stderr}");
}

/// A parameter that is no `&mut` is one value in every state, so `old(e)`
/// reads it as itself wherever in `e` it is: `old(v@) + 1`, `old(v@ + 1)` and
/// `old(v@ + i)` under a quantifier were each refuted with a fresh `old_v`
/// unrelated to `v`, while only the exact `old(v)` was read as `v`.
#[test]
#[timeout(600_000)]
fn a_value_parameter_under_old_is_itself() {
    let bin = "value_param_old";
    let stderr = run_fixture(bin);
    assert_all_verified(
        bin,
        &stderr,
        &["old_of_a_view", "old_of_a_sum", "old_under_a_quantifier"],
    );
    assert_none_verified(bin, &stderr, &["old_under_a_quantifier_false"]);
}

/// A pre-Creusot `*p` of a parameter the result may borrow (a raw pointer,
/// `Rc<i32>`, `Vec<i32>`, a struct holding a raw pointer, a recursive type, a
/// trait method's impl, a `&Cell`) was read at entry by the callee's own lane, which
/// proved each callee's false `*p == old(*p)`, and as the value `p` is left
/// with at each call, crediting each caller with `^x == *x`. Both lanes now
/// refuse it, from the signature.
#[test]
#[timeout(600_000)]
fn a_pre_creusot_read_of_a_lent_final_is_no_fact_in_either_lane() {
    let bin = "call_lent_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &[
            "leak_caller",
            "leak_handle_caller",
            "share_caller",
            "bump_and_list_caller",
            "tag_caller",
            "generic_caller",
            "concrete_caller",
            "give_caller",
        ],
    );
    for callee in [
        "leak",
        "leak_handle",
        "share",
        "bump_and_list",
        "tag",
        "<U as Leak2>::leak2",
        "give",
    ] {
        assert!(
            !stderr.contains(&format!("trust-wp: {callee} verified")),
            "{bin}: `{callee}` verified a false contract; stderr: {stderr}"
        );
    }
    assert!(
        stderr.contains("the returned value may borrow it"),
        "{bin}: the lent final read is not refused by name; stderr: {stderr}"
    );
}

/// A shared reborrow lends nothing a caller can write through: the result
/// cannot carry the borrow (`mut_borrow::may_carry_borrow`), so the callee's
/// pre-Creusot `*p` is the value `p` is left with in its lane and at the
/// call. The call once refused it for the region alone.
#[test]
#[timeout(600_000)]
fn a_shared_reborrow_lends_nothing() {
    let bin = "call_lent_true";
    let stderr = run_fixture(bin);
    assert_all_verified(bin, &stderr, &["inc_peek_caller"]);
}

/// A shared reference to a referent that owns a cell through a `Box` lends
/// the borrow (`Box<Cell<T>>` is `Freeze`, the cell is not inline): each
/// callee's pre-Creusot `*p == old(*p)` has no reading, in its lane or at
/// its call. Both halves verified when `Freeze` alone decided it.
#[test]
#[timeout(600_000)]
fn a_shared_reference_to_a_boxed_cell_lends_the_borrow() {
    let bin = "call_lent_box_cell_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &["peek_caller", "field_caller", "give_box_caller"],
    );
    for callee in ["H::peek", "field", "give_box"] {
        assert!(
            !stderr.contains(&format!("trust-wp: {callee} verified")),
            "{bin}: `{callee}` verified a false contract; stderr: {stderr}"
        );
    }
}

/// A shared borrow of a `&mut` parameter's referent from which
/// interior-mutable memory is reachable is a write: `x.set(5)` left the
/// final value the entry value, inline, through a local reborrow, behind a
/// `Box`, in a field, and in the pre-Creusot dialect.
#[test]
#[timeout(600_000)]
fn a_write_through_interior_mutability_moves_the_final_value() {
    let bin = "interior_write_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &[
            "direct_set_cell",
            "local_reborrow_set",
            "boxed_set",
            "field_set",
            "old_dialect_set",
        ],
    );
}

/// A borrow another holder writes through after the call, by a write no
/// prophecy records (stored in another parameter, or returned as a
/// `&Cell`), has a final value no lane may read: each callee's clause is
/// refused by name and each caller is credited with nothing.
#[test]
#[timeout(600_000)]
fn a_final_another_holder_decides_has_no_reading() {
    let bin = "lent_elsewhere_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &["stash_caller", "stash_old_caller", "give_caller"],
    );
    for callee in ["stash", "stash_old", "stash_push", "stash_insert", "give"] {
        assert!(
            !stderr.contains(&format!("trust-wp: {callee} verified")),
            "{bin}: `{callee}` verified a false contract; stderr: {stderr}"
        );
    }
    assert!(
        stderr.contains("another parameter may hold its borrow after the call")
            && stderr.contains("whoever holds it decides that value"),
        "{bin}: the lent finals are not refused by name; stderr: {stderr}"
    );
}

/// A callee clause silent about a `&mut` argument says nothing of its final
/// value, through a reborrow of a reborrow too; a clause that states it is
/// credited, and two `&mut` of one lifetime whose referents hold no borrow
/// lend nothing to each other.
#[test]
#[timeout(600_000)]
fn a_callee_clause_is_all_a_caller_learns_of_a_reborrowed_argument() {
    let bin = "unmentioned_argument";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &["keep_caller", "keep_through_local", "keep_assert"],
    );
    assert!(
        !stderr.contains("keep_assert verified"),
        "{bin}: an assertion after the call learned the argument's final value; stderr: {stderr}"
    );
    assert_all_verified(
        bin,
        &stderr,
        &["keep", "inc", "inc_caller_reborrow", "swap_old"],
    );
}

/// A logic function reads its `&mut` parameter as one value, so a final
/// read inside it was the current one and `unchanged(p)` (`^q == *q`) held of
/// a write, a lend into another parameter, a cell write and an unmentioned
/// argument. Each such function is withdrawn and every goal naming it is
/// refused; one reading only `*q` keeps its reading (D-108).
#[test]
#[timeout(600_000)]
fn a_logic_function_reading_a_final_value_is_refused_wherever_it_is_read() {
    let bin = "final_read_logic_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &[
            "set5",
            "set5_flipped",
            "stash_logic",
            "stash_logic_caller",
            "cell_set",
            "keep_logic_caller",
        ],
    );
    assert!(
        stderr.contains("may name a logic function that reads a final value"),
        "{bin}: the goals naming a final-reading logic function are not refused by name; \
         stderr: {stderr}"
    );
    assert_all_verified(bin, &stderr, &["keep", "inc_beside"]);
}

/// A borrow stored in another parameter's slot through a projection naming
/// its late-bound region, or under an outlives bound implied by the return
/// type or an impl header, is lent: each callee's `^p == *p` is refused and
/// no caller is credited with its argument unchanged (D-108).
#[test]
#[timeout(600_000)]
fn a_lend_the_signature_implies_is_a_lend() {
    let bin = "lent_projection_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &["stash_proj_caller", "stash_ret_caller", "stash_impl_caller"],
    );
}

/// A `&mut` parameter over interior-mutable memory has no final value to
/// state whatever route writes it (an annotated loop, a copied `&Cell`),
/// while a `&mut` beside it keeps its reading (D-108).
#[test]
#[timeout(600_000)]
fn a_final_over_interior_mutable_memory_has_no_reading() {
    let bin = "interior_route_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &["loop_set", "copy_field_set", "copy_option_set"],
    );
    assert_all_verified(bin, &stderr, &["inc_beside_cell"]);
}

/// A final value is refused by what denotes it, not by the spelling `^`:
/// `resolve(x)`, a tuple binder of `x`, a quantified borrow equal to `x` and
/// a logic function reading `^q` each denote the final value of a `&mut`
/// over interior-mutable memory, `old(resolve(x))` reads a final value in the
/// entry state, and `resolve(x)` in a loop invariant is the final value it
/// denotes, not `true`; the true claims beside them keep their reading
/// (D-109).
#[test]
#[timeout(600_000)]
fn a_final_value_is_refused_however_denoted() {
    let bin = "final_denoted_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &[
            "copy_set_resolve",
            "copy_set_tuple_match",
            "copy_set_exists",
            "copy_set_logic",
            "set5_old_resolve",
            "set5_loop_resolve",
        ],
    );
    assert_all_verified(
        bin,
        &stderr,
        &["untouched", "inc_beside_copy", "flip_exists"],
    );
}

/// A call of a foreign item is read at the type it returns there: a `for`
/// loop over a `Range` (whose `next` declares a projection that may carry
/// anything and returns `Option<isize>`) and an `IndexMut` write on a
/// `Vec<i32>` are credited with their spec's `^self` (D-124).
#[test]
#[timeout(600_000)]
fn a_foreign_call_is_read_at_the_type_it_returns() {
    let bin = "foreign_call_instance_true";
    let stderr = run_fixture(bin);
    assert_all_verified(
        bin,
        &stderr,
        &["for_range_counts_to_n", "for_range_usize", "index_mut_set"],
    );
}

/// A borrow lent into another holder is refused beside a foreign call read
/// at its instance: `stash`'s `^it == *it` is refused by name, and neither
/// caller, which writes or advances the range through the slot, is credited
/// (D-107, D-124).
#[test]
#[timeout(600_000)]
fn a_lend_is_refused_beside_a_foreign_call_read_at_its_instance() {
    let bin = "foreign_call_instance_lent_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &["stash", "stash_then_write", "stash_then_advance"],
    );
    assert!(
        stderr.contains("' of `stash`: "),
        "{bin}: the lent final is not refused by name; stderr: {stderr}"
    );
}

/// `resolve(x)` is the by-value `true` only of a variable whose sort's shape
/// holds no borrow: the closure postcondition's `|r|` (an unannotated
/// `result`, also bound by a `let`, dereferenced or borrowed), a returned
/// `Vec` of a borrow and a snapshot of one read the caller's (or the body's)
/// borrow as a value, and verified, and so did a caller writing through the
/// borrow its callee claimed resolved; so did a struct whose `Option<&mut
/// i32>` field its declaration reads at `Int`, itself or through the field,
/// a quantifier's `&mut` binder, whose `^q` was its `*q`, and the binder of
/// a returned closure's state. A value whose borrow's final
/// value the lane does not name (a by-value `Box<&mut i32>`, a borrow at a
/// loop head) has its `resolve` refused, not refuted with a fresh final; the
/// true claims beside them keep their reading (D-126).
#[test]
#[timeout(600_000)]
fn resolve_is_by_value_only_of_a_sort_holding_no_borrow() {
    let bin = "resolve_by_value_false";
    let stderr = run_fixture(bin);
    assert_none_verified(
        bin,
        &stderr,
        &[
            "closure_resolve",
            "closure_resolve_unannotated",
            "closure_resolve_some",
            "closure_resolve_let",
            "closure_give",
            "closure_give_caller",
            "closure_resolve_deref",
            "closure_resolve_shared",
            "closure_resolve_bool",
            "vec_resolve",
            "snapshot_resolve",
            "snapshot_resolve_bool",
            "field_resolve",
            "field_projection_resolve",
            "quantified_resolve",
            "quantified_beside_inc",
            "quantified_shadowing",
            "closure_state_resolve",
        ],
    );
    for name in ["snapshot_resolve", "snapshot_resolve_bool"] {
        assert!(
            !stderr.contains(&format!("::{name} verified")),
            "{bin}: the snapshot's resolve was asserted in `{name}`; stderr: {stderr}"
        );
    }
    for name in ["box_untouched", "loop_untouched"] {
        assert_none_verified(bin, &stderr, &[name]);
        assert!(
            !stderr.contains(&format!("trust-wp: {name} FAILED")),
            "{bin}: the true resolve of `{name}` was refuted; stderr: {stderr}"
        );
    }
    assert_all_verified(bin, &stderr, &["give", "value", "untouched", "write_five"]);
}
