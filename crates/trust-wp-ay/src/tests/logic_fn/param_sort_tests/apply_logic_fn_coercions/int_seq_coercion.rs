// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test that apply_logic_fn coerces Int-sorted arguments when the function
/// parameter expects Seq (Uninterpreted). (#1965)
///
/// When a variable gets the default Int sort from first-declaration-wins
/// but the logic function's declared parameter sort is Seq, the coercion
/// should replace the Int-sorted term with a fresh Seq-sorted constant
/// instead of panicking. This affects 5+ tests (rusthorn/inc_some_*).
#[test]
#[timeout(30000)]
fn test_apply_logic_fn_coerces_int_arg_to_seq_param() {
    use trust_wp_core::logic::logic_fn_smt_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare a logic function with a Seq-typed parameter:
    //   seqsum(s: Seq) -> Int
    // Use a name without underscores so SMT name mangling is predictable.
    let seq_sort = Sort::seq(Sort::Int);
    let smt_name = logic_fn_smt_name("seqsum");
    let func_decl =
        encoder
            .solver
            .declare_fun(&smt_name, std::slice::from_ref(&seq_sort), Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, func_decl);

    // Create an Int-sorted variable (simulating first-declaration-wins default)
    let int_term = encoder
        .get_or_declare_var("mylist", Sort::Int)
        .expect("declare mylist as Int");
    assert_eq!(
        encoder.solver.get_sort(int_term),
        Sort::Int,
        "precondition: mylist should be Int"
    );

    // Calling apply_logic_fn should coerce Int→Seq without panic
    let result = encoder.apply_logic_fn("seqsum", &[int_term], None, None);
    assert!(
        result.is_ok(),
        "apply_logic_fn should coerce Int→Seq without panic (#1965): {result:?}"
    );
}

/// Test that apply_logic_fn coerces Seq-sorted arguments when the function
/// parameter expects Int. (#1965)
///
/// Symmetric case: function declared with Int parameter, but caller passes
/// a Seq-sorted term (from View encoding). Should coerce without panic.
#[test]
#[timeout(30000)]
fn test_apply_logic_fn_coerces_seq_arg_to_int_param() {
    use trust_wp_core::logic::logic_fn_smt_name;

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Declare a logic function with an Int-typed parameter:
    //   ident(x: Int) -> Int
    let smt_name = logic_fn_smt_name("ident");
    let func_decl = encoder
        .solver
        .declare_fun(&smt_name, &[Sort::Int], Sort::Int);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(smt_name, func_decl);

    // Create a Seq-sorted variable (simulating View encoding)
    let seq_sort = Sort::seq(Sort::Int);
    let seq_term = encoder
        .get_or_declare_var("vview", seq_sort)
        .expect("declare vview as Seq");
    assert!(
        encoder.solver.get_sort(seq_term).is_seq(),
        "precondition: vview should be Seq"
    );

    // Calling apply_logic_fn should coerce Seq→Int without panic
    let result = encoder.apply_logic_fn("ident", &[seq_term], None, None);
    assert!(
        result.is_ok(),
        "apply_logic_fn should coerce Seq→Int without panic (#1965): {result:?}"
    );
}
