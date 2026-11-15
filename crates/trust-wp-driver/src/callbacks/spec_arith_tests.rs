// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

fn u32_operand() -> Operand {
    Operand::Machine {
        bits: 32,
        signed: false,
    }
}

#[test]
fn a_machine_add_reads_wrapping_at_its_type() {
    let reading = reading_of_sites(&[(ArithOp::Add, u32_operand())], false);
    assert_eq!(
        reading.kinds[&ArithOp::Add],
        KindReading {
            reading: OpReading::Wrapping(MachineInt::new(32, false).unwrap()),
            typed: Some(1),
        }
    );
}

#[test]
fn an_int_add_reads_mathematically() {
    let reading = reading_of_sites(
        &[(ArithOp::Add, Operand::Int), (ArithOp::Add, Operand::Int)],
        false,
    );
    assert_eq!(
        reading.kinds[&ArithOp::Add],
        KindReading {
            reading: OpReading::Mathematical,
            typed: Some(2),
        }
    );
}

#[test]
fn one_kind_at_two_types_is_refused() {
    for other in [
        Operand::Int,
        Operand::Machine {
            bits: 8,
            signed: false,
        },
    ] {
        let reading = reading_of_sites(
            &[(ArithOp::Add, u32_operand()), (ArithOp::Add, other)],
            false,
        );
        assert!(matches!(
            reading.kinds[&ArithOp::Add].reading,
            OpReading::Refused(_)
        ));
    }
}

#[test]
fn a_dropped_subterm_refuses_a_machine_kind_and_reads_the_rest_by_syntax() {
    let reading = reading_of_sites(
        &[(ArithOp::Add, u32_operand()), (ArithOp::Sub, Operand::Int)],
        true,
    );
    assert!(matches!(
        reading.kinds[&ArithOp::Add].reading,
        OpReading::Refused(_)
    ));
    assert_eq!(reading.kinds[&ArithOp::Sub].reading, OpReading::Syntactic);
    assert_eq!(reading.kinds[&ArithOp::Mul].reading, OpReading::Syntactic);
}

#[test]
fn a_shift_reads_at_its_shifted_operand_type() {
    for op in [ArithOp::Shl, ArithOp::Shr] {
        let reading = reading_of_sites(&[(op, u32_operand())], false);
        assert_eq!(
            reading.kinds[&op].reading,
            OpReading::Wrapping(MachineInt::new(32, false).unwrap()),
            "{op:?}"
        );
    }
}

#[test]
fn division_complement_and_128_bits_on_machine_integers_are_refused() {
    for op in [ArithOp::Div, ArithOp::Rem, ArithOp::Not] {
        let reading = reading_of_sites(&[(op, u32_operand())], false);
        assert!(
            matches!(reading.kinds[&op].reading, OpReading::Refused(_)),
            "{op:?}"
        );
    }
    let wide = Operand::Machine {
        bits: 128,
        signed: true,
    };
    let reading = reading_of_sites(&[(ArithOp::Add, wide)], false);
    assert!(matches!(
        reading.kinds[&ArithOp::Add].reading,
        OpReading::Refused(_)
    ));
}

#[test]
fn the_stubs_are_known_by_their_path_in_trust_wp_std() {
    let path = |names: &[&str]| names.iter().map(|n| (*n).to_string()).collect::<Vec<_>>();
    assert_eq!(
        stub_operator(&path(&["__spec_tc", "AddTc", "add_tc"])),
        Some(ArithOp::Add)
    );
    assert_eq!(
        stub_operator(&path(&["__spec_tc", "sub_lit"])),
        Some(ArithOp::Sub)
    );
    assert_eq!(
        stub_operator(&path(&["__spec_tc", "NegTc", "neg_tc"])),
        Some(ArithOp::Neg)
    );
    assert_eq!(
        stub_operator(&path(&["logic", "ops", "AddLogic", "add"])),
        None
    );
    assert_eq!(stub_operator(&path(&["__spec_tc", "equal"])), None);
}
