// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Collision-free mapping between Rust source variables and AY identities.
//!
//! AY reserves native theory/operator spellings such as `default` and its
//! private `__ay_` namespace. Rust identifiers can still reach the verifier
//! with those spellings (MIR locals, synthetic inputs, and hand-built VCs), so
//! source variables must not be declared under their raw name unconditionally.
//!
//! Every source name and source-derived auxiliary identity is encoded under a
//! versioned prefix. Encoding every name is required: otherwise an ordinary
//! Rust variable named `heap`, `seq_empty`, or `fmap_empty` can alias one of
//! the encoder's internal constants. The source component uses a canonical,
//! lossless byte escape that keeps ASCII identifier characters readable (and
//! therefore keeps AY's name-sensitive search stable), while encoding every
//! other byte as `~hh`. Separate base/derived tags prevent a user name such as
//! `x__upgraded` from colliding with an auxiliary declaration for `x`.

use std::borrow::Cow;

const PREFIX: &str = "__trust_wp_source_var_v1_";
const BASE_TAG: &str = "b_";
const DERIVED_TAG: &str = "d_";

pub(crate) fn base_identity(name: &str) -> Cow<'_, str> {
    Cow::Owned(format!("{PREFIX}{BASE_TAG}{}", encode_component(name)))
}

pub(crate) fn derived_identity(name: &str, role: &str) -> String {
    format!(
        "{PREFIX}{DERIVED_TAG}{}_{}",
        encode_hex(role),
        encode_component(name)
    )
}

/// Recover a source spelling for user-facing counterexample output.
///
/// Invalid or non-canonical strings in the private namespace are left intact;
/// this keeps internal solver identities visible instead of mislabelling them.
pub(crate) fn source_name(identity: &str) -> Cow<'_, str> {
    match decode_identity(identity) {
        Some(DecodedSourceIdentity::Base { source }) => Cow::Owned(source),
        // Without the encoder's active-binding map, a derived identity may be
        // a stale phantom left by a sort upgrade. Keep it role-qualified so it
        // cannot silently shadow the active source value in a counterexample.
        Some(DecodedSourceIdentity::Derived { .. }) | None => Cow::Borrowed(identity),
    }
}

pub(crate) fn is_encoded_source_identity(identity: &str) -> bool {
    decode_identity(identity).is_some()
}

pub(crate) enum DecodedSourceIdentity {
    Base { source: String },
    Derived { source: String, role: String },
}

pub(crate) fn decode_identity(identity: &str) -> Option<DecodedSourceIdentity> {
    let Some(encoded) = identity.strip_prefix(PREFIX) else {
        return None;
    };

    let (role, source) = if let Some(source_hex) = encoded.strip_prefix(BASE_TAG) {
        let Some(source) = decode_component(source_hex).filter(|source| !source.is_empty()) else {
            return None;
        };
        (None, source)
    } else if let Some(derived) = encoded.strip_prefix(DERIVED_TAG) {
        let Some((role_hex, source_hex)) = derived.split_once('_') else {
            return None;
        };
        let Some(role) = decode_hex(role_hex).filter(|role| !role.is_empty()) else {
            return None;
        };
        let Some(source) = decode_component(source_hex).filter(|source| !source.is_empty()) else {
            return None;
        };
        (Some(role), source)
    } else {
        return None;
    };

    let canonical = role.as_ref().map_or_else(
        || base_identity(&source).into_owned(),
        |role| derived_identity(&source, role),
    );
    if canonical != identity {
        return None;
    }
    Some(match role {
        Some(role) => DecodedSourceIdentity::Derived { source, role },
        None => DecodedSourceIdentity::Base { source },
    })
}

fn encode_hex(value: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(value.len() * 2);
    for byte in value.bytes() {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}

fn encode_component(value: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(value.len());
    for byte in value.bytes() {
        if byte.is_ascii_alphanumeric() || byte == b'_' {
            encoded.push(char::from(byte));
        } else {
            encoded.push('~');
            encoded.push(char::from(HEX[usize::from(byte >> 4)]));
            encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
        }
    }
    encoded
}

fn decode_component(value: &str) -> Option<String> {
    let bytes = value.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut index = 0usize;
    while index < bytes.len() {
        let byte = bytes[index];
        if byte.is_ascii_alphanumeric() || byte == b'_' {
            decoded.push(byte);
            index = index.saturating_add(1);
            continue;
        }
        if byte != b'~' || index + 2 >= bytes.len() {
            return None;
        }
        decoded.push((hex_nibble(bytes[index + 1])? << 4) | hex_nibble(bytes[index + 2])?);
        index += 3;
    }
    String::from_utf8(decoded).ok()
}

fn decode_hex(value: &str) -> Option<String> {
    if value.len() % 2 != 0 {
        return None;
    }
    let mut decoded = Vec::with_capacity(value.len() / 2);
    for pair in value.as_bytes().as_chunks::<2>().0 {
        decoded.push((hex_nibble(pair[0])? << 4) | hex_nibble(pair[1])?);
    }
    String::from_utf8(decoded).ok()
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordinary_source_names_are_namespaced_and_round_trip() {
        let identity = base_identity("value");
        assert_ne!(identity, "value");
        assert_eq!(source_name(identity.as_ref()), "value");
        assert_eq!(source_name("value"), "value");
    }

    #[test]
    fn reserved_and_private_names_round_trip_injectively() {
        for name in [
            "default",
            "select",
            "__ay_adversarial",
            "__ay_»»☃",
            "seq_empty",
            "heap",
            "domain",
            "perms",
            "fmap_empty",
            "fset_empty",
        ] {
            let identity = base_identity(name);
            assert_ne!(identity, name);
            assert_eq!(source_name(identity.as_ref()), name);
        }
    }

    #[test]
    fn already_encoded_spelling_is_encoded_again_without_collision() {
        let reserved_identity = base_identity("default").into_owned();
        let adversarial_identity = base_identity(&reserved_identity).into_owned();
        assert_ne!(reserved_identity, adversarial_identity);
        assert_eq!(source_name(&reserved_identity), "default");
        assert_eq!(source_name(&adversarial_identity), reserved_identity);
    }

    #[test]
    fn derived_roles_cannot_collide_with_source_suffix_spellings() {
        let upgrade = derived_identity("x", "upgrade");
        let user_suffix = base_identity("x__upgraded");
        let other_role = derived_identity("x", "seq_synth_0");
        assert_ne!(upgrade, user_suffix);
        assert_ne!(upgrade, other_role);
        assert_eq!(source_name(&upgrade), upgrade);
        assert_eq!(source_name(&other_role), other_role);
        assert!(is_encoded_source_identity(&upgrade));
        assert!(is_encoded_source_identity(&other_role));
    }

    #[test]
    fn source_names_do_not_alias_internal_solver_constants() {
        use ay_dpll::api::{Logic, Solver, Sort};

        let mut solver = Solver::try_new(Logic::All).expect("solver");
        for internal_name in ["seq_empty", "heap"] {
            let internal = solver.declare_const(internal_name, Sort::Int);
            let source_identity = base_identity(internal_name);
            let source = solver.declare_const(source_identity.as_ref(), Sort::Int);
            assert_ne!(internal, source);
        }
    }

    #[test]
    fn unicode_source_identity_is_accepted_by_solver() {
        use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

        let mut solver = Solver::try_new(Logic::All).expect("solver");
        let identity = base_identity("café_☃");
        let source = solver.declare_const(identity.as_ref(), Sort::Int);
        let seven = solver.int_const(7);
        let equality = solver.eq(source, seven);
        solver.assert_term(equality);

        assert_eq!(solver.var_name(source).as_deref(), Some(identity.as_ref()));
        assert_eq!(solver.check_sat(), SolveResult::Sat);
        assert_eq!(source_name(identity.as_ref()), "café_☃");
    }

    #[test]
    fn malformed_private_identities_are_not_misreported_as_source_names() {
        for identity in [
            "__trust_wp_source_var_v1_b_",
            "__trust_wp_source_var_v1_b_not-hex",
            "__trust_wp_source_var_v1_b_~4A",
            "__trust_wp_source_var_v1_d__78",
            "__trust_wp_source_var_v1_d_78_",
            "__trust_wp_source_var_v1_d_00_not-hex",
            "__trust_wp_source_var_v1_unknown",
        ] {
            assert_eq!(source_name(identity), identity);
        }
    }
}
