// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, NAMED_FIELD_LOGIC_FN_PREFIX},
    parse_named_struct_ctor, Pattern, PureExpr, NAMED_CTOR_REST_MARKER,
};

use super::{super::struct_field_map::CtorFieldOrder, placement::FieldPlacement, ParsedContract};

/// The two tables a named-field contract expression is resolved against.
///
/// `flat` answers "what index does a field NAME have" across every struct in
/// one signature. It is what a field ACCESS (`x.inner`) needs, because the
/// contract text carries no type there, and it is ALL it may be used for.
///
/// `ctors` answers "which constructor is spelled `E::C`, and what does it
/// declare, in order". It is the only table a named-field PATTERN or LITERAL
/// may be placed from, because those name a constructor and may name an enum
/// VARIANT — and `flat` is built by `build_struct_field_map`, which returns
/// early on `!adt_def.is_struct()` and so knows nothing of any variant. Ask
/// `flat` where a variant's fields sit and it answers from whatever unrelated
/// STRUCT in the same signature happens to share the field names: not a worse
/// oracle for exotic cases, the wrong oracle for every case. That is why
/// `place_named_fields` below takes the constructor table alone and cannot
/// reach this struct at all (D-31).
#[derive(Clone, Copy)]
pub(in crate::callbacks) struct FieldOrderTables<'a> {
    pub(in crate::callbacks) flat: &'a HashMap<String, usize>,
    pub(in crate::callbacks) ctors: &'a CtorFieldOrder,
}

impl<'a> FieldOrderTables<'a> {
    pub(in crate::callbacks) fn new(
        flat: &'a HashMap<String, usize>,
        ctors: &'a CtorFieldOrder,
    ) -> Self {
        Self { flat, ctors }
    }
}

/// Why a named-field pattern or constructor could not be placed in
/// declaration order. Carried out to the caller, which refuses the function:
/// the alternative — binding the fields in the order they were written —
/// types one field as another (D-31).
pub(in crate::callbacks) type FieldOrderRefusal = String;

fn refusal(type_name: &str, field_names: &[&str], why: &str) -> FieldOrderRefusal {
    format!(
        "cannot place the fields of `{type_name} {{ {} }}` in declaration order ({why})",
        field_names.join(", ")
    )
}

/// Resolve the declaration index of every field a named-field pattern or
/// literal writes, or say why it cannot be resolved.
///
/// `field_names` is in SOURCE order and may end with the `..` rest marker.
///
/// The guarantee is structural rather than asserted (D-31). This function has
/// exactly ONE `Ok` exit, and the only way to build the [`FieldPlacement`] it
/// returns is `FieldPlacement::from_declaration`, whose argument is a
/// `DeclaredFields` — a field list rustc copied out of a `VariantDef`.
/// `FieldPlacement`'s fields are private to the `placement` module, so no
/// code here can assemble a second. Every other exit is an `Err`: a
/// source-order fallback is a guess, and a guess that places one field where
/// another is declared types a binding as the wrong field.
///
/// There is no `Ok` for `C { .. }`: the parser encodes a pattern naming no
/// field as a BARE constructor name, so it carries no metadata and never
/// arrives here, and the empty case is a refusal — see `placement.rs`.
///
/// Read `placement.rs` to check that claim — it is the whole of the trusted
/// part. Read this function for the refusals, each of which closes a way to
/// GUESS:
///
/// * A candidate table that silently DROPPED constructors past a cap would let
///   a decoy answer for the real one, so a capped entry is refused before it
///   is read — the first thing this function does with an entry
///   (`tests/adversarial/cases/s82v2_ctor_candidate_cap.rs`).
/// * A fallback to the flat name->index map whenever the spelling is not in
///   the table would make every spelling the table cannot CONSTRUCT
///   (`self::E::C`, `super::E::C`, …) a misplacement, so no flat map is in
///   scope here, and the table is not built by constructing spellings alone:
///   `struct_field_map::record_spec_tc_resolved_ctors` asks rustc which
///   constructor each clause's spelling actually resolved to
///   (`tests/adversarial/cases/s82v3_selfmod_path_reorder.rs`).
fn place_named_fields(
    type_name: &str,
    field_names: &[&str],
    ctors: &CtorFieldOrder,
) -> Result<FieldPlacement, FieldOrderRefusal> {
    let has_rest = field_names.last() == Some(&NAMED_CTOR_REST_MARKER);
    let named: &[&str] = if has_rest {
        &field_names[..field_names.len() - 1]
    } else {
        field_names
    };
    // NOT an early `Ok`. `C { .. }` — the only pattern that writes no field
    // name — is encoded by the parser as a BARE constructor name with no field
    // list, so it never reaches this function. An expression that DOES reach
    // here with an empty name list came from somewhere else, and there is
    // nothing about it to trust: `FieldPlacement::from_declaration` refuses it
    // below, where every other refusal lives.

    let Some(entry) = ctors.get(type_name) else {
        // No constructor of that spelling was resolved in a type-checked
        // clause, and no declaration in scope answers to it. A pattern that
        // cannot be tied to a declaration is refused: the function loses a
        // proof it might have had, which is the price of not inventing one.
        let why = if has_rest {
            "a `..` rest pattern needs the constructor's declared field list, \
             and no declaration for that name was found"
        } else {
            "no declaration for that name was found"
        };
        return Err(refusal(type_name, field_names, why));
    };
    if entry.is_capped() {
        // The table stopped recording constructors for this spelling, so what
        // it kept is not known to contain the one this pattern means. Every
        // survivor is then a possible decoy, and agreement among decoys says
        // nothing about where THIS constructor declares its fields.
        return Err(refusal(
            type_name,
            field_names,
            "more constructors answer to that name than the candidate table keeps, \
             so which one this pattern means cannot be established",
        ));
    }

    // Several constructors may answer to this spelling. What the pattern
    // needs is where its fields SIT, so candidates that agree on the
    // placement resolve; only a real DISAGREEMENT refuses.
    let mut agreed: Option<FieldPlacement> = None;
    let mut last_mismatch: Option<String> = None;
    for declared in entry.lists() {
        match FieldPlacement::from_declaration(declared, named, has_rest) {
            Ok(placement) => match &agreed {
                Some(prev) if *prev != placement => {
                    return Err(refusal(
                        type_name,
                        field_names,
                        "more than one constructor answers to that name and they place these \
                         fields differently",
                    ));
                }
                Some(_) => {}
                None => agreed = Some(placement),
            },
            Err(why) => {
                last_mismatch.get_or_insert(why);
            }
        }
    }
    agreed.ok_or_else(|| {
        let why = match last_mismatch {
            Some(mismatch) => format!("`{type_name}` {mismatch}"),
            None => format!("no constructor spelled `{type_name}` declares exactly these fields"),
        };
        refusal(type_name, field_names, &why)
    })
}

/// Rewrite named struct field access expressions to positional tuple-get calls.
///
/// The contract parser lowers `x.inner` to `LogicFnCall("__trust_wp_field_inner", [x])`,
/// while MIR extraction lowers struct field projections to
/// `LogicFnCall("__trust_wp_tuple_get_0", [x])`. These are two unrelated uninterpreted
/// functions in SMT, so the postcondition can never be proved.
///
/// This pass rewrites `__trust_wp_field_<name>` -> `__trust_wp_tuple_get_<index>` using
/// type information from `tcx` to map field names to positional indices, and
/// places named-field constructors and patterns at their DECLARED indices.
///
/// Returns the first refusal if any named-field constructor or pattern in the
/// expression cannot be placed; the caller must then refuse the function
/// rather than verify it.
pub(in crate::callbacks) fn rewrite_named_field_access_expr(
    expr: &PureExpr,
    tables: FieldOrderTables<'_>,
) -> Result<PureExpr, FieldOrderRefusal> {
    let mut refused: Option<FieldOrderRefusal> = None;
    let rewritten = expr.rewrite_bottom_up(|node| match node {
        PureExpr::LogicFnCall { name, args } => {
            if let Some(field_name) = name.strip_prefix(NAMED_FIELD_LOGIC_FN_PREFIX) {
                if let Some(&index) = tables.flat.get(field_name) {
                    return PureExpr::LogicFnCall {
                        name: tuple_field_logic_fn_name(index),
                        args,
                    };
                }
            }

            if let Some((type_name, field_names)) = parse_named_struct_ctor(&name) {
                match reorder_named_fields_to_positional(type_name, &field_names, &args, tables) {
                    Ok(reordered) => {
                        return PureExpr::LogicFnCall {
                            name: type_name.to_string(),
                            args: reordered,
                        }
                    }
                    Err(why) => {
                        refused.get_or_insert(why);
                        // The node is left as written; the caller refuses.
                        return PureExpr::LogicFnCall { name, args };
                    }
                }
            }

            PureExpr::LogicFnCall { name, args }
        }
        PureExpr::Match { scrutinee, arms } => PureExpr::Match {
            scrutinee,
            arms: arms
                .into_iter()
                .map(|arm| trust_wp_core::formula::MatchArm {
                    pattern: match rewrite_named_struct_pattern(&arm.pattern, tables) {
                        Ok(pattern) => pattern,
                        Err(why) => {
                            refused.get_or_insert(why);
                            arm.pattern.clone()
                        }
                    },
                    body: arm.body,
                })
                .collect(),
        },
        other => other,
    });
    match refused {
        Some(why) => Err(why),
        None => Ok(rewritten),
    }
}

/// Reorder named struct constructor arguments to canonical (definition-order)
/// positions.
///
/// Given field names `["y", "x"]` and args `[val_y, val_x]` for a constructor
/// declaring `{ x, y }`, produces `[val_x, val_y]`.
///
/// Refuses when the declaration order cannot be established. A struct literal
/// carries a value for every field, so — unlike a pattern — there is nothing
/// to pad: a rest marker or an arity mismatch is also a refusal.
pub(super) fn reorder_named_fields_to_positional(
    type_name: &str,
    field_names: &[&str],
    args: &[PureExpr],
    tables: FieldOrderTables<'_>,
) -> Result<Vec<PureExpr>, FieldOrderRefusal> {
    if field_names.len() != args.len() {
        return Err(refusal(
            type_name,
            field_names,
            "the constructor was written with a different number of values than field names",
        ));
    }
    let placement = place_named_fields(type_name, field_names, tables.ctors)?;
    if placement.arity() != args.len() {
        return Err(refusal(
            type_name,
            field_names,
            "a struct literal must carry a value for every declared field",
        ));
    }
    let mut out: Vec<Option<PureExpr>> = vec![None; placement.arity()];
    for (src, &idx) in placement.indices().iter().enumerate() {
        out[idx] = Some(args[src].clone());
    }
    out.into_iter()
        .map(|slot| {
            slot.ok_or_else(|| {
                refusal(
                    type_name,
                    field_names,
                    "a declared field was left without a value",
                )
            })
        })
        .collect()
}

/// Rewrite named struct constructor patterns to canonical field order.
///
/// For `Constructor { name: "TypeName{y,x}", inner: Tuple([pat_y, pat_x]) }`,
/// rewrites to `Constructor { name: "TypeName", inner: Tuple([pat_x, pat_y]) }`.
///
/// A `..` rest pattern is expanded to the constructor's full arity with
/// `Wildcard` in every position it did not name.
///
/// Refuses when the declaration order cannot be established.
pub(super) fn rewrite_named_struct_pattern(
    pattern: &Pattern,
    tables: FieldOrderTables<'_>,
) -> Result<Pattern, FieldOrderRefusal> {
    match pattern {
        Pattern::Wildcard | Pattern::Binding(_) | Pattern::Literal(_) => Ok(pattern.clone()),
        Pattern::Alias { alias, pattern } => Ok(Pattern::Alias {
            alias: alias.clone(),
            pattern: Box::new(rewrite_named_struct_pattern(pattern, tables)?),
        }),
        Pattern::Tuple(elements) => Ok(Pattern::Tuple(
            elements
                .iter()
                .map(|p| rewrite_named_struct_pattern(p, tables))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Pattern::Constructor { name, inner } => {
            let rewritten_inner = inner
                .as_ref()
                .map(|p| rewrite_named_struct_pattern(p, tables))
                .transpose()?;
            if let Some((type_name, field_names)) = parse_named_struct_ctor(name) {
                let reordered_inner =
                    reorder_named_pattern_fields(type_name, &field_names, rewritten_inner, tables)?;
                Ok(Pattern::Constructor {
                    name: type_name.to_string(),
                    inner: reordered_inner.map(Box::new),
                })
            } else {
                Ok(Pattern::Constructor {
                    name: name.clone(),
                    inner: rewritten_inner.map(Box::new),
                })
            }
        }
        // Pattern is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns, clippy::match_wildcard_for_single_variants)]
        _ => Ok(pattern.clone()),
    }
}

/// Place pattern fields at their declared positions, padding a `..` rest with
/// `Wildcard`.
fn reorder_named_pattern_fields(
    type_name: &str,
    field_names: &[&str],
    inner: Option<Pattern>,
    tables: FieldOrderTables<'_>,
) -> Result<Option<Pattern>, FieldOrderRefusal> {
    let Some(inner) = inner else {
        return Ok(None);
    };

    let placement = place_named_fields(type_name, field_names, tables.ctors)?;

    // The parser stores a one-field pattern bare and a multi-field one as a
    // Tuple.
    let elements: Vec<Pattern> = match (&inner, placement.indices().len()) {
        (Pattern::Tuple(elements), n) if elements.len() == n => elements.clone(),
        (_, 1) => vec![inner.clone()],
        _ => {
            return Err(refusal(
                type_name,
                field_names,
                "the pattern binds a different number of sub-patterns than field names",
            ))
        }
    };

    let mut slots: Vec<Pattern> = vec![Pattern::Wildcard; placement.arity()];
    for (src, &idx) in placement.indices().iter().enumerate() {
        slots[idx] = elements[src].clone();
    }
    if slots.len() == 1 {
        Ok(Some(
            slots.into_iter().next().expect("arity == 1 checked above"),
        ))
    } else {
        Ok(Some(Pattern::Tuple(slots)))
    }
}

/// Apply named field access rewriting to all expressions in a parsed contract.
///
/// Returns the first refusal if any named-field pattern or constructor in the
/// contract cannot be placed in declaration order.
pub(super) fn rewrite_named_field_access_in_contract(
    parsed: &mut ParsedContract,
    tables: FieldOrderTables<'_>,
) -> Result<(), FieldOrderRefusal> {
    // NOTE: this deliberately does NOT skip on an empty `flat` map. The
    // function whose signature contains only an ENUM produces an empty flat
    // map, and skipping would leave its reordered variant patterns to be read
    // in source order by the encoder (D-31).
    let mut refused: Option<FieldOrderRefusal> = None;
    parsed.rewrite_all_exprs(|expr| match rewrite_named_field_access_expr(expr, tables) {
        Ok(rewritten) => rewritten,
        Err(why) => {
            refused.get_or_insert(why);
            expr.clone()
        }
    });
    match refused {
        Some(why) => Err(why),
        None => Ok(()),
    }
}
