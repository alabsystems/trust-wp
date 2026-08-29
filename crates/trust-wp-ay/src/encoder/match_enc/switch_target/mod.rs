// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match target inference and datatype construction helpers.

#[cfg(test)]
mod tests;

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
use trust_wp_core::formula::{parse_named_struct_ctor, MatchArm, Pattern};

/// Extract the short (unqualified) constructor name from a potentially
/// qualified path. Named-struct constructor metadata like `"Point{x,y}"`
/// normalizes to the base constructor name first.
pub(crate) fn short_constructor_name(name: &str) -> &str {
    let normalized = normalize_constructor_name(name);
    normalized
        .rsplit_once("::")
        .map_or(normalized, |(_, short)| short)
}

/// Strip parser-encoded named-struct field metadata from constructor names.
pub(crate) fn normalize_constructor_name(name: &str) -> &str {
    parse_named_struct_ctor(name).map_or(name, |(type_name, _)| type_name)
}

/// Returns true when the constructor has no qualifier (unqualified `Ok`) or
/// has a stdlib qualifier (`Result::Ok`, `std::result::Result::Ok`).
/// Returns false for user-defined qualifiers like `OwnResult::Ok`. (#2462)
pub(crate) fn is_stdlib_enum_qualifier(full_name: &str, short_name: &str) -> bool {
    if full_name == short_name {
        return true; // Unqualified — assume stdlib
    }
    let qualifier = full_name
        .rsplit_once("::")
        .map_or(full_name, |(prefix, _)| prefix);
    let base_qualifier = qualifier.rsplit_once("::").map_or(qualifier, |(_, b)| b);
    matches!(base_qualifier, "Option" | "Result")
}

/// Classify a stdlib constructor name to its canonical switch target.
///
/// Returns `Some` for unqualified stdlib constructors (`Some`, `Ok`) and for
/// qualified stdlib paths (`Option::Some`, `std::result::Result::Err`).
/// Returns `None` for user-defined constructors such as `OwnResult::Ok`.
pub(crate) fn stdlib_constructor_target(name: &str) -> Option<SwitchTarget> {
    let normalized = normalize_constructor_name(name);
    let short = short_constructor_name(normalized);
    if !is_stdlib_enum_qualifier(normalized, short) {
        return None;
    }

    match short {
        "Some" | "None" => Some(SwitchTarget::OptionInt),
        "Ok" | "Err" => Some(SwitchTarget::ResultIntInt),
        _ => None,
    }
}

/// Returns true for stdlib constructors that carry a payload.
///
/// Includes unqualified forms (`Some`, `Ok`, `Err`) and qualified stdlib
/// forms (`Option::Some`, `Result::Err`), but excludes nullary `None`.
pub(crate) fn is_stdlib_payload_constructor(name: &str) -> bool {
    let normalized = normalize_constructor_name(name);
    let short = short_constructor_name(normalized);
    is_stdlib_enum_qualifier(normalized, short) && matches!(short, "Some" | "Ok" | "Err")
}

pub(crate) fn stdlib_option_datatype_for_payload(payload_sort: Sort) -> DatatypeSort {
    if payload_sort == Sort::Int {
        return SwitchTarget::OptionInt.datatype();
    }

    let name = format!("Option{}", option_payload_sort_tag(&payload_sort));
    DatatypeSort {
        name: name.clone(),
        constructors: vec![
            DatatypeConstructor {
                name: option_constructor_name_for_datatype(&name, "None"),
                fields: vec![],
            },
            DatatypeConstructor {
                name: option_constructor_name_for_datatype(&name, "Some"),
                fields: vec![DatatypeField {
                    name: format!("{}_some_value", name.to_lowercase()),
                    sort: payload_sort,
                }],
            },
        ],
    }
}

pub(crate) fn option_constructor_name_for_datatype(datatype_name: &str, logical: &str) -> String {
    if datatype_name.starts_with("Option")
        && datatype_name != "OptionInt"
        && matches!(logical, "Some" | "None")
    {
        format!("{datatype_name}__{logical}")
    } else {
        logical.to_string()
    }
}

pub(crate) fn datatype_constructor_name(datatype: &DatatypeSort, logical: &str) -> String {
    let logical = short_constructor_name(logical);
    let specialized = option_constructor_name_for_datatype(&datatype.name, logical);
    if datatype
        .constructors
        .iter()
        .any(|ctor| ctor.name == specialized)
    {
        specialized
    } else {
        logical.to_string()
    }
}

pub(crate) fn datatype_constructor_matches(
    datatype: &DatatypeSort,
    actual: &str,
    logical: &str,
) -> bool {
    actual == datatype_constructor_name(datatype, logical)
}

pub(crate) fn logical_constructor_alias_for_datatype(
    datatype_name: &str,
    actual: &str,
) -> Option<&'static str> {
    if datatype_name.starts_with("Option")
        && datatype_name != "OptionInt"
        && actual == option_constructor_name_for_datatype(datatype_name, "Some")
    {
        Some("Some")
    } else if datatype_name.starts_with("Option")
        && datatype_name != "OptionInt"
        && actual == option_constructor_name_for_datatype(datatype_name, "None")
    {
        Some("None")
    } else {
        None
    }
}

fn option_payload_sort_tag(sort: &Sort) -> String {
    fn hex(raw: &str) -> String {
        let mut encoded = String::new();
        for byte in raw.as_bytes() {
            let _ = std::fmt::Write::write_fmt(&mut encoded, format_args!("{byte:02x}"));
        }
        encoded
    }

    match sort {
        Sort::Bool => "Bool".to_string(),
        Sort::Real => "Real".to_string(),
        Sort::Seq(_) => "Seq".to_string(),
        Sort::Uninterpreted(name) if name == "Seq" => "Seq".to_string(),
        Sort::Uninterpreted(name) if name == "FMap" => "FMap".to_string(),
        Sort::Uninterpreted(name) if name.starts_with("Tuple") => name.clone(),
        Sort::Uninterpreted(name) => format!("U{}", hex(name)),
        Sort::Datatype(dt) => format!("D{}", hex(&dt.name)),
        _ => "Other".to_string(),
    }
}

/// Typed switch target — classifies match expressions by the ADT being matched.
///
/// Replaces the former `MatchDatatypeKind` with a general-purpose enum that
/// supports arbitrary user-defined enums in addition to the hardcoded Option
/// and Result types. Constructor information is inferred from arm patterns.
///
/// Inspired by Creusot's `Branches::Constructor(AdtDef, GenericArgsRef, ...)`
/// (reference/creusot/creusot/src/translation/fmir.rs:184-193), adapted for
/// trust-wp's parser-derived `Pattern::Constructor { name, inner }` where MIR
/// type info is unavailable. (#1578)
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SwitchTarget {
    /// `Option<T>` — constructors: `Some(T)`, `None`
    OptionInt,
    /// `Option<T>` with a known non-Int payload sort.
    OptionPayload(Sort),
    /// `Result<T, E>` — constructors: `Ok(T)`, `Err(E)`
    ResultIntInt,
    /// User-defined enum with constructors inferred from match arm patterns.
    ///
    /// `adt_name` is derived from qualified constructor paths (e.g., `MyEnum::A`
    /// → `"MyEnum"`) or synthesized from constructor names when unqualified.
    /// `constructors` stores `(name, field_sorts)` pairs where `field_sorts`
    /// is a `Vec<Sort>` for each payload field. All fields default to
    /// `Sort::Int` because `Pattern` nodes carry no type information and
    /// syntactic heuristics for recursive ADTs are unsound (#2189).
    /// Sort coercion in `apply_logic_fn` handles mismatches conservatively.
    UserDefined {
        adt_name: String,
        constructors: Vec<(String, Vec<Sort>)>,
    },
}

/// Backward-compatible alias for `SwitchTarget`.
///
/// Existing code that imports `MatchDatatypeKind` continues to work.
/// New code should prefer `SwitchTarget` directly.
pub(crate) type MatchDatatypeKind = SwitchTarget;

impl SwitchTarget {
    /// Infer the switch target from match arm constructor patterns.
    ///
    /// Returns `Some(SwitchTarget)` when the arms contain constructor patterns
    /// that can be classified as a known type (Option, Result) or synthesized
    /// into a user-defined ADT.
    pub(crate) fn from_arms(arms: &[MatchArm]) -> Option<Self> {
        let mut saw_constructor = false;
        let mut only_option = true;
        let mut only_result = true;
        let mut constructors: Vec<(String, Vec<Sort>)> = Vec::new();

        for arm in arms {
            if let Some((name, inner)) = Self::constructor_pattern_parts(&arm.pattern) {
                saw_constructor = true;
                let normalized = normalize_constructor_name(name);
                let short = short_constructor_name(normalized);
                let is_stdlib = is_stdlib_enum_qualifier(normalized, short);
                only_option &= is_stdlib && matches!(short, "Some" | "None");
                only_result &= is_stdlib && matches!(short, "Ok" | "Err");

                let arity = Self::pattern_arity(inner);
                if !constructors.iter().any(|(n, _)| n == normalized) {
                    constructors.push((normalized.to_string(), vec![Sort::Int; arity]));
                }
            }
        }

        if !saw_constructor {
            return None;
        }

        if only_option {
            Some(Self::OptionInt)
        } else if only_result {
            Some(Self::ResultIntInt)
        } else {
            // Reject mixed constructors from known stdlib types (e.g., Some + Err).
            // User-defined enums that happen to use Ok/Err are allowed. (#2462)
            let has_known = constructors.iter().any(|(n, _)| {
                let short = short_constructor_name(n);
                is_stdlib_enum_qualifier(n, short)
                    && matches!(short, "Some" | "None" | "Ok" | "Err")
            });
            if has_known {
                return None;
            }

            let adt_name = Self::infer_adt_name(&constructors);
            debug_assert!(
                !constructors.is_empty(),
                "UserDefined requires at least one constructor (#1980)"
            );

            Some(Self::UserDefined {
                adt_name,
                constructors,
            })
        }
    }

    fn constructor_pattern_parts(pattern: &Pattern) -> Option<(&str, Option<&Pattern>)> {
        match pattern {
            Pattern::Constructor { name, inner } => Some((name, inner.as_deref())),
            Pattern::Alias { pattern, .. } => Self::constructor_pattern_parts(pattern),
            _ => None,
        }
    }

    /// Determine the arity (number of payload fields) from a constructor's
    /// inner pattern.
    fn pattern_arity(inner: Option<&Pattern>) -> usize {
        match inner {
            None => 0,
            Some(Pattern::Tuple(elems)) => elems.len(),
            Some(_) => 1,
        }
    }

    /// Derive an ADT name from constructor names.
    ///
    /// If any constructor uses a qualified path (e.g., `MyEnum::A`), extract
    /// the prefix as the ADT name. Otherwise, synthesize a name from the
    /// sorted constructor names joined with underscores.
    fn infer_adt_name(constructors: &[(String, Vec<Sort>)]) -> String {
        for (name, _) in constructors {
            if let Some(prefix) = name.rsplit_once("::").map(|(p, _)| p) {
                return prefix.replace("::", "_");
            }
        }

        let mut names: Vec<&str> = constructors.iter().map(|(n, _)| n.as_str()).collect();
        names.sort_unstable();
        format!("Adt_{}", names.join("_"))
    }

    /// The constructor name for wrapping a single value (e.g., `Some` for
    /// `OptionInt`, `Ok` for `ResultIntInt`).
    ///
    /// For user-defined enums, returns the first constructor with arity >= 1.
    ///
    /// Used when re-wrapping a scalar body result that MIR unwrapped. (#1055)
    pub(crate) fn value_constructor_name(&self) -> &str {
        match self {
            Self::OptionInt | Self::OptionPayload(_) => "Some",
            Self::ResultIntInt => "Ok",
            Self::UserDefined { constructors, .. } => {
                let ctor = constructors
                    .iter()
                    .find(|(_, sorts)| !sorts.is_empty())
                    .or(constructors.first())
                    .expect("UserDefined must have at least one constructor");
                short_constructor_name(&ctor.0)
            }
        }
    }

    /// Build the ay `DatatypeSort` for this switch target.
    pub(crate) fn datatype(&self) -> DatatypeSort {
        match self {
            Self::OptionInt => DatatypeSort {
                name: "OptionInt".to_string(),
                constructors: vec![
                    DatatypeConstructor {
                        name: "None".to_string(),
                        fields: vec![],
                    },
                    DatatypeConstructor {
                        name: "Some".to_string(),
                        fields: vec![DatatypeField {
                            name: "option_some_value".to_string(),
                            sort: Sort::Int,
                        }],
                    },
                ],
            },
            Self::OptionPayload(payload_sort) => {
                stdlib_option_datatype_for_payload(payload_sort.clone())
            }
            Self::ResultIntInt => DatatypeSort {
                name: "ResultIntInt".to_string(),
                constructors: vec![
                    DatatypeConstructor {
                        name: "Ok".to_string(),
                        fields: vec![DatatypeField {
                            name: "result_ok_value".to_string(),
                            sort: Sort::Int,
                        }],
                    },
                    DatatypeConstructor {
                        name: "Err".to_string(),
                        fields: vec![DatatypeField {
                            name: "result_err_error".to_string(),
                            sort: Sort::Int,
                        }],
                    },
                ],
            },
            Self::UserDefined {
                adt_name,
                constructors,
            } => {
                let dt_constructors = constructors
                    .iter()
                    .map(|(name, field_sorts)| {
                        let short_name = short_constructor_name(name);
                        let fields = field_sorts
                            .iter()
                            .enumerate()
                            .map(|(i, sort)| DatatypeField {
                                name: format!(
                                    "{}_{}_{i}",
                                    adt_name.to_lowercase(),
                                    short_name.to_lowercase()
                                ),
                                sort: sort.clone(),
                            })
                            .collect();
                        DatatypeConstructor {
                            name: short_name.to_string(),
                            fields,
                        }
                    })
                    .collect();
                DatatypeSort {
                    name: adt_name.clone(),
                    constructors: dt_constructors,
                }
            }
        }
    }
}
