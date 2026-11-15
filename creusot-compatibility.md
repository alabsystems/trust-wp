<!-- Copyright 2026 Andrew Yates -->
<!-- Licensed under the Apache License, Version 2.0 -->

# Creusot compatibility

trust-wp's goal is complete Creusot replacement. Completion is established by
the corpus and soundness gates in docs/GOAL.md, not by the
presence of a macro, parser rule, standard-library specification, or encoder.
The current checkout has not established that full replacement claim.

The `creusot-contracts` and `creusot-std` crates provide the compatibility
namespaces. The native `trust-wp` facade re-exports contracts and helpers
through `use trust_wp::*;`. [contract-syntax.md](contract-syntax.md) documents
the supported syntax, including contracts, quantifiers, logic functions,
ghost code, snapshots, mutable-reference state, and external specifications.
Parsing a construct and proving every program that uses it are separate
requirements.

## Establishing compatibility

The pinned oracle is recorded in
[tests/creusot_compat/REFERENCE.pin](tests/creusot_compat/REFERENCE.pin).
[tests/creusot_compat/README.md](tests/creusot_compat/README.md) explains how to
obtain that reference and run the lanes. docs/HARNESS.md
describes how results are graded, and docs/DEVELOPING.md
describes artifact and dependency checks. Committed baselines are historical
inputs, not a live compatibility score.

Run `scripts/creusot_replacement_review.sh` for the review gate. A replacement
claim requires fresh success and rejection lanes plus the full adversarial
suite, with AY as the only backend. A translated or compiled program alone is
not proof of its contract; the gate's documented zero-goal and NO_REPLAY
policies determine when a row has no provable obligation to discharge.

## Interpreting verification

Machine-integer overflow, division safety, and indexing safety are proof
obligations. For example, `#[requires(x > 0)]` does not make `x + 1` safe for
an `i32`: the caller may supply `i32::MAX`. Examples intended to verify must
state bounds strong enough to prove their arithmetic and memory operations.

Standard-library contracts used as assumptions are part of the trust base.
The `#[trusted]` specifications in `trust-wp-std` are not proved by trust-wp;
see docs/GOAL.md. A specification being present or wired into
the driver does not establish all behavior of that type.

Incomplete extraction, unsupported encodings, solver limits, and missing
checked certificates must remain explicit refusals or unknown results.
docs/soundness.md records known soundness boundaries;
docs/DIRECTION.md describes the work toward eliminating
the text-based contract frontend and its duplicated semantic inference.
