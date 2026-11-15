<!-- Copyright 2026 Andrew Yates -->
<!-- Licensed under the Apache License, Version 2.0 -->

# Measuring trust-wp

Use the Trust toolchain and the dependency checkout described in
[README.md](README.md). Run comparable measurements with the same dependency
revisions, compiler, build profile, and machine load, and retain that evidence
beside the results.

## Encoding microbenchmarks

The Criterion targets are declared in the crates' manifests:

```sh
targo --unverified bench --locked -p trust-wp-core --bench smt_encoding
targo --unverified bench --locked -p trust-wp-ay --features internal-bench-api --bench ay_encoding
```

These measure encoding costs. They do not prove a program's contract or
establish Creusot compatibility. The AY crate also has algorithmic scaling
regressions under
[performance_proofs](crates/trust-wp-ay/src/tests/performance_proofs/mod.rs)
and
[performance_hotspot_proofs.rs](crates/trust-wp-ay/src/tests/performance_hotspot_proofs.rs).

## Verification corpus

The [Creusot harness](tests/creusot_compat/README.md) records per-test results,
durations, wire counters, and dependency provenance. Use fresh runs of both
`should_succeed` and `should_fail`; filtered runs diagnose a case but cannot
establish the replacement claim.

`scripts/creusot_replacement_review.sh` drives the review gate.
`scripts/compare_baselines.py::find_true_100_violations` determines compatibility
credit; a faster run or a larger raw pass count alone is not progress toward
that gate. The [adversarial suite](tests/adversarial/README.md) checks rejection
of invalid programs.

Retain complete logs and raw lane JSONs. Compare timings only after checking
that both runs examined the same obligations and received the same proof
credit. A refusal, timeout, or dropped obligation can appear faster while
providing less verification.
