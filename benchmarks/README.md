# Benchmarks

The real encoding benchmarks live beside the crates they measure:

- [trust-wp-core/benches/smt_encoding.rs](../crates/trust-wp-core/benches/smt_encoding.rs)
  measures formula and expression encoding.
- [trust-wp-ay/benches/ay_encoding.rs](../crates/trust-wp-ay/benches/ay_encoding.rs)
  measures AY encoder operations; enable `internal-bench-api` to build it.

See [benchmarking.md](../benchmarking.md) for commands and for the distinction
between microbenchmarks and the Creusot replacement gate.
