# trust-wp-ay Proof Artifacts

This directory contains formal proofs for critical logic encodings in trust-wp-ay.

## Contents

| File | Description | Related Code |
|------|-------------|--------------|
| `base_memory_model_invariants.md` | Separation logic invariants for BaseMemoryModel | `../src/memory_model/base/mod.rs`, `../src/memory_model/base/tests.rs` |

## Purpose

Proof artifacts document the mathematical correctness of:

1. **Encoding soundness** - SMT encodings correctly represent separation logic semantics
2. **Invariant preservation** - Operations maintain required properties
3. **Memory safety** - Encoding detects use-after-free, double-free, dangling pointers
4. **Permission conservation** - Fractional permissions follow algebraic rules

## Format

Each proof document includes:

- **Summary**: What is being proven and why
- **Definitions**: Formal notation and encoding definitions
- **Theorems**: Mathematical statements with rigorous proofs
- **Test Correspondence**: Mapping between theorems and test cases
- **Verification Commands**: How to run the related tests
- **Assumptions**: Limitations and prerequisites

## Verification

Run all memory model proofs:

```bash
cargo +nightly-2025-11-13 test -p trust-wp-ay --lib -- memory_model
```

Individual theorem verification commands are listed in each proof document.

## Contributing

When adding new proofs:

1. Follow the existing format (see `base_memory_model_invariants.md`)
2. Include theorem statements, proofs, and test correspondence
3. Document all assumptions and limitations
4. Ensure all referenced tests pass
