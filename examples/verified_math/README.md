# Verified Math Example

A simple library demonstrating trust-wp contract verification.

## Functions Verified

| Function | Precondition | Postcondition |
|----------|--------------|---------------|
| `safe_increment(x)` | `x < i32::MAX` | `result == x + 1` |
| `double(x)` | `-1000 <= x <= 1000` | `result == x * 2` |
| `abs(x)` | `x > i32::MIN` | `result >= 0` |
| `is_positive(x)` | none | `result == (x > 0)` |
| `zero()` | none | `result == 0` |
| `negate(b)` | none | `result == !b` |

## Running Verification

From the trust-wp root directory:

```bash
# Verify all functions (--crate-type=lib for library files)
./scripts/run-trust-wp-rustc.sh examples/verified_math/src/lib.rs --crate-type=lib -- --force
```

### Expected Output (Success)

```
trust-wp: Found 6 functions with contracts:
  safe_increment
    requires: x < 2147483647
    ensures: result == x + 1
  double
    requires: x >= -1000 && x <= 1000
    ensures: result == x * 2
  abs
    requires: x > -2147483648
    ensures: result >= 0
  is_positive
    ensures: result == (x > 0)
  zero
    ensures: result == 0
  negate
    ensures: result == !b

trust-wp: safe_increment verified ✓
trust-wp: double verified ✓
trust-wp: abs verified ✓
trust-wp: is_positive verified ✓
trust-wp: zero verified ✓
trust-wp: negate verified ✓

trust-wp: 6 verified, 0 failed, 0 errors
```

### Verbose Mode

```bash
./scripts/run-trust-wp-rustc.sh examples/verified_math/src/lib.rs --crate-type=lib -- --force --verbose
```

This shows details about the verification condition generation and SMT solving.

## Running Tests

The source file includes unit tests:

```bash
cargo test -p verified_math
```

## Contract Syntax

Contracts use Creusot-compatible proc-macro attributes:

```rust
use trust-wp::{ensures, requires};

#[requires(precondition expression)]
#[ensures(postcondition expression)]
fn my_function(...) { ... }
```

Available constructs:
- `result` - refers to the function return value
- Arithmetic: `+`, `-`, `*`, `/`, `%`
- Comparison: `==`, `!=`, `<`, `<=`, `>`, `>=`
- Logical: `&&`, `||`, `!`

See `contract-syntax.md` at the repo root for the full grammar.
