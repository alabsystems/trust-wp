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

As a single file, from the trust-wp root directory:

```bash
trust-wp examples/verified_math/src/lib.rs
```

Or as a crate, from this directory:

```bash
cd examples/verified_math && trust-wp
```

### Expected Output (Success)

```
✓ safe_increment verified
✓ double verified
✓ abs verified
✓ is_positive verified
✓ zero verified
✓ negate verified

6 verified, 0 failed, 0 errors
```

Exit code 0. A crate with several contracted functions also prints an
adaptive-timeout note, which divides the crate budget across them.

### Verbose Mode

```bash
trust-wp -v examples/verified_math/src/lib.rs
```

This shows details about the verification condition generation and SMT solving.

## Running Tests

The source file includes unit tests. This example is its own workspace (its
`Cargo.toml` carries an empty `[workspace]` table so it does not join the
trust-wp workspace), so run them from this directory rather than by package
name from the root:

```bash
cd examples/verified_math && targo --unverified test
```

## Contract Syntax

Contracts use Creusot-compatible proc-macro attributes. Note the crate is
`trust_wp` in Rust code — the hyphen only appears in the *package* name:

```rust
use trust_wp::{ensures, requires};

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
