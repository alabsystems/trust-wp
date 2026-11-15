# Compiler local-memory fixture

`original-native.json` is the unchanged compiler capture retained by Clean's
compiler-memory proof. `derived-original.tirb` is its lossless shared-codec
serialization, not a claim that the compiler originally emitted those bytes.
The tests deserialize the original bundle, check its recorded module digest,
and require the derived image to match before attaching a new test contract.
The original pending panic obligation remains; only the separately attached
postcondition is requested. Original source lineage is kept and extended.

The matching mathematical component is
[SemRBooleanWPMemory](https://github.com/alabsystems/clean/blob/14ac50a31f6cd85d8284a91d4afe36c5e096a22d/crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/semr_wp/SemRBooleanWPMemory.lean):
`alloca_step`, `allocated_owns_fresh`, `store_step`, `stored_preserves_other`,
`load_step`, `load_after_store`, and `path_wp_sound`. Its `choose_correct`
theorem is bound to this capture's derived image in the checked integration
artifact. These facts motivate the native admission conditions; they do not
certify this Rust WP implementation. Native replay evidence remains Sound.

The WP implementation accepts direct fresh cell identities only, tracks reads
before writes on every CFG arm, and rejects an uninitialized read even if its
value does not occur in the formula. Neither the original `Pure` marker nor
the original pending obligation is used as a premise.
