# Declaration inventory metadata repair

The initial unanchored declaration scan incorrectly extracted `Astra.PhysicalSpliceRegistry.transports` from header prose, “The final theorem transports”. Rust static readback found it before Root publication clearance. The declaration inventory now uses an expression anchored to actual declaration lines, allowing leading attributes, `private` and `noncomputable`; the one nonexistent entry was removed.

Original SOURCE-PINS SHA256 `4f3121b1fbda4785b57063ff0681e3da9eb9e8fd4823aaf7db1d6746b6d6f0b1` and MANIFEST `64cb6e784f2cde3142c55210f2a5fe8b167d44b09a8320dd06b3e1dc717495af` are preserved byte-for-byte under `evidence/initial-metadata/`. README and Lean source bytes did not change. The source remains SHA256 `3bcb80b268b31eae7b4eccd3cd50da6f42494a27d9c6017d91ff52b90bd1d034`, unselected and uncompiled. This is metadata repair only; no compiler/query/test was run.
