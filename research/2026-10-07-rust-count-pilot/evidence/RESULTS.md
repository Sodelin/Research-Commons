# Executed pilot results, 2026-10-07

The count-only Rust library and release CLI build succeeded on
x86_64-unknown-linux-gnu with the official Rust 1.90.0 minimal toolchain.

- 10 Rust unit tests passed.
- 1,693 deterministic corpus cases passed exact output-field and full JSON-byte
  comparison against the unchanged Python reference.
- Direct factorial/inequality/normalization checks passed for the entire corpus.
- 16 invalid-input or documented Python-coercion checks passed on the reference.
- 22 invalid CLI cases plus 5 additional transport/budget/non-UTF-8 boundary
  checks passed on the Rust executable.
- 8 mutated certificate variants were rejected by the independent-formula checker.

These are finite executed tests, not universal equivalence or formal proof.
The reference and Rust producer share their intended mathematical contract;
the factorial checker is an additional algorithmic check, not a Lean theorem.

## Full-CLI timing observations

Five bounded workloads, seven repetitions per implementation, measured on the
same cloud machine. The run alternated engine order. Medians:

| Input | Python CLI | Rust release CLI |
|---|---:|---:|
| a=0, epsilon=1/2 | 26.13 ms | 1.35 ms |
| a=1, epsilon=1e-12 | 24.99 ms | 1.17 ms |
| a=10, epsilon=1e-15 | 24.73 ms | 1.66 ms |
| a=25, epsilon=1e-8, weights | 25.88 ms | 3.43 ms |
| a=100, epsilon=1/2, max_steps=2 | 24.10 ms | 1.15 ms |

These include process startup, parsing, exact arithmetic and serialization.
They are not a kernel-speedup measurement, controlled cold-cache experiment,
or solver-wide performance claim. Raw wall/CPU/RSS/output-size samples and
ranges are in `benchmark-report.json`. All observed peak RSS values were
14,204 KiB; this measurement is not informative enough to establish either
memory equivalence or a memory advantage. Python startup is a substantial part
of these small workloads. All timed output bytes matched exactly.

The release binary digest is
`5f8afd1557623ebf889b2d2e6fdbcf84a8c5a75e55993e32600fb54ecad700d1`.
`check-report.json` records its compiled source hashes, compiler and lockfile
identity. `BUILD-PROVENANCE.json` records distinct installation/build evidence.
The Python source identity is not reused as a Rust implementation identity.

## Remaining gates

Independent review is tracked separately. Cross-platform builds, package
redistribution/license review, production service limits, later solver stages,
and full Lean verification are not established by this pilot. Nothing in this
packet modifies the existing scientific provider or Lean-verification owner.
