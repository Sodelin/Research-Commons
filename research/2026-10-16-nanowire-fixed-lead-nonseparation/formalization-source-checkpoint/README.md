# All-channel formalization: reviewed route and uncompiled source checkpoint

17 October 2026. Author: dot (OpenAI), working with Nolan.

**NOT LEAN VERIFIED. No executed build is included.** This packet preserves a complete independently reviewed alternative hand-proof route and two uncompiled Lean source files. The absence of new `axiom` declarations or `sorry` placeholders does not make the full theorem formally proved. The matrix-to-scalar bindings and several substantial mathematical suppliers remain unfinished.

## What is preserved

- [Pfaffian-free proof route](PFAFFIAN-FREE-PROOF-ROUTE.md): the same full theorem for every finite electron-channel count, with real SVD and finite-cube interpolation for necessity, and explicit one-/two-mode blocks for every-point attainment.
- [Independent mathematical review](INDEPENDENT-PFAFFIAN-FREE-REVIEW-02.md): scoped hand-proof PASS, including zero singular values, both channel parities and all degenerate endpoints. This review does not certify the Lean source.
- [Exact claim specification](ClaimSpec.lean): defines the complete necessary-and-sufficient matrix statement, determinant reality, margin compatibility and closed-error report predicates. Defining those propositions proves none of them.
- [Finite-cube source candidate](Nanowire/CubeAffine.lean): attempted proofs of arbitrary finite-dimensional cube interpolation and the exact separately affine scalar polynomial form. It has not been compiled and may require source corrections before Lean accepts it.
- [Pinned Mathlib source inventory](MATHLIB-SOURCE-INVENTORY.json): verified official source locators and blob identities for Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (v4.33.1). No local toolchain or cache is distributed here.

The original accepted theorem remains [the all-channel packet](../all-channel/README.md). This checkpoint does not alter that proof or upgrade its verification status.

## Why the alternative route matters

The complete matrix theorem can avoid a new Pfaffian library, a finite fermionic density construction and connected Pfaffian fibres. At fixed orthogonal SVD factors, the needed polynomial contains no squared coordinate, so its bounds reduce to orthogonal cube vertices. A Schur-complement identity supplies the unitary vertex inequality. Explicit block formulas give every point of the exact region for odd and even channel counts.

The main formal obligations are still real SVD realization including zero modes, the exact Majorana/PHS conversion, the unitary Schur and singular-block norm arguments, matrix-expression binding to cube interpolation, and direct-sum witness construction. The complete list is in the route note. A successful generic cube-module build alone would not prove the nanowire theorem.

## Provenance and limits

The unchanged review pins the original source audit at SHA256 `3f48810d0050e87d1f3567df21a3ad0d35d30a986e60798e5a5f59ea33600f25`. The public route note retains its mathematical content and records the limited editorial replacement of operational wording. The exact original ClaimSpec and CubeAffine bytes are preserved; the manifest lists their hashes.

The underlying covariance, unitary-scattering and parity ideas have established precedents, described in the [published prior-work addendum](../all-channel/ALL-N-PRIOR-ADDENDUM-20261017-0108.md). Historical novelty remains unresolved. This formalization checkpoint introduces no novelty claim, microscopic realization theorem, experiment, temperature/bias extension, or proof of protected Majorana modes.

No new matrix assumption, channel cutoff or independently justified margin premise has been silently added or removed. Full-region attainment and the distinction between a source margin promise and a direct determinant certificate remain part of the target.
