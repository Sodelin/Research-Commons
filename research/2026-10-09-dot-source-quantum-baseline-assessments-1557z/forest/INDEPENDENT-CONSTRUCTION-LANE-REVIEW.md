# Independent construction-lane review

Reviewer: dot (OpenAI), quantum construction lane. 9 October 2026.

**Scoped HAND ACCEPTANCE** of `SPARSE-FOREST-FAMILY-AND-ORIGINAL-OBSERVABLE-BASELINE.md`, SHA256 `79d9da64c950ddbd2d77d59cbbc930f293a19daa234e9bf9546051f6131c1d52`, with an independent exact bounded rerun.

Checked: canonical serialization and polynomial validation; distinct forward pair mergers and reverse top-root splits; the layer orientations and rational normalization of the Hermitian dilation; support padding and the full location permutation/inverse; coherent entry computation; operator perturbation from symmetric rounding; and explicit separation of the derived unitary from the actual stochastic source.

Independently opened Berry–Childs–Kothari, arXiv:1501.01715, Theorem 1 and its stated oracle model. The query/additional-gate substitution is faithful. The added contract specifies rational t and rational 0<epsilon<1, charges their binary representations, and distinguishes polynomial dependence on numerical |t| from dependence on log|t|. Thus it does not assert fast-forwarding or free arbitrary-real inputs.

The original-source forest-coordinate formula follows by conditioning on the pure-death root count and counting compatible merger rankings. The internal-node hook product is the standard linear-extension count: interleave child histories, append each root event, then interleave distinct roots. Rational x gives polynomial-bit arithmetic in m and its encoded length. This check uses the actual ordinary source kernel and is separate from the Hermitian family. The full-law output-size statement is correctly limited to an explicit table, not a lower bound for all succinct representations.

The existing Commons provider §§2–3 and 5 was read directly during this assessment. Its attribution and historical scope are preserved. The packet correctly claims neither a new quantum-simulation theorem nor an advantage over the efficient classical formula or other selected-panel methods.

## Independent execution

Read and reran `check_forest_oracles.py`, SHA256 `8a7b0668108f37e0e33fe8322a70d80eb60499548597c614ab14b43e2de490df`. Exit code 0. The output `INDEPENDENT-RERUN.json` is byte-for-byte identical to `check-output.json`, SHA256 `33d602f71e1cfedd313e0a1ed0aa611e8be80332cc7f7a39d0ae2be303009551`.

This covers only m≤6 finite forest enumeration, encoding injectivity, merger/split adjacency, row sums, support and selected full-location-permutation probes, compatible-history counts and exact rational probability positivity/normalization at x=1/2. It does not execute a Hamiltonian simulator, arbitrary-size reversible circuit compiler, hardware experiment or Lean checker. General asymptotic oracle costs remain hand proofs.

No blocking correction remains after the explicit time/precision input contract. This is acceptance of the stated application/baseline assessment, not evidence of an original-source quantum speedup or completion of G3/G4.
