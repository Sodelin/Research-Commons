# E8 deterministic class-mass certificate: exact Lean checkpoint

Author: dot (OpenAI), formalization assistance for Nolan
Context UTC: 2026-10-02 04:40

## Proved

For an arbitrary class type, finite discovered set D and selected set T of
cardinality k, simultaneous discovered-class lower/upper bounds plus a bound
on EVERY undiscovered class certify the strict top-k SET when every selected
lower bound exceeds all discovered outsider upper bounds and the unseen cap.
No countability or mass normalization premise is needed for this ordering lemma.
A threshold implementation checks the min-selected versus max-outsider bound;
an arbitrary single kth lower value without its minimum property is insufficient.
Set certification does not assert the internal order of the selected classes.

Additional proved deterministic consequences:
- Two CDF boundary errors at most b give class-jump error at most 2b
- Empirical mass zero and absolute error at most r give unseen class mass at most r
- A simultaneous event at every time makes each successful certificate sound,
  including at a data-selected time
- A VERIFIED coordinate discrepancy eta widens each lower bound by -eta,
  each upper bound by +eta, and the unseen cap by +eta
- A true in/out gap greater than 4r forces empirical interval separation
- Positive selected mass greater than 3r beats the unseen cap; combined with
  discovery and 4r gaps this forces certificate success

With a supplied DKW class radius r=2b, the conservative gap becomes greater
than 8b. These are conditional deterministic implications, not newly proved
concentration inequalities or stochastic sampler statements.

## Verification

Lean4.33.1 (commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6),
mathlib0df444a360eaa60ab8c11dca51a86af692955474. Both files compiled from
immutable source copies. All 13 substantive endpoint audits contain only
propext, Classical.choice and Quot.sound. No sorry/admit/desired-theorem axiom.
The dependency olean hash was stable and is recorded in the second receipt.
Exact source, log and receipt bytes are included beside this file.

- E8DeterministicTopKCertificate: source `32dc60e3db94f387fae00212662ae9b85544aa759857231ba50d1bb3181a9e7a`, 1.345636s PASS
- E8CertificateStability: source `9a30ed5deee52a9f57f764878889988e11630037353698268485d80999fe739a`, 1.576033s PASS

## Explicit boundaries

The all-time event probability, DKW inequality, fixed countable ordering,
post-discovery Beta/Dirichlet intervals, discovery/termination, genuine TV
bound, grammar/shape-class language correctness, exact energy arithmetic and
versioned PRISM IID/RNG law are NOT proved by these two files. The actual
sampler audit has a reproduced failure; no end-to-end RNA certificate is claimed.

Close prior includes Massart's DKW inequality, existing multinomial confidence
sequences, and RapidShapes exact class masses/residual top-k stopping. This
checkpoint implements deterministic logic in Lean and makes no novelty claim.
The source-specific research questions and sampler audit belong to the E8
research lane; this proof does not repair or certify that executable.

## Reproduction

With matching Lean/mathlib objects available, compile E8DeterministicTopKCertificate
first, then E8CertificateStability, using lean -j1 -M4096 and 120s bounds.
The failed initial missing-Finset-card-import attempt is retained locally; it
is not a successful endpoint and is not used by either published proof.
