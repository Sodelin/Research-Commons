# Attribution and later bounded controls for the aggregate-label calculation

19 October 2026. Author: dot (OpenAI), working with Nolan.

This addendum accompanies the frozen hand candidate P1-AGGREGATE-LABEL-NOISE-STABILITY-CANDIDATE-20261019.md, SHA256 1e67d8e6f69b1200edd204ba511ccd6b593fdfc4b7567aac49af56a34805fcad. It changes neither its proof nor its scope. Separate review is pending at the time of this addendum.

## Closest directly checked prior mechanism

Bogdanov and Mossel, *On extracting common random bits from correlated sources*, arXiv:1007.2315v2, dated 22 September 2011:
https://arxiv.org/html/1007.2315v2

Section 2, Theorem 1 and Claims 2–3 use hypercontractivity and small output probabilities to limit agreement between functions of correlated bit strings. Their theorem treats binary-symmetric correlated inputs and high-min-entropy outputs. This is the established mechanism underlying the candidate's exact-label limitation. The candidate instead derives the posterior channel of repeated weak Bernoulli observations, permits fractional source-to-label assignments, and transfers the calculation to a fine Gibbs net. The prior theorem is not imported unchanged as a statement about Gibbs learning or aggregate fidelities. Only the listed theorem, claims and their proofs were read for this comparison. No exhaustive prior-work audit or historical-novelty conclusion is claimed.

The candidate's displayed hypercontractive inequality is also a diagonal specialization of Montanaro and Osborne, *Quantum boolean functions*, Theorem 46, as cited there. No new hypercontractivity theorem is asserted.

## Later executed controls

The frozen candidate's no-execution statement describes its initial proof-only status. After it was frozen, the following author-written bounded checker was executed with Python's exact rational arithmetic:

- check_aggregate_posterior_channel_20261019.py, SHA256 11940659da8bec42ba7645e16aa97e9104835921aef356c4d9aa1710312188d8.
- check_aggregate_posterior_channel_20261019.log, SHA256 d646852d581657d6d040cdf4e869c4d341f31b84cef304e69ad99fe943bc55ee.

All 24 one-coordinate posterior/noise/Hellinger controls and all 12 two-coordinate tensor-channel and fractional-function identities passed. The controls use three rational bias values and bounded copy counts. They do not execute or prove the arbitrary-N theorem, the hypercontractive supplier, the arbitrary-net transfer, or a P1 rate. The general conclusion remains a hand argument requiring separate review. No Lean verification is claimed.
