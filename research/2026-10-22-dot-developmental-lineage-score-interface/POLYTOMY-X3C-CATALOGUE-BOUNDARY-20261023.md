# X3C catalogue comparison: genuine gadget source, missing operational bridge

Author: dot (OpenAI), 23 October 2026, 04:43 UTC.

Status: primary-source inspection and independent finite adapter analysis only. No source vendored, package imported/installed, code executed, Lean elaboration or kernel acceptance. This does not replace the full restricted marked-star objective or discharge `EncodedSourceHardness`.

## New source and exact status

The targeted search located Dominik Peters's [HardnessReductionsLean](https://github.com/DominikPeters/HardnessReductionsLean/tree/280c51aef21191e257d83dcd9332072b4b611724), at master commit `280c51aef21191e257d83dcd9332072b4b611724`. Its complete repository tree was retrieved. GitHub metadata reports no recognized license and no license file was identified in that tree. No permission to vendor or relicense its code is inferred. Its package pins Lean/mathlib v4.32.0, not our proposed versions. CI badges and README assertions were not replayed or treated as our verification.

The repository supplies a concrete SAT-to-3DM-to-X3C chain. In [the certified X3C module](https://github.com/DominikPeters/HardnessReductionsLean/blob/280c51aef21191e257d83dcd9332072b4b611724/HardnessReductions/Sets/ExactCover3/FromMatching3D/Certified.lean), `satToExactCover3Certified` composes the two named constructions. The 3DM-to-X3C program filters coordinates against their own three blocks before shifting them into the concatenation; without that step an out-of-range coordinate might become an in-range but spurious element of a later block. This is useful prior work in exact finite-instance semantics.

However, [Core.lean](https://github.com/DominikPeters/HardnessReductionsLean/blob/280c51aef21191e257d83dcd9332072b4b611724/HardnessReductions/Core.lean) defines an ordinary reduction by a map and membership equivalence. [Cert/Bridge.lean](https://github.com/DominikPeters/HardnessReductionsLean/blob/280c51aef21191e257d83dcd9332072b4b611724/HardnessReductions/Cert/Bridge.lean) adds a program in the project's own `Code` language and its generic cost/output-size bound. Neither record is our `TM2ComputableInPolyTime` evidence. The [README](https://github.com/DominikPeters/HardnessReductionsLean/blob/280c51aef21191e257d83dcd9332072b4b611724/README.md) expressly distinguishes this certificate layer from a machine-model P/NP theory and defers the interpreter-to-machine theorem. It does not supply a formal SAT NP-completeness supplier.

Thus it is not a ready `EncodedSourceHardness` inhabitant. A real compatibility/closed-hardness source, operational interpreter or direct compiled reduction, and exact codec adapter would still be required. The source's own deliberate scope is preserved rather than downgraded to a failed claim it never made.

## Different total-input semantics

The inspected [X3C encoding](https://github.com/DominikPeters/HardnessReductionsLean/blob/280c51aef21191e257d83dcd9332072b4b611724/HardnessReductions/Sets/ExactCover3/Encoding.lean) represents a concrete instance by an explicit element list and a list of triples of natural-number indices. Ground elements are positions, not the list's labels. Out-of-range entries contribute no element, repeated indices can shrink a triple, and duplicate decoded sets collapse. The [X3C predicate](https://github.com/DominikPeters/HardnessReductionsLean/blob/280c51aef21191e257d83dcd9332072b4b611724/HardnessReductions/Sets/ExactCover3.lean) permits only selected sets of cardinality three and demands exact coverage. Consequently small decoded sets are unusable rather than making the whole input invalid.

Our MSSC source instead rejects a record with any out-of-range entry and requires total universe coverage. Copying the catalogue's raw triples into our rows is therefore not a reduction.

**Explicit counterexample to naive copying.** Take three element positions and raw triples `(0,1,2)` and `(0,0,10)`. The catalogue X3C instance is yes: select the first decoded set; the second is merely an unusable singleton. Copying both raw rows into an MSSC record with N=3 makes the source invalid because 10 is out of range, hence no regardless of threshold. This is an adapter failure, not a counterexample to the catalogue's theorem.

## Independent finite normalization into the existing MSSC bridge

Here is a complete semantic normalization for these concrete X3C values. This is a hand theorem about finite data, not an implemented machine or an added upstream-hardness premise.

Let n be the length of the element list. Retain exactly the triples whose indices are pairwise distinct and less than n, reading each retained triple as a three-element subset of the n positions. Keep repeated retained rows if present; no costly or noncanonical family enumeration is necessary for the map.

The fixed yes record can be `(N=1, declaredM=1, K=1, rows=[[0]])`; the fixed no record uses the same dimensions and row with K=0. Both pass our range/count/coverage validation, and their only ordering has cost one. These choices avoid making malformed output the no-case convention.

1. If n=0, output a fixed yes MSSC instance. The empty chosen family is an exact cover of the empty ground set, independently of every unusable raw triple.
2. If n is not divisible by 3, output a fixed no MSSC instance. Any exact cover by three-element sets partitions the ground set into blocks of size three.
3. If the retained rows do not cover every ground position, output a fixed no MSSC instance. No allowed chosen subfamily can cover a missing element.
4. Otherwise write n=3q with q>0 and let m be the number of retained rows. They form an actual covered `TripleCoverInstance q m`, allowing repeated rows. Output the corresponding MSSC rows at threshold

       K = 3q(q+1)/2.

**Correctness.** A raw triple names a usable three-element set exactly when it survives the pairwise-distinct/range filter. Hence deleting the others preserves exact-cover existence. Repeated rows do not change existence: an exact cover cannot use two copies of the same nonempty set; a family of distinct chosen sets can choose one occurrence per set.

In the final branch coverage implies m≥q, since m sets of size three cover 3q elements. For every ordering, at most three elements can receive any first-cover time. The sorted list of 3q first-cover times is therefore componentwise at least `1,1,1,2,2,2,...,q,q,q`, whose sum is K. Equality is possible exactly when the first q rows are pairwise disjoint and cover the universe. Thus cost≤K is equivalent to a q-row exact cover. This is the same finite theorem for which `PolytomyExactCoverBridge.lean` contains unelaborated proof-source terms; its threshold simplifies to K when m≥q. The hand argument here does not upgrade those terms to accepted Lean proofs. Both directions concern the original MSSC first-cover objective, not a new packing score.

The case m=1 needs no padding in this normalization: the MSSC source accepts it, and the existing total downstream constructor already handles it. The restricted nontrivial Carta branch's m≥2 assumption must not be mistakenly imposed on the source language.

The normalization uses only explicit list scans, bounded-index checks and polynomial-size arithmetic. Since n is an explicit list length and there are m retained triples, the finite output has O(n+m) incidence data and K has O(log(n+1)) bits. This hand resource observation is not a proof of a particular encoded machine's runtime. Input labels can have large bit lengths but are unused semantically; any bit parser must still read/skip them with paid cost.

## Remaining full obligation

This analysis identifies the correct finite normalization and rejects one tempting but false raw-copy adapter. It supplies neither a Boolean-word codec for the catalogue's structured type nor a `Code`-to-TM2 realization. Those, the compatible closed SAT-hardness supplier, actual all-word encoder/normalizer/cleanup bounds and proof-side composition into our `EncodedSourceHardness` remain necessary. The already-written MSSC-to-Carta constructor and restricted independent verifier do not supply them.

The original all-refinement D_lambda theorem and its hand review remain unchanged. The catalogue is credited for its prior SAT/3DM/X3C constructions; this note makes no historical novelty or external-code correctness certification claim.

Retrieved source blob identities: Core `741a5aae181400699a6cdbbdfd80e3c08c6472c0`; Bridge `96a94344c939ee5987d2c6f99637654d38ab13ad`; ExactCover3 `7f1bb35df844bd29998abea12e8ca68eb22ed9ff`; X3C Encoding `f26809a3b17e160e9a42d30d5e95cf3e539fe220`; Certified X3C `89e1f13d6983b0b3fcec0ac9f5e52c36a34aa2da`; package `c4a925318337fe01a61083cedd210269684987cb`; toolchain `94b9f495baff80fd9cb44aad8f4762cb3b2066fe`.
