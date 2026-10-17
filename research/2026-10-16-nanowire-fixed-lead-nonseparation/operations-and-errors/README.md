# Scattering operations and error contracts

17 October 2026. dot (OpenAI), working with Nolan.

**Accepted scope: independently reviewed hand proofs for finite matrices.** This packet records which operations preserve the hypotheses of the previously reviewed conductance bounds and how matrix errors propagate. It is classical matrix/network groundwork. It is not a claim of historical novelty, a Lean-verified package, an implemented toolkit or a universal device theory.

## What is established

- Canonical zero-energy particle-hole-symmetric matrices become real matrices after the stated unitary Majorana-coordinate change. Square matrices form a real, rather than complex, unital *-algebra.
- The contractive subset is closed under compatible products, adjoints, consistently reordered direct sums, real convex combinations and paired-channel compression. It is not closed under arbitrary addition or scalar multiplication. A square contraction has a contractive inverse exactly when it is unitary.
- Reflection and transmission blocks from one device must satisfy their common parent scattering constraints. Separate block admissibility does not establish a shared physical source.
- Regular passive feedback preserves contraction and particle-hole symmetry when its internal inverse exists. The packet gives an explicit resolvent guard and perturbation bound. A passive example shows why no uniform conditioning constant follows from passivity alone.
- For incoming electron-channel count n and operator-norm error epsilon, the quadratic charge readout changes by at most 2n epsilon. For square size 2N, determinant error is at most 2N epsilon. A contraction with determinant magnitude at least m>0 retains its determinant sign under any particle-hole-symmetric perturbation of norm strictly less than m.

These statements concern admitted matrices. They do not infer a matrix uncertainty budget from a fit, manufacturing tolerance or experiment.

## Exact dimensions and editorial clarifications

For the feedback formula, use a in C^(2n), b in C^(2m), and u,v in C^(2p). Then A is 2m by 2n, B is 2m by 2p, C is 2p by 2n, and D,K are square 2p by 2p. The common scattering matrix S has size 2(m+p) by 2(n+p), in terminal-grouped coordinates with the matching particle-hole involutions. The effective F has size 2m by 2n. With u=Kv,

    F=A+B(I−KD)^−1KC.

Invertibility of I−KD is a separate premise. The inverse itself need not be contractive. The singular cases are outside this regular formula; they are not declared physically impossible. Established generalized star-product constructions can cover additional cases.

For paired-channel embeddings, read the draft's norm-one phrase as **norm at most one**, which also covers a zero-dimensional selected space. These clarifications were supplied by the independent review; they do not change the accepted formulas or the preserved draft bytes.

The fixed-point real-algebra statements apply at zero energy. Away from zero, physical particle-hole symmetry generally relates opposite energies. Direct sums require the stated channel-order permutation. Ordinary matrix multiplication is not generally physical device cascading because feedback may be present.

## Evidence and attribution

- [Preserved mathematical draft](SCATTERING-OPERATIONS-AND-ERROR-CONTRACTS-DRAFT-09.md): full derivations, source links and physical limits. Its original “draft for review” header is preserved as development history; this README and the review give the subsequent accepted status.
- [Independent review](INDEPENDENT-OPERATIONS-REVIEW-09.md): scoped hand-proof PASS on the exact source hash, including dimensions, noncommuting feedback order, all constants, the passive conditioning example and strict sign guard.
- [Hash manifest](MANIFEST.json): exact SHA256 and byte length of each substantive file.

The primary sources are Beenakker's Majorana-scattering review, Kostrykin–Schrader's generalized star product, Cervera–van der Schaft–Baños's passive network interconnections, and Rosdahl and colleagues' transport conventions. Their established contributions are explicitly credited in the draft and review. No claim of new Redheffer theory or new physical mechanism is made; the prior search is bounded, not exhaustive.

No proof-assistant compilation, numerical experiment or device operation establishes this packet. Its acceptance is mathematical hand review. Microscopic device realization, finite-temperature admission, a common parameter tuple across settings and calibrated error remain separate obligations. Ordinary transistor applications remain deferred until those obligations are supplied.

This packet is additive to the [all-channel theorem](../all-channel/README.md), [indicator/transmission register](../indicator-register/README.md) and [conditional thermal adapter](../finite-temperature/README.md). It does not modify their assumptions or settle the original biological or many-body research targets.
