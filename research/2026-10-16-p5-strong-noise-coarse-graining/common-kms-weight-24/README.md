# An exact obstruction to one shared KMS metric for full and deleted-site Redfield evolution

17 October 2026. Research and checker: dot (OpenAI). Independent mathematical review and separately authored matrix checker: dot (OpenAI), independent reviewing context.

**Status: scoped hand-proof and exact symbolic-check acceptance. The full P5 problem remains open.** The proof retains its submitted candidate header; this README records the subsequent review without altering those reviewed bytes.

For one explicit connected two-qubit model with six independent Pauli bath channels, the full one-sided Redfield filters give two generators: the full generator and the generator with all three channels anchored at site 1 removed, retaining the same Hamiltonian and surviving filters. They have no common trace-one Hermitian stationary operator. It follows that no faithful density matrix can make both evolutions contractive in the same sandwich KMS norm.

This remains a real obstruction when the weight is changed from the bare Gibbs state to the actual stationary state: the proof gives explicit strong-noise parameters for which the full generator has a unique faithful stationary density, yet its deleted-site counterpart cannot be contractive in that density's KMS norm. The result does not decide whether the full generator alone is contractive in its corrected stationary norm.

## Why this test matters

[Bergamaschi, *Fast mixing of all-to-all quantum systems at high temperatures*, arXiv:2606.26090v1](https://arxiv.org/html/2606.26090v1), Definition1.10, Lemma1.11 and Lemma4.7/Eq.75, uses common-weight contraction for its specified nonpositive auxiliary generator and its deleted-site evolutions. The present result rules out a direct transplant of that particular premise to every admitted physical Redfield generator. It does not contradict that paper: its Gibbs-conjugate filters and generator are different. The source definitions and the relevant contraction step were checked; no complete audit of the paper's proofs is claimed.

The physical bath is the [previously reviewed finite-temperature covariance](https://github.com/Sodelin/Research-Commons/blob/43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md). The broad difference between bath KMS and exact generator equilibrium is established prior work, credited in the proof. No historical novelty claim is made.

## Evidence

- [Exact proof](P5-COMMON-KMS-WEIGHT-OBSTRUCTION-24.md): grouped-channel matrices, symmetry argument, contraction-to-stationarity lemma, actual faithful stationary-state existence, and explicit physical parameter checks.
- [Independent review](INDEPENDENT-REVIEW-24.md): full hand argument and independent reconstruction of all eight grouped 4-by-4 matrix images. No mandatory mathematical correction.
- [Author checker](check_metric_block.py) and [fresh result](SYMBOLIC-CHECK-RESULT.json): 90 exact algebraic and parameter-arithmetic checks passed.
- [Independently authored checker](independent_check_24.py) and [its execution output](INDEPENDENT-CHECK-24.txt): both full grouped maps matched on all four basis elements.
- [Hash manifest](MANIFEST.json): exact UTF-8 files and SHA256 values.

The candidate was saved afresh from the authored draft after the first local save failed. The included author checker was also recreated and rerun. No vanished earlier execution output is counted as surviving evidence. Independent review is pinned to the freshly preserved candidate's exact bytes. No software installation was needed.

To replay the finite symbolic checks with Python and SymPy already available:

    python check_metric_block.py
    python independent_check_24.py

These runs check finite symbolic identities, not the analytic bath integral or all functional-analytic steps. Those are covered by the scoped hand review. This packet is not Lean verified.

## Scope that remains open

Different weights for different generators, a changed decomposition, controlled norm growth, and other local-response estimates are not excluded. This two-site metric obstruction proves neither unstable fixed-support dynamics nor failure of the requested all-time, volume-uniform Redfield/coarse-grained comparison. It supplies no new operator-norm response bound. The original P5 target and its physical comparator remain unchanged.
