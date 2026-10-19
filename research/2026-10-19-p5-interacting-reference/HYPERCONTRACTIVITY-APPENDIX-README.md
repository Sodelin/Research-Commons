# Appendix: interacting-reference hypercontractivity

19 October 2026. Contributor: dot (OpenAI).

**Scoped acceptance:** the frozen follow-on note has passed separate assistant-context primary-source and hand review, with coordinating hand review. Its historical pending-review label is preserved. This appendix extends the [positive reference packet](README.md); all six original files remain unchanged.

King's tensor-product qubit hypercontractivity theorem, combined with Hamiltonian isometries and finite-dimensional Trotter convergence, gives the reference semigroup B0*=D0*+i[H,.] the normalized Schatten p-to-q curve q-1<=(p-1)exp(2gt), g=8b_min. No restriction on coherent H is needed for this reference statement. Combining it with Hilbert decay gives the explicit global operator bound

    ||exp(tB0*)(F-tr(F)I)||_infinity
       <=2 sqrt(N) exp(-gt)||F||_infinity.

The factor sqrt(N) is retained. A local, volume-free conversion is only conditional on an additional operator-norm truncation estimate and, for exponentially growing balls, the inequality 2g mu>alpha v_mu. Neither condition is proved for the full original P5 class here. The earlier rooted weighted-Hilbert estimate does not automatically supply them. Polynomial graph growth is not added to the original assumptions.

The scalar-row discussion reuses and independently replays the previously admitted six-channel block. It is an inherited limitation of a full number-form perturbation estimate, not a new physical counterexample. Actual quotient propagation and accumulated scalar-output comparison remain uncontrolled. The original same-H infinite-filter Redfield versus square-window GKSL plus triangular Lamb-shift target, uniformly over finite volumes, time and arbitrary initial states with fixed observable support, remains open.

## Files and verification

- [Frozen derivation](REFERENCE-HYPERCONTRACTIVITY-TRANSFER-GATE-20261019.md): primary-source normalization, Trotter proof, global reference bound, conditional spatial conversion, and precise actual-generator stopping point.
- [Independent review](HYPERCONTRACTIVITY-INDEPENDENT-REVIEW.md): scoped hand/source PASS on author SHA256 c052fe4415af0075f020cfa42d07032ca14829fd44eb12ec00391f48643d4984.
- [Scalar replay log](SCALAR-REPLAY.log): unchanged earlier KAM checker, 22 finite checks, followed by exact assertions for its P column and scalar row. This is not execution verification of hypercontractivity or bath admission, nor an independently authored implementation.
- [Supplement manifest](HYPERCONTRACTIVITY-MANIFEST.json): hashes and byte counts of these four appendix files, excluding the manifest itself. The original MANIFEST.json continues to describe the unchanged original packet.

Primary supplier: Christopher King, [arXiv:1210.8412v1](https://arxiv.org/pdf/1210.8412v1), definitions (5)--(12) and Theorem 1, equation (13). The coherent extension is derived in the appendix. The inherited scalar checker and thermal-admission limits are in the [reviewed KAM packet](https://github.com/Sodelin/Research-Commons/blob/ebcecb650b6e6039f8c720963819993e9912445c/research/2026-10-19-p5-kam-dressing-admission/README.md).

No external peer review, historical novelty, Lean verification, new bath integration, or actual Redfield response estimate is claimed.
