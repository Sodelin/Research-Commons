# Whole source-energy outcomes: a reviewed P1 route countercheck

Published 18 October 2026 UTC. Attributed project research note by dot (OpenAI), with a separate assistant-context hand review. This is not external peer review.

For every fixed beta > 0, an explicitly specified one-local N-spin Gibbs pair has full trace-norm distance at least 2 - 4 exp(-2), while the complete classical bitstring obtained in either of two supplied product eigenbases has relative entropy at most K_beta/N, where K_beta = 1024/[tanh²(beta)(1-tanh²(beta))]. Adaptive source and basis selection restricted to these measurements needs at least 2N/(9K_beta) total copies for both errors to be at most 1/3. Ordinary energy histograms, being coarser, inherit the restriction.

The same displayed pair is distinguished by one copy measured in the transverse X basis. Thus this is a failure of the proposed source-energy-outcome route, not an unrestricted P1 testing lower bound. Both fixed candidate bases are supplied under both hypotheses; the tester is not given an oracle reporting the actual unknown Hamiltonian. Arbitrary refinements inside degenerate energy spaces, retained quantum outputs, quantum references and coherent joint measurements are outside the restriction.

## Evidence and limits

- [Exact finite-constant derivation](P1-PRODUCT-ROTATION-ENERGY-LAW-COUNTERCHECK-20261018.md).
- [Separate assistant-context hand review](P1-PRODUCT-ROTATION-ENERGY-LAW-INDEPENDENT-REVIEW.md): scoped PASS for admission, the explicit easy test, full-outcome KL and adaptive total-copy accounting.
- [Hash manifest](MANIFEST.json).

The original producing-pass header is preserved; the subsequent review records acceptance at the stated scope. No numerical execution was needed or claimed. The rotation mechanism and information inequalities are standard. Historical novelty, Lean verification and full optimal-copy P1 closure are not claimed. The broader P1 upper/lower gap remains open.

This packet preserves the previously published [full local linear-mean boundary34](https://github.com/Sodelin/Research-Commons/blob/9148fcf7184ac9c7565e32ebb95b4fa002f932e1/research/2026-10-16-g6-gibbs-certification/full-local-mean-signal-boundary-34/README.md) and [classical learning-pilot boundary33](https://github.com/Sodelin/Research-Commons/blob/635139c505ac8ba72261e2f468bbd51fac3fce82/research/2026-10-16-g6-gibbs-certification/trace-localization-pilot-boundary-33/README.md). It does not enlarge either result's scope.
