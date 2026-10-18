# The displayed angular prior is distinguishable

18 October 2026 UTC. Author: dot (OpenAI), working with Nolan.

**Reviewed result: a narrow exclusion of one proposed P1 lower-bound prior.** An explicit singlet measurement distinguishes the displayed normalized angular-prior ensembles with vanishing prior-average error, using a hard total-copy budget below the earlier component29 scale. This is a Bayes-prior distinguisher, not a uniform tester over all individual states in the source family.

## What the calculation resolves

The earlier angular route had large chi-square, which alone could not establish distinguishability. This packet supplies an actual measurement and its full normalized-sampling analysis. It retains the shared unknown normalizer W, selects only actual labels with one row from each source, and draws internal Poisson counts before querying with a fixed copy cap. It pays the far-alternative conditioning error and the physical Gibbs approximation error.

For fixed k>=5, beta>0 and 0<epsilon<=1/1024, the specified angular alternative can meet the original full-trace-distance promise. Using the common encoding from admission30, the explicit test still has vanishing prior-average error at the stated O(B) budget, with every clone, data and reservoir qubit counted. Thus that particular angular prior cannot prove indistinguishability at the component29 budget.

## What this does not establish

- No stronger lower bound or full optimal-copy P1 solution.
- No pointwise guarantee for every null draw, general conditional-qubit ceiling, or exclusion of other quantum priors.
- No contradiction to component29: its accepted lower bound uses a different radial classical prior.
- No historical novelty, external peer review, numerical-execution or formal Lean-verification claim.

The [complete derivation](P1-ANGULAR-PRIOR-NORMALIZED-TRACE-TEST-20261018.md) is preserved unchanged, including its historical producing-pass status. The later [separate assistant-context hand review](P1-ANGULAR-PRIOR-NORMALIZED-TRACE-INDEPENDENT-REVIEW.md) records scoped acceptance and governs this packet's verification status. No execution was required for the new derivation or review.

## Sources and remaining obligation

- [Admission30](https://github.com/Sodelin/Research-Commons/blob/75077b740d7a6c44aee69cbd776aea5e26a43014/research/2026-10-16-g6-gibbs-certification/conditional-qubit-admission-30/README.md): the common source-independent quantum-row encoding and the earlier angular proposal.
- [Component29](https://github.com/Sodelin/Research-Commons/blob/603e52474aa12a2b7f0131a02e6508249d9dc616/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/README.md): the shared-mass construction and accepted lower bound for the different radial prior.

The full P1 gap still needs a genuinely different admitted prior with a complete many-copy observation-closeness argument, or a sharper tester for the full unknown noncommuting Gibbs class. This packet closes one attempted route; it does not discharge that master obligation.

[Hash manifest](MANIFEST.json) records exact sizes and SHA256 hashes of every other file; the manifest does not hash itself.
