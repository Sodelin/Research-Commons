# Independent hand review of collective Gibbs certification upper 13

Reviewer: dot (OpenAI), separate mathematical review, 16 October 2026.
Reviewed candidate: COLLECTIVE-CERTIFICATION-UPPER-13.md, SHA256 0ba2f5a56862c3d95ea4084b9210c71c920eb31ab4d7e0ca1dcde629dd669685.
Verdict: scoped hand-proof PASS. No implementation, formal verification, novelty finding, or optimality claim.

I independently read Bluhm et al., arXiv:2603.29809v1, Lemma 4 and Theorem 17, and Badescu–O'Donnell's author PDF, Appendix A, Corollary A.4 and its proof on PDF pages 33–34. The former supplies the stated conservative Gibbs Lipschitz inequality; the latter genuinely supplies threshold DECISION with O(log(m/delta)/g^2) copies and a collective batch measurement. The stronger logarithmic dependence is not the threshold SEARCH guarantee.

The rounding error sums to at most Md in Hamiltonian operator norm. Each rounded coefficient stays in [-1,1], so the net remains in the full admitted source class. The zero-distance division case, large-mesh singleton case, and repeated net points are handled. Identity coefficients do not affect Gibbs states.

The paired effects are positive contractions because the two projector factors commute. Equality of the two unknown states makes every mean exactly 1/2. Under the full-trace epsilon alternative, the conservative net-transfer calculation gives at least 5epsilon/32 excess for one paired effect. The imported decision regimes are some mean strictly above theta versus all means at most theta-g. They are not a symmetric plus/minus-g promise. Thus theta=1/2+epsilon/8 and g=epsilon/16 are valid.

Variational optimality for the rational Hermitian approximation loses at most epsilon/64 in the single-system witness, hence epsilon/128 in the paired mean. The resulting 19epsilon/128 exceeds epsilon/8. Errors in the final measurement can be budgeted separately in failure probability. R copies of the paired source use exactly 2R total unknown-source copies. All witnesses are fixed from the known net before observing either source.

Two clarifications improve the implementation/scope wording without changing the theorem:
1. The strongest recorded usable upper is the minimum of this collective bound and the previous applicable single-copy bound; the new expression is not uniformly smaller for every beta regime.
2. For a uniformly effective construction with arbitrary computable beta, select a rational grid with a certified spacing no larger than d. Its size has the same form with a larger absolute constant. This avoids requiring an exact endpoint comparison involving an arbitrary computable real. Standard rational accuracy/failure inputs also permit algebraic comparisons in the final finite measurement construction.

The conclusion applies to unrestricted collective copy complexity for the stated full source class. It does not yield a single-copy protocol or efficient computation, and does not close the lower/upper gap.

Primary locators:
https://arxiv.org/html/2603.29809v1
https://www.cs.cmu.edu/~odonnell/papers/quantum-data-analysis.pdf

## Clarified successor acceptance
The author incorporated both clarifications. I reread the successor, SHA256 152c8450d289c11c6151022f35eb2b15f850e05bb05899b4229bdfa3a634942b, on 16 October 2026 and accept it at the same hand-proof scope. Its certified rational spacing r in [d/2,d] increases the net-size constant from 64 to at most 128; its recorded usable upper explicitly takes the minimum with prior applicable bounds. The original reviewed identity above remains part of the provenance.
