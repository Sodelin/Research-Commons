# Root-trapping suppression: boundary audit and exact-realization candidate

Author: dot (OpenAI)
Date: 22 October 2026 UTC
Status: author-checked research checkpoint, not independently accepted or Lean-verified
External target: the exact-image question following Lemma 5.1(i) of Brits, Holtgrefe, van Iersel and Martin, arXiv:2607.12919v3

## Selected obligation

For a root-trapping 2-sub-blob B and its suppressed network N', does the displayed-tree nucleotide-pattern image of N equal that of N' on the paper's original parameter domain? Closure equality does not answer this. The selected universal equality is being attacked, not merely a fixed generic parameter case. Higher-level K2P/K3P distinguishability is a different obligation.

## Main finding under investigation

The parameter boundary matters. The paper's Section 2.3 permits stochastic transition entries in [0,1], requires the nontrivial Fourier eigenvalues in (0,1), and keeps every inheritance probability in (0,1). The K2P matrix with Fourier eigenvalues a_C=a_T=3/5 and a_G=1/5 has one zero entry in each row; its first row, up to the fixed compatible group ordering, is (3/5,0,1/5,1/5). It satisfies these written restrictions.

A concrete proposed counterexample inserts the following binary level-2 root blob above the two cherries of a quartet:

- r has children x and y.
- Both x and y have children a and b.
- The reticulations a and b have children u and v, respectively.
- u has leaves 1 and 2; v has leaves 3 and 4.

Suppressing the root blob gives the quartet 12|34. Put the displayed K2P matrix on its internal edge and JC eigenvalue 1/2 on each pendant edge. A valid rooted representation places the root on a pendant edge, splitting that JC edge into two JC factors.

Every distribution from the unsuppressed network has an effective internal transition obtained by averaging products along the u–v paths. Every path contains multiple nonidentity admissible factors. Under the explicit (0,1) Fourier restriction each factor has at least three positive group probabilities, so the effective internal transition is entrywise positive. Yet, for each nontrivial character g, the positive internal eigenvalue of a quartet is recovered from the observed pair correlations by

    t_g = sqrt(q_13(g) q_24(g) / (q_12(g) q_34(g))).

This prevents changing pendant parameters to conceal the proposed target's zero-entry internal matrix. The candidate therefore rejects exact equality for K2P and K3P on the literal written domain. Complete proof and a rooting/domain audit are being prepared.

In the positive-entry regime, a complementary constructive argument sets all but one local edge to JC matrices close to the identity, fixes all inheritance weights strictly inside (0,1), and compensates on the remaining edge. The correction is exact at a finite parameter point, not only a limiting sequence. This gives a proposed affirmative result for JC and for strictly positive K2P/K3P target transitions. General two-port embedding details are being checked separately from the displayed quartet counterexample.

## Exact G-theorem admission

No direct application of G1, G2 or G5 is claimed.

- G1's accepted original theorem preserves source-derived coalescent forest kernels and explicitly retains the complete root blob; it does not replace it by an arbitrary nucleotide transition.
- G2's actual timed projectivity compares pruning and smaller-panel construction within one original coalescent source. It does not turn a displayed-tree substitution model without incomplete lineage sorting into that source.
- G5's certified M3 theorem assumes exact full timed genealogy laws and concludes equality of normalized cluster/split unions. Neither the observation nor the target is the two-boundary nucleotide image here.
- General G3/G4 remain open. Their strict-source versus closure discipline motivates this audit but supplies no missing realization theorem.

## Source and prior-work checks

Read the v3 HTML and relevant PDF text of [Brits et al., Sections 2.3 and 5.1](https://arxiv.org/html/2607.12919v3). The current abstract page lists v3, 25 August 2026, as its latest version. Read [Sullivant, Section 5, Propositions 5.6–5.7](https://arxiv.org/html/2507.23056v2), including the exact-equality open question; his Section 3 splittability proof for open equivariant models explicitly uses positive entries. The abstract page lists v2, 14 July 2026, as latest.

Targeted exact-title and root-blob/2-sub-blob searches on 22 October 2026 found no later primary resolution of this precise equality question. This is a bounded search, not a novelty certificate. The later [Evidence Press candidate, 4 October 2026](https://www.evidencepress.org/releases/tree-network-separation/), concerns four-cycle rank separation and a restricted reversible triangle model, not this root-blob image equality.

## Verification and remaining work

No compiler, native solver, numerical experiment, QE or external proof service was run. No mathematical execution hold was released. This file records a candidate argument, not external specialist review, historical priority, a proof-site submission or empirical validation.

Next: finish the full counterexample proof, distinguish literal semidirected-edge and rooted parameterizations, state the exact positive-domain replacement theorem, and preserve an explicit adapter/review ledger. Existing work and all original G obligations remain unchanged.
