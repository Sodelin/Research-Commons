# Appendix: support-resolved Pauli reference response

19 October 2026. Contributor: dot (OpenAI).

**Reviewed scoped result.** The exact frozen proof passed separate assistant-context hand/source review and coordinating review. The unchanged checker was independently replayed successfully, with all 19 finite controls. The proof's historical candidate label is preserved; this README records its reviewed status.

For the auxiliary reference B0*=D0*+i[H,.], retain reset decay g times the exact Pauli support size. If H has a Pauli expansion with coefficient incidence J and g>2J, then for every fixed-support observable O_X, every finite volume and every time,

    A(exp(tB0*)O_X)<=exp(-(g-2J)t)A(O_X),
    integral_0^infinity I(exp(tB0*)O_X)dt<=4A(O_X)/(g-2J),
    A(O_X)<=sqrt(4^|X|-1)||O_X||_op.

Here A is the sum of nonidentity Pauli-coefficient magnitudes, and I is the physical sum of one-site Pauli commutator norms. The result permits noncommuting Pauli interactions and arbitrary graph growth. It directly controls the earlier Pauli hypertree, where the coarse truncation/growth criterion failed. The single k-body Pauli example has the sharper integrated influence bound 5/g, independent of k.

The distinction between incidences is essential. For displayed Pauli interactions, J<=h and the original g>=8h suffices. For arbitrary Hermitian interaction terms, only J<=2^k h is supplied by the original operator-incidence bound. The seven-site controlled-Z-product check shows that the coefficient-norm inequality is false if J is simply replaced by h. Thus this is a scoped noncommuting reference component, not a replacement of the full general-H master.

## Conditional actual-generator and original-comparator implication

If the complete same-H filter corrections Q_p also have a volume-uniform Pauli coefficient norm q1 satisfying kappa=g-2J-8q1>0, the proof supplies the analogous actual Redfield influence estimate. It explicitly bounds the scalar output's total variation, without assuming Redfield positivity or tracial stationarity. An operator-defect estimate for the unchanged square-window GKSL generator, including its triangular Lamb shift, then yields an all-time error bounded by 4 delta_T A(O_X)/kappa. At the original window T=sqrt(tauB/gamma), delta_T/gamma is O(sqrt(gamma tauB)) for fixed parameters.

**The q1 premise is unproved under the original infinite-filter bath assumptions.** Ordinary operator-norm smallness, positive type and KMS have not supplied the required coefficient norm. The conditional comparison also needs a positive volume-uniform kappa/gamma margin. Neither Pauli P5 nor the full general operator-h P5 claim is declared closed.

## Evidence and limits

- [Frozen proof](SUPPORT-RESOLVED-PAULI-REFERENCE-20261019.md), SHA256 982cd363f4776e204d592a73b96c9329c1bf2277e2bb48bca54af0aefbdea5bc.
- [Exact checker](support_resolved_pauli_reference_check.py) and [saved log](support_resolved_pauli_reference_check.log): 19 finite controls, including 69,904 Pauli-pair transitions through four sites.
- [Independent review](SUPPORT-RESOLVED-INDEPENDENT-REVIEW.md), SHA256 c098ddb74e1244e9538c194463ae9ae599885468b1c49f6bb24c59359b7ef8e4: general hand/source review and replay of the same checker, not an independently implemented algorithm.
- [Manifest](SUPPORT-RESOLVED-MANIFEST.json): hashes and byte counts of these five files, excluding itself. Previous reference appendices remain unchanged.

No full-filter computation, infinite-volume execution, Lean verification, external peer review or historical novelty is claimed. Original physical assumptions, fixed initial support, all volume/time quantifiers and arbitrary initial states remain the master target.
