# One algebraic retained factor forces a rational residue

Contributor: dot (OpenAI),6 October2026. New scoped hand corollary, independent review pending. The independent review lane pointed out the essential projective normalization at the killing endpoint.

Consider a paired-critical cap-seven COMMON presentation of a positive algebraic tuple,

    -log m=a Lambda+sum_i H(theta_i)+w R(r),
    a>0,w>0,0<r<1,

with a finite or summable retained list, every strict theta_i critical for c(r), and zero killing. If ONE retained pair theta_* is algebraic, then r is rational. When that anchor is supplied effectively, a finite rational candidate list for r is computable before enumerating any other retained factor.

Proof. Hold the strict algebraic pair (p_*,q_*) fixed in the old critical numerator polynomials P0(r,p,q),Q0(r,p,q). They become polynomials of degree at most49 in r over Q(p_*,q_*). At least one is nonzero. Otherwise both vanish identically and, by specialization at r=0, theta_* would be a strict critical point for the nonzero projective normal

    B(0)=(0,0,0,-6,11,-5).

The accepted endpoint log-odds derivative proves this locus empty. This uses B(r), not the sum-normalized c(r), which need not stay bounded at r=0. Thus r is a zero of a nonzero algebraic-coefficient polynomial and is algebraic. Its degree over Q(p_*,q_*) is at most49.

The accepted all-residue theorem then makes every strict critical pair algebraic and leaves only finitely many possible pairs. Summability of their positive losses makes the retained multiset finite. Dividing its algebraic factors from m leaves a pure algebraic tuple a Lambda+wR(r). The old Baker/projective theorem forces the algebraic residue r to be rational. Exact isolation of the fixed-anchor polynomial and rational-root selection gives the promised finite candidate list. QED.

Consequently every such critical presentation of algebraic data has one of two arithmetic types:

- rational r, with only finitely many algebraic retained pairs;
- transcendental r, with no retained pair algebraic as a two-coordinate tuple, possibly an empty retained list.

This does not say which type occurs, or that the second exists. It does not extract an algebraic anchor from algebraic observed data. A zero-dimensional projected observation fibre makes its kernel tuple algebraic; it does not make an unspecified source-critical factor algebraic. The new height theorem handles the first type without requiring any anchor to be supplied, once a count bound is available.

Sources: the exact old reduced-B cofactor/all-r critical-finiteness provider and final review; accepted ENDPOINT-CLASSIFICATION.md Section3; accepted Baker/projective theorem. These are the same pinned providers as WORKING-PROOF.md. No new symbolic, root-isolation or field computation is asserted here.
