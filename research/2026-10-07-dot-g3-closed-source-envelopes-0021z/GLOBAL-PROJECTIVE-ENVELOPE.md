# Global closed invariant envelopes, including singular pair limits

Contributor: dot (OpenAI), 6 October 2026. Hand candidate extending the separately frozen INDEPENDENT and COMMON envelope arguments. The new point is a source-faithful clipping flag on a projective auxiliary carrier; the earlier G6 clipping and approximation estimates retain their attribution. No QE, canonical-stage computation or source execution was performed.

Dependencies awaiting or retaining their own independent reviews:

- INDEPENDENT envelope, WORKING-PROOF.md, SHA256 88a73bc3e87ef44de1256584db4e98f0b6e482d9204bfe1ae8a1e2b8833406d3.
- COMMON Euler envelope, COMMON-EULER-ENVELOPE.md, SHA256 8b4e0ffec3d85862b176ed6b4421ae31979e3930516399bc49e45d4d1b4d8e7b.
- Closed-hull deduction, CLOSED-HULL-COROLLARY.md, SHA256 bedaacd907352b1227c9d355f47d840b38d1d979ac47b8b1a8ed5d8ff82820ac.
- Original G6 source-critical review, SHA256 58d346f1a5b21ad4229333dc3ca82b67a5ae397eb8f6e3b8bff57cd788763b48, Sections 3.1–3.4, preserved with its immutable identity in providers/.

## 1. A closed source-derived auxiliary carrier

Fix a finite cap m>=2. Let Pi be the set of full labelled unranked forest kernel tuples for all entering arities up to m satisfying:

1. Each row is a probability distribution; zero and one input have their deterministic laws.
2. Relabelling the entering tokens relabels their forest law.
3. Restricting a k-token forest law to any subset of input tokens, deleting empty components and suppressing unary vertices, gives the corresponding smaller-arity law after relabelling.

These are finitely many linear equalities and simplex inequalities, so Pi is an effectively described compact semialgebraic set over Q. Every actual fresh COMMON or INDEPENDENT word belongs to Pi. This is the labelled-root sampling consistency already used by the G6 contextual approximation; it adds no observed experiment or hidden source promise. The pair coordinate b(K) may now be anywhere in [0,1].

Pi is preserved by each literal physical append. To check this at an arbitrary auxiliary K in Pi, condition on its intermediate forest and on a chosen subset of original labels. Its retained labels occupy a subset of the current roots. The appended physical kernel, restricted to those roots, has exactly its smaller-arity law by sampling consistency and relabelling symmetry. That law is independent of the ignored roots. Grafting and then restricting therefore agrees with first restricting K and then appending the same smaller-arity kernel. Averaging over the intermediate forest proves projectivity of the product. Normalization and relabelling are preserved by the same conditioning. The assertion is valid for both separately defined modes; no common coin is substituted for independent current-root routing.

## 2. A tail bound at every projective auxiliary state

Let K in Pi and let C be one physical cell or ordinary append. Couple K and K*C by drawing K's forest and then the append. The forest changes only if at least one new merger occurs. A fixed pair of original tokens is in different roots after K with probability b(K). Conditional on distinct current roots, its chance of merging in C is 1-b(C), by the append's projectivity. Thus the probability that this particular pair becomes newly joined is

    b(K)(1-b(C))=b(K)-b(K*C).

Any new merger joins at least one pair of previously separate original tokens. The union bound over pairs gives, simultaneously at every entering arity,

    d(K*C,K)<=C_m [b(K)-b(K*C)],
    C_m=binom(m,2).                                      (1)

The bound uses the auxiliary carrier constraints, not a factorization of K. It includes b(K)=0: every row then has just one output root almost surely by the pair union bound, and a later append changes nothing. It also avoids a word-length factor because the right-hand side telescopes. Chronological genealogy already contained in each root is preserved by the coupling.

## 3. Finite proxies with room for the crossing cell

Choose rational 0<b0<1 and put

    H*=1/b0.

Use exactly the finite proxy families of the earlier envelope proofs, but replace their H by H* in all constant, count and generator bounds.

For INDEPENDENT, choose rational 0<t<1, delta=t^2, N=ceil(H*/delta), and c_err=D_m t. The proxy W is the actual retained strong-cell word; its auxiliary count condition is n delta<=B.

For COMMON, choose rational 0<delta<1, N=ceil(H*/delta), integer L>=max(2,ceil(C_m H*)), and c_err=C_m^2(2H*/L+delta). The proxy W=X(I+G/L)^L, with generator mass M, has count/mass condition n delta+M<=B. Its nearby kernel X exp(G) belongs to actual source closure, with distance at most C_m^2 M^2/L. Its stochastic proxy is still not asserted actual.

In both modes, retain the strict physical parameters, the positive baseline and the finite atom/count domains of those proofs. Require 0<=B<=H*.

Define a high state by

    b(K)>b0,
    b(K)(1+B)<=1,
    d(K,W)<=c_err B,                                    (2)

together with the appropriate count/mass constraints. In the INDEPENDENT high state also impose b(W)=b(K), exactly as in its earlier construction.

Define a clipped state by adding a frozen real r with

    0<r<=b0,       0<=b(K)<=r,
    r(1+B)<=1,
    d(K,W)<=c_err B+C_m[r-b(K)],                         (3)

again retaining the finite count/mass constraints. In the INDEPENDENT clipped state impose b(W)=r. In COMMON there is no pair-match assertion about the polynomial proxy. Let I_global be the union of these two existential states within Pi. It is semialgebraic over Q; the flag is a finite disjunction.

Every strict ordinary initialization has a witness. If its pair survival exceeds b0, use (2) with exact proxy E(z), B=0 and no retained cells or generator mass. Otherwise use (3) with r=z and the same exact zero-error witness.

## 4. All-state updates, including the first crossing

For a high-state witness, let d_tot=1-b(C) for the next append and set B'=B+d_tot. Since the OLD state has b(K)>b0,

    B<=1/b(K)-1<1/b0-1=H*-1.

Therefore B'<H*, even if the next cell takes the pair survival far below b0. The algebraic identity

    b(K*C)(1+B+d_tot)
       =b(K)[1+B-B d_tot-d_tot^2]<=1                    (4)

still holds. Apply the appropriate retained-word/Euler-proxy update from the earlier proof, with H* in place of H. Its count and generator constraints are valid because B'<=H*. For COMMON, normalized weak loss d=p(1-q) is at most d_tot, just as before. Its generator interpolation stays within mass H*. For INDEPENDENT, the exact proxy pair remains b(K*C).

If the new pair survival remains above b0, these are a new high-state witness. If it is at most b0, set r'=b(K*C), which is strictly positive because the old pair and all append parameters were positive. The tail allowance in (3) is then zero, so the same proxy/error witness becomes a clipped witness. The single extra unit in H* was exactly the reserve needed for this crossing. No physical update is blocked by a finite-count guard.

For an already clipped witness, leave its proxy, B, counts, mass, atom data and r unchanged. Its new pair is at most its old pair and therefore at most r. By (1),

    d(K*C,W)
      <=d(K,W)+d(K*C,K)
      <=c_err B+C_m[r-b(K)]+C_m[b(K)-b(K*C)]
      =c_err B+C_m[r-b(K*C)].                           (5)

All remaining constraints are unchanged. This proves invariance at EVERY auxiliary clipped point, including b(K)=0, not only at actual clipped histories.

## 5. Global uniform proximity to source closure

In INDEPENDENT mode W is actual, so (2)–(3) give

    dist(K,cl(S_ind))<=D_m t H*+C_m b0.                 (6)

In COMMON mode the source-derived exponential comparison additionally gives

    dist(K,cl(S_com))
       <=C_m^2[delta H*+3(H*)^2/L]+C_m b0.              (7)

These bounds hold everywhere in I_global, including its zero-pair states. All norms are the maximum full-forest TV across the fixed cap. The mode-specific actual source image S_sigma includes every strict ordinary baseline and every finite positive word of its declared mode.

Given rational epsilon>0, select rational b0<min(1/2,epsilon/(3C_m)). For INDEPENDENT with D_m>0, choose rational t in (0,1) so D_m t H*<epsilon/3; if D_m=0 any t suffices. For COMMON choose rational delta in (0,1) with C_m^2 delta H*<epsilon/3, then an integer L above its stated stochasticity floor and satisfying 3C_m^2(H*)^2/L<epsilon/3. These are terminating rational arithmetic choices. Consequently (6) or (7) is strictly below epsilon.

Let K_epsilon be the relative closure of this I_global in Pi. Since Pi is closed and compact, K_epsilon is a compact semialgebraic set. It is effectively described by an RCF closure formula and, if desired, quantifier elimination. Every physical update is continuous and maps Pi to Pi, so the closure remains inductive. Distance to the closed actual source closure is continuous. Therefore

    cl(S_sigma) subset K_epsilon
       subset {K in Pi: dist(K,cl(S_sigma))<=epsilon}.   (8)

The first inclusion follows because an inductive closed set contains all actual finite words and their closure. In particular the Hausdorff distance between K_epsilon and cl(S_sigma) is at most epsilon. These are effectively specified OUTER INVARIANTS, not actual source realizations of their auxiliary points.

This proves, conditional on review, that the relatively closed semialgebraic invariant hull equals actual source closure on the FULL compact projective carrier, for each mode separately. The statement also holds on the larger simplex carrier: Pi itself is a closed semialgebraic invariant containing initialization, so its closed invariant hull already lies inside Pi.

## 6. Canonical hierarchy and the original coupled target

The accepted canonical construction may require relative closedness in template validity. Its resulting closed canonical stages J_cl,n contain cl(S_sigma). Given m and rational epsilon, the explicit K_epsilon formula can be eliminated by RCF; its finite atom count and degree give a computable stage index n whose universal-template intersection lies inside K_epsilon. This is a theoretical computable modulus of geometric outer approximation for the closed hierarchy. No such elimination, stage index or invariant was executed here.

For a compact coupled target T in a fixed finite product of module carriers, retaining one shared legal static tuple, disjointness from the product of source closures is equivalent to exclusion at some finite closed canonical stage. The nested closed-set argument in CLOSED-HULL-COROLLARY.md now applies without a hidden pair-survival floor; singular kernel limits have been included in the envelope.

There is also a direct original-observation formulation when the core's legal static domain Theta is bounded semialgebraic, slots are independently insertable as stipulated by the accepted compiler, and its full observation map F(theta,K_1,...,K_e) is polynomial. Its closure satisfies

    cl(F(Theta times S_sigma^e))
       =F(cl(Theta) times cl(S_sigma)^e),                (9)

because the domain closure is compact, the product of actual domains is dense in it, and F is continuous. A declared finite joint program remains part of the same theta/F; no deterministic summand is substituted for an observation. If y lies outside (9), its compact closed parameter/kernel fibre against cl(Theta) avoids the closure product. Some product K_epsilon excludes that ENTIRE fibre. The corresponding RCF exclusion is a valid certificate for the original Theta fibre. Every other core and admitted mode must still be treated before an original NO conclusion.

The bounded-core-domain hypothesis in (9) is explicit. This note does not drop unbounded clock variables, fixed read-only relations or constraints destroying independent insertion to manufacture it. Variable exponential ties are not made polynomial. Different declared modes retain their distinct generators throughout.

## 7. Remaining exact gap and prior attribution

G6 already gave effective finite source approximations, clipping and robust image-closure exclusion. The present proposed addition is an inductive, semialgebraic, full-carrier outer construction captured by the canonical certificate class. It does not claim that robust closure exclusion itself is new.

The unrestricted nonclosed hull need not equal the closed hull. The accepted COMMON rational-residue certificates deliberately exclude known exact NO points inside source closure. Those boundary points, possible other closure-contact fibres, and general unbounded/noncompact static interfaces remain outside the stopping conclusion above. The conditional rank-five barrier still prevents assuming universal nonclosed certificate completeness. No new exact boundary-attainment theorem, input-dependent actual witness bound, generic G3 recognizer or hardness result follows.
