# Prior attribution correction: the weak equal-arm rule is OLD

24 October 2026 UTC. Existing G3 owner.
Stable key: G3-INTERIOR-COIN-PRIOR-ATTRIBUTION-01.

This corrects attribution, not the mathematical conclusion of the paired
diagonal application. Original G3 and CP-Pair remain unresolved.

## Exact retained predecessor and later acceptance

At Commons8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6, under

    research/2026-10-08-dot-g4-interior-coin-source-jets-1213z/

the following COMPLETE bodies were actually read and byte/hash identified:

* INTERIOR-COIN-SOURCE-JETS-ADDENDUM-CANDIDATE.md,7641B,
  SHA25681de27ab78b4bf8b8889d2b8a7005194264b831396a50ac0d71076899ac660b6,
  blob38d3595be706125a9a706d2dd188efa926e3a58c.
* INDEPENDENT-HAND-REVIEW.md,6182B,
  SHA256f659f795f963fc9c923f6427e06bb52d905dd8be211582f72387212f03c82f83,
  blob060ec321968d89487dcf067d753c874d41d1d9cc.
* README.md,2752B,
  SHA25675aa45b46860ca491cd90b255014d25f1acda5d763ee2a357fa3fe1ca9aafb12,
  blob16dd2bf7f33148fab637a80516b69e277affcfe0.
* PROVENANCE.md,1579B,
  SHA256a36760629e66d05c33c03671087c245cf21b61af86d136297ea9677b2aee7584.

[Old accepted source](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-08-dot-g4-interior-coin-source-jets-1213z/INTERIOR-COIN-SOURCE-JETS-ADDENDUM-CANDIDATE.md),
[scoped HAND ACCEPT](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-08-dot-g4-interior-coin-source-jets-1213z/INDEPENDENT-HAND-REVIEW.md),
[later status](https://github.com/Sodelin/Research-Commons/blob/8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6/research/2026-10-08-dot-g4-interior-coin-source-jets-1213z/README.md).
The frozen candidate heading is historical. The source rule is PROVED,
with its existing scoped AI hand acceptance; missing Lean does not reopen it.

## Literal specialization, not a new all-order rule

Use delta for the OLD small parameter, a0 for its base coin, h0 for its
mean coefficient. The actual old arms and coin are

    x=delta^2*h0/a0-delta^3*u/a0^2+delta^4*v/a0^3,
    y=delta^2*h0/(1-a0)+delta^3*u/(1-a0)^2+delta^4*v/(1-a0)^3,
    g=a0+delta*w, zeta=w*h0-u.

Its Section4 ALREADY proves for EVERY fixed j>=3

    D_j=delta^(2j)*J_j+O(delta^(2j+1)),
    J_j=(-1)^j*(j-1)!/2*h0^(j-3)
                      *[h0^3-j*zeta^2/(a0*(1-a0))].

Set

    a0=1/2, h0=a/2, u=v=0,
    w=sqrt(kappa*a)/2, delta=sqrt(epsilon).

Then x=y=a*epsilon, g=(1+sqrt(kappa*a*epsilon))/2 and
zeta^2/(a0*(1-a0))=kappa*a^3/4. The old formula is EXACTLY

    D_j=(-1)^j*(j-1)!/2^(j+1)
                      *a^j*(1-2j*kappa)*epsilon^j+O(epsilon^(j+1)).

The improved remainder follows from equal-arm coin symmetry: the
specialized law is even in delta, hence analytic in epsilon=delta^2.
The OLD joint lower vanishings and this parity supply the IFT division.
No fresh graph enumeration or source coefficient is needed.

## What was wrong in f22a48a4, and what remains proved

The initial [paired-diagonal proof](https://github.com/Sodelin/Research-Commons/blob/f22a48a41a8b2f00a3d4abeb4e16bfb7e1c8f981/research/2026-10-24-g3-weak-equal-arm-paired-diagonals/PROOF.md),
16465B/SHA2564d0811415b80ca77704f00bf84fce274c9d5ff8bc8668679961bd5ff8462b4c6,
and its source-owner summary called this a new restricted source rule.
That attribution is WITHDRAWN. Its path/cycle argument reproduced the
retained connected-incidence theorem. It is not new mathematical progress.

The direct provider cited in the inspected R8 source scope led to this
Section4, but was not followed before f22a48a4 was frozen. Searches of newer
names and selected predecessor statements were insufficient. A failed
keyword lookup was not absence evidence. The exact original and later
status are now retained under the actual equal-arm/square-root-bias aliases.

The paired-diagonal conclusion itself remains PROVED BY HAND as an
application: finite regular sums and IFT use OLD suppliers, and the
positive ordinary pad plus finite block repetition sets both passages.
For every finite M and0<C<D<sqrt(C), one strict equal-arm near-fair word
has COMMON E(C) at all arities and I diagonals D^binom(n,2) through M.
The same C,D work across caps with a new finite word allowed per cap.
Its full I forest/commutation equations are still uncontrolled.

No novelty claim is made for the coefficient, sign method, regular-sum
lemma, IFT or general prescribed-time method. Historical novelty of the
particular paired application is unassessed. The old source review is not
an independent review of that application.

## Changed entrypoints and preserved history

The original f22a48a4 bytes stay immutable. An exact own-workspace authored
archive also preserves the pre-correction proof/status and entrypoints.
The current proof replaces the redundant all-order derivation with the
literal old specialization. Source status, current lookup, AGENTS,
continuation and audit mark the rule OLD/PROVED/REUSE. No new critical-
Newton source task, next-cap producer or old diagonal derivation is active.

The paired-diagonal application stays closed. CP-Pair is the one active
unproved source-rigidity implication. Original all-core source reduction,
completed COMMON/BOTH suppliers, other owners and all holds are unchanged.
There was no source/solver/model/native/Lean/CI execution, old-suite replay,
local Git mutation, new worker or new key. No proof is reopened because
formalization or independent review is absent.

