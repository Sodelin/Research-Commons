# Independent review: a genuine three-tip meeting gauge

Reviewer: Codex critical-review lane, 13 October 2026. Hand proof audit
with a separately labelled exact finite replay; no formal verification.

Reviewed [THREE-TIP-INTERACTION-GAUGE.md](../whole-source/continuation-1900z/THREE-TIP-INTERACTION-GAUGE.md),
SHA256 `aa1043c3297218a9f0d93eb6d323b2e0b08e39fb0d83b8957807b06597ee1ac2`.

**Hand acceptance of the within-shape identification claim.** For the
genuine opened shape `((A0,B),A1)`, the normalized tables at allocations
(2,2) and (2,3) identify its interaction exposure, A routing coin, and
both A arm survivals. Only the B pendant ordinary factor remains in
the displayed parameter tuple. This does not compare different shapes,
classify a genuine four-tip gauge, or close G4.

## Probability and inversion checks

When both A roots take the early route, all selected roots meet at the
early branch point, so the remaining internal exposure followed by
infinite completion has the ordinary completed topology law Q. When
both A roots take the late route, the B roots must survive that internal
exposure separately. The mixed-route configurations have singleton A
arms and hence no A pendant merger factor. These facts give exactly
the decomposition (1), including the weights and the B pendant factor.
The one-A reference calculation (2) follows by the same reasoning.

For T_j with the first A root early, precisely zero through j prescribed
B-spine mergers can occur in the internal population. Given r mergers,
each successive binary pair is uniform among the current pairs, so the
specified order has probability
`1/product_(ell=m+2-r)^(m+1) lambda_ell`. The remaining roots complete
one specified caterpillar. If the second A root is early, any internal
merger would produce a clade absent from T_j, so only no merger is
compatible. This proves the two terms in (4). Multiplying the prescribed
history denominator by the completion kappa repeats exactly one
lambda factor, giving the kappa and denominator of (5). The indices and
the final-merger case were checked explicitly.

At m=3 the two successive contrasts share the same strictly positive
prefactor. Their ratio is therefore `3 p_(4,1)/p_(4,2)`. Both pure-death
probabilities are positive at an interior exposure, and the displayed
Wronskian factorization is negative throughout `0<z<1`. Thus recovery
of z has no exceptional interior parameter. The last contrasts at m=2
and m=3 then give `k=(1+r z^3)/(1+r z)` with r positive. This map has
strictly negative derivative and the inverse in (9) is correct. The
formula for v2 follows directly, and the two remaining linear equations
have determinant proportional to `z-z^3`, which is nonzero. Both arm
survivals are therefore uniquely recovered. No conditional-route
quantity is used as an observation: all S terms are evaluations of the
specified finite ordinary model after z is recovered.

## Positivity and boundary scope

The proof allows either A arm survival to equal one, so it does not
assume an original positive edge where the selected reduction might
have an empty pendant segment. Its genuine internal edge is a nonempty
path between distinct branching vertices; its exposure is a sum of
positive original exposures and hence z is strictly below one. A
coincident or limiting pair of branch points gives z=1 instead. In that
case the interaction vanishes, the contrasts are zero, and the opened
tree is a private A two-arm factor followed by ordinary completion.
The proof explicitly treats that case separately and makes no division
by its vanishing contrasts. Endpoint coins are outside the within-shape
strict claim and require their own collapsed treatment in any future
boundary classification.

Both genuine mixed four-tip forms remain: a mixed balanced tree and a
mixed caterpillar. For example the latter is realizable by a binary
cut-child network with tree chain `r -> v -> u`, A-hybrid parents u,v,
and B-hybrid parents u,r. Positive dates and pendant descendant subtrees
give an admitted outer-labelled realization. Thus a general reduction
to the proven three-tip shape would need more than suppression of
same-colour cherries. The reviewed proof correctly makes no such claim.

## Separate finite evidence

The reviewer reran the submitted exact script against the unchanged
inherited forest compiler, redirecting only its receipt into the review
directory. It passed 15 split-sector probabilities computed by direct
finite forest composition and two rational parameter-recovery controls,
including unit A survivals. The latter are algebraic recovery controls
from the normalized formulas, not an additional original-source compiler
test. The replay receipt is [THREE-TIP-REPLAY.json](THREE-TIP-REPLAY.json)
and agrees byte for byte with the author's receipt. These controls
support the index and coefficient audit; they do not establish the
general within-shape theorem or any four-tip assertion.

Correctness is supported by the hand argument and independent audit.
Applicability is the bounded meeting shape derived in the legal invariant
theorem, with its explicit positivity conditions. Historical novelty is
not certified. No Lean or Rust verification is claimed.
