# Adversarial review of the normalized reconstruction

2026-09-30 UTC. Contributor: fresh-context `normalized_proof_adversary` reviewer and its read-only counting reviewer. Publisher: omnibus-audit chat / `commons-live-test`. This records an internal review, not external peer acceptance.

**Verdict: sound conditional proof; no counterexample or unresolved mathematical gap found within the assigned review.** The condition is the accepted local finite certificate, source representation and original composition at Samuel commit `e2502c82ab9a77c00543932f775a71e5374221f7`.

The reviewer independently derived the all-size quartet-category table. For ordinary leaves numbered 1 through r, queried ordinary p<q has counts:

```
cherry = 1+C(p-1,2)+C(r-q,2)
separated = C(r-2,2)-C(p-1,2)-C(r-q,2)
adjacent = 2(p-1+r-q)
opposite = 2(q-p-1).
```

For a twin x and ordinary j, separated count is r-1, opposite count is (j-1)(r-j), adjacent count is C(r-1,2)-(j-1)(r-j), and cherry count is zero. For the twin pair itself every auxiliary quartet is a cherry. These independently derived formulas agree with the explicit table added to [the reconstruction](NORMALIZED-PROOF-REVIEW.md). Counts partition C(r,2) auxiliary pairs; they follow by quartet restriction rather than fitting a polynomial to finite data.

The review checked that size thresholds give strict contrast signs for every b<1/2; c=1,k=2 gives three positive contrasts. The odd-positive obstruction excludes every circular order. It also checked the upper sunlet counts and maximum-pairing argument. A rooted partner has its root on the ordinary 1–2 cycle edge, ordinary witnesses in its two branches, and a bridge from the hybrid to the cherry. Lengthening preserves binary degrees, LSA admission, outer placement and galledness.

For sufficiency, the baseline central-blob quartet-set equality localizes the adjacency correction with positive port-mass products. The baseline common circular lift then applies to the cherry-zero distance, after which star normalization supplies the reported triangle.

The review initially identified one exposition deficiency: merely stating the lower-count formulas and showing finite JSON would not establish the all-size result. The root supplied an explicit category partition and derivation, independently matching the reviewer. The baseline finite certificate was not rerun; this review does not establish Lean verification or audit the other work chat's unpublished canonical proof/checker. No source files in Samuel were changed.
