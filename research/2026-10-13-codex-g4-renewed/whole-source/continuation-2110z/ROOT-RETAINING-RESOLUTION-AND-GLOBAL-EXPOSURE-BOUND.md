# A root-retaining resolution and a global finite exposure bound

Contributor: Codex whole-source lane, 14 October 2026.
**Hand-proof candidate; independent graph/source review requested.**
This exploratory strengthening is NOT used by the accepted natural BOTH
theorem, which needs only the separately accepted selected-anchor bounds.
It is preserved as unreviewed work and supplies no additional acceptance.
This uses the original binary root-LSA cut-child grammar and the accepted
whole positive COMMON profile support. It strengthens the selected-anchor
exposure bound only if the root-retaining argument below is accepted.
It does not bound the number of equal-arm cells or prove finite forcing.

## A supported resolution retains the original root

Let C be the hierarchy of clades common to every full ordinary displayed
profile, and let its maximal proper members be C_1,...,C_k, k>=2. Every
hybrid child-cut set is contained in one such member. In particular two
taxa in different members have no common ancestral hybrid.

Let v_0,v_1 be the two children of the ORIGINAL root. Each has a sampled
descendant, by the admitted source grammar. Let I_i be the nonempty set
of maximal members containing a taxon reachable below v_i. Their union
contains every maximal member. Since k>=2, choose distinct members
C_a in I_0 and C_b in I_1. Choose a taxon A in C_a with a root-to-A path
starting through v_0, and a taxon B in C_b with a path starting through
v_1.

The two paths cannot use a common hybrid: such a hybrid would be ancestral
to A and B, contrary to their distinct maximal members. In fact they
cannot meet below the root at all. The first meeting of paths from the
two root children would be a vertex with two incoming paths, hence would
involve a hybrid ancestral to both selected taxa. Therefore the two paths
can be retained simultaneously by one COMMON parent assignment. Their
hybrid choices are disjoint and can be extended arbitrarily to all other
sites.

Both root branches still have a sampled descendant in that displayed
resolution. Pruning and ordinary suppression consequently retain the
original root as the displayed root. Every natural coin is interior, so
this resolution has positive weight and its full population profile is
in the observed positive support S.

This is an existence statement about a supported assignment, not a new
conditional query. It uses the root-LSA/cut-child source grammar, rather
than claiming the assertion for arbitrary phylogenetic network models.

## Bound every original edge using the same finite support

For each ordinary profile s in S and each taxon A, let d_s(A) be its
finite root-to-A exposure. Put

    D=max_(s in S,A) d_s(A) < infinity.              (1)

Choose the root-retaining assignment from the preceding proof. For every
A, the physical exposure from A to the original root under that one
assignment is at most D. Its serial ancestry representation has minimum
COMMON rootward exposure

    H_A = sum_(ordinary A gaps) a_j
                        + sum_(A cells) shorter_arm_i.

All terms are nonnegative, and the selected route equals H_A plus a
subset sum of its unequal full-arm differences. Hence H_A<=D.

For each A use one target-derived anchor B. The
[joint-ratio palette](ALL-ANCESTRAL-UNEQUAL-PALETTE-FROM-JOINT-COMMON.md)
bounds the number k_A of unequal A cells by
|supp(nu_AB)|-1 and puts their positive differences in a finite set.
Let K be the maximum of these support-count bounds and let Delta_max
be the largest permitted difference, with K Delta_max interpreted as
zero if every palette is empty. Then EVERY rootward A path, under ANY
COMMON assignment, has exposure at most

    H_A+sum_(unequal A cells) Delta_i <= D+K Delta_max.       (2)

Every original finite edge lies on a directed path from the original
root to some sampled taxon, again by the admitted source grammar.
That path can be realized by a COMMON assignment of its hybrid choices.
The edge's nonnegative exposure is at most the total in (2). Thus every
original finite edge of every compatible strict rival has the uniform
target-derived bound D+K Delta_max, independently of rival size.

The claim is about coalescent EXPOSURE, not separate physical time or
population-size parameters. An infinite ordinary ancestral completion
above the original root is explicitly excluded. No total count or lower
edge bound is inferred. Many equal-arm cells or ordinary subdivisions
can share a fixed exposure budget.

If accepted, this removes the possible infinite-exposure faces from
finite-body compactification below the original root. Zero exposures
and endpoint equal-arm coins remain, as do their local cone issues.
The previously proved anchor exposure bound remains valid independently
of this stronger corollary.

Verification: hand graph construction and source path inequalities.
No numerical or Lean verification was performed. Providers are the
original root-LSA/cut-child admission contract, full COMMON displayed
profile supplier, and the separately reviewed joint-ratio palette.
