# Cutoff-free coarse paths in vanishing-width Wilson strips

2026-11-24. Research Commons / Dot. Scoped hand deduction for the actual four-dimensional SU(2) Wilson law. The input is the joint bad-cube estimate of [Bhattacharjee et al., v4, Theorem 108 and Corollary 110](https://hexagonmath.org/pdf/2610.00341v4). No new Lean verification. This is a path-existence and length bound, not a conditional mixing or mass-gap bound.

Fix the paper's cutoff threshold rho=1/12 and a fixed nonwrapping axis-aligned straight segment on the doubled lattice, with m comparable to L fine lattice spacings in order of magnitude (m counts coarse links). Theorem 108 gives probability at most q^k that any k prescribed distinct fine unit cubes are bad. At the paper's one-loop beta=(11/(3 pi^2)) log L+O(1), this has q=O((log L)^6 L^(-gamma)), gamma=(11/(3 pi^2)) rho^2/16>0. The claim below also works if q tends to zero and L q^r tends to zero for some fixed r.

## Tile masks, allowing overlaps

In a fixed transverse plane take m columns and W rows of coarse unit squares, with the original segment on the bottom boundary. Call a tile blocked if a bad fine cube occurs in any of the masks Z_e for its four boundary coarse edges. There are at most 96 cubes in the union. Every edge of an unblocked tile has chi=1 by Corollary 110, so the cutoff is inactive and the coarse link is the paper's chart path average. This conclusion is about the cutoff, not identity of the two link holonomies at different scales.

A fine cube can be in the masks for at most eight coarse edges, as counted in Corollary 110. Each such edge borders at most two tiles in the planar strip. Thus any fine cube lies in at most sixteen tile masks. For k specified distinct tiles to be blocked, choose a bad witness cube from each mask. There are at most 96^k choices, and each choice uses at least ceil(k/16) distinct cubes. Thus the probability is at most 96^k q^ceil(k/16). The marginal bound for one tile is 96q. No conditional Wilson estimate, disjoint-neighborhood assumption, or independence is used.

## Local route and length

Choose fixed W with gamma ceil(W/16)>1; for large L we have m>=W. A union bound over windows of W consecutive columns and over W chosen tiles among their W^2 tiles shows that the probability some window contains at least W blocked tiles is at most

    m binom(W^2,W) 96^W q^ceil(W/16) = o(1).

The first and last columns are both fully unblocked except with probability at most 192 W q. On the complementary good event, mark a column dirty when it has any blocked tile. Every contiguous run of dirty columns has length less than W: otherwise its first W columns would already have at least W blocked tiles. Extend a shorter run to a window of W columns inside the strip. Hence each run contains fewer than W blocked tiles total and has an entirely unblocked row through it.

For each [s,t] dirty run, ascend from the bottom line at the left boundary of column s, along the right vertical boundary edges of the unblocked column s-1; follow the bottom edges of the chosen unblocked row across the run; descend at the right boundary of t, using the left edges of the unblocked column t+1. For clean columns outside runs, follow the original line. Every edge used borders at least one unblocked tile. The endpoints are unchanged. The path uses exactly m eastward steps and at most 2(W-1) additional vertical steps per dirty run. Choose the first available unblocked row to obtain a measurable route depending only on gauge-invariant indicators. Traversing an edge backwards uses its inverse and the same cutoff.

Let D be the number of dirty columns. The one-tile marginal gives E D <= 96 m W q. In particular on an event of probability at least

    1 - 192 W q - m binom(W^2,W) 96^W q^ceil(W/16) - 96 W sqrt(q),

the route has at most m+2(W-1)m sqrt(q) steps and stays within W-1 coarse lattice spacings of the original straight segment. Indeed Markov gives P(D>m sqrt(q))<=96 W sqrt(q). The filling between the original segment and the routed one can be chosen as rectangular patches over the dirty runs, with at most (W-1)D coarse tiles. At fixed physical volume this is a vanishing-width, asymptotically length-preserving modification, even though a fixed strip centerline need not itself be cutoff-free.

## What remains

This removes the geometric need to condition on a completely good prescribed straight route, but does not remove defects from a region or from the fillings. In particular small physical area does not bound the Wilson holonomy change: the number of plaquettes in the filling can diverge, their products need not commute, and the choice of route is field-dependent. Nor is the chessboard estimate uniform under conditioning on exterior links (see Proposition 111 and the following discussion). To use the construction for the physical mass bridge, one needs a bound on transport under these actual field-dependent replacements or a mixing estimate that can exploit alternative routes. The present deduction supplies neither.
