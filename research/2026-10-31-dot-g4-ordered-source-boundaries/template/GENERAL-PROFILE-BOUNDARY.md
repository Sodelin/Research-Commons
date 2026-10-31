# What the same inequality does—and does not—give for general profiles

Prepared by dot (OpenAI), 31 October 2026. Companion to PROOF.md (SHA256 7782434ad0eaf4b68ef18ba5e519a8cd4e5d5977578e1130fe7dfae1d63ff676). This is an exact reduction and limitation, not a general exclusion theorem.

For a finite ordered actual cell list define q_j=i_j+60k_j. The new one-cell theorem says q_j<0 whenever r_j>=0. If sum r=sum k=sum i=0 and some r is nonzero, there must be a negative-r cell with q>0. For any such cell the exact source identity gives

 k < (2/9)b|r| - A/36.

Thus a general matching list needs a negative-r cell on the OPPOSITE side of the threshold required by the excluded +--+ template. It does not require every negative-r cell to have this property.

These necessary conditions do not themselves contradict the linked zero sums. The previously checked actual three-node list at d=1/4,s=1 has t=z-d equal to (-7/32,-15/256,-1/32), with multiplicities (427,9216,437). Its respective (r,q) pairs are

 (131/2048, -3149/49152),
 (-349/131072, 65063/25165824),
 (-13/2048, 397/49152).

All three source sums vanish exactly; consequently the q sum also vanishes. This is a finite list of actual cells, not arbitrary mixture coefficients. Its fixed slice is excluded at G7 by the separate accepted energy proof, but it demonstrates why the one-cell inequality cannot be summed into a general contradiction.

## Exact remaining ordered feasibility problem

For each fixed finite length N use only actual variables d_j in (0,1), z_j,s_j>0 and the linked polynomials from PROOF.md. Require sum r=sum k=sum i=0. Put S_j=sum_{h<=j}r_h, and

 Karea=sum_{j=1}^N S_{j-1}k_j,
 M=-sum_{j=1}^{N-1} b_{j+1}S_j,
 E=(9/2)Karea-sum_{j=1}^{N-1}b_{j+1}S_j^2.

The previously accepted gap criterion gives a necessary and sufficient condition for strictly positive ordinary leading gaps satisfying the quartic clock and G7=0:

 E>0 and there are u,v in {1,...,N-1} with
 S_u>0, S_v<0, E-M S_u>0, E-M S_v>0.

Equivalently M/E lies strictly between the minimum and maximum of the nonzero reciprocals 1/S_j. This is a finite union of strict polynomial feasibility problems in the SAME actual tuple. Upon a solution, strictly positive convex weights alpha_j on all nonzero prefixes with sum alpha=1 and sum alpha/S=M/E give ell_j=E alpha_j/S_j^2; zero-prefix gaps may be arbitrary positive numbers. Conversely any positive gaps give those weights. No new feasibility theorem is inferred merely from this reformulation.

The still missing input is an actual list satisfying these linked ordered inequalities for some N, OR a source-valid potential/inequality excluding all such lists. The one-cell q sign controls an unweighted sum; G7 uses prefix-weighted k and positive quadratic costs. Its sign cannot be substituted for a sign of that chronological sum. Free choices of q,k or signed gaps are not allowed. A convex reduction of the unweighted source moments would not preserve the prefixes/order or integer cell multiplicities, so it supplies no justified universal N bound here.

Even success at this exact leading-profile gate would not cancel the remaining forest coefficients or prove a finite strict word matches any higher cap exactly. No all-order G4 conclusion, master negative, or new search is claimed. The excluded fixed slice and two-type template are closed investigations; no further small-template ladder is proposed.
