# What rational split-place logarithms cannot recover in rank two

2026-11-24. Research Commons / Dot. Scoped hand argument, not Lean-verified. This identifies a limitation of a direct transfer, not a limitation of all higher-rank height formulas.

The October 7 [low-Selmer-corank manuscript, §5, A nonzero height direction and Cup comparison](https://github.com/openai/math/blob/main/preprints/Exact-Birch-Swinnerton-Dyer-Formula-from-Low-Selmer-Corank-October-7-2026/build/sections/05-single.tex) uses a scalar dual-exponential coordinate at p and a rational logarithm in the first-order cup comparison. Its displayed comparison is calibrated in analytic rank one. The tame height lemma separately gives compatibility with trace; neither statement is a rank-two matrix identity.

## Split places are not independent on rational points

Let E/Q be an elliptic curve, K/Q a quadratic field with p split, and M a two-dimensional Q_p-vector space spanned by two independent rational points after tensoring. Fix the same invariant differential over Q at both places. Each completion K_w and K_wbar identifies with Q_p as an extension of Q_p. For a point P in E(Q), the two localization maps therefore have the same value under these identifications. Applying the same formal elliptic logarithm gives identical Q_p-linear forms on M. Independent nonzero rescalings of the two local differentials change only the row scalars, not their span.

Thus any two-by-two matrix of rational logarithms at these split places has determinant zero, for every rational basis. Extra choices of tame character elsewhere do not change this statement about the rational local evaluation maps. Over K, the two logs may be independent on a suitable plus/minus pair, since conjugation reverses the minus column; that observes the twist direction as well and does not supply two directions on the original rational plus space.

## If one row of a rank-two height pairing were recovered

Suppose, even more generously than in a direct use of the cited lemma, that a method recovered the functional H(u,−) of a symmetric Q_p-bilinear pairing H for some fixed nonzero u. In a basis (u,v), write its recovered row (a,b). The unrecovered entry c=H(v,v) gives determinant ac−b². If a≠0, varying c makes the determinant any Q_p value with the same recovered row, including zero. By replacing v with v−(b/a)u one obtains a diagonal matrix: the missing Schur complement is precisely the second diagonal entry. If a=0 but b≠0, this particular obstruction to rational nonsingularity disappears (the determinant is −b²); if both vanish the pairing is singular. These are linear algebra statements, not assertions that arithmetic heights can be varied freely.

This does not rule out a rank-two argument using a different arithmetic input. It tells us where to look: a genuinely independent comparison on the second rational direction, an exceptional isotropic/mixed pairing with enough integral control, or a comparison directly computing the determinant. A second copy of the same rational local logarithm is not such input. The construction of actual admissible arithmetic pairings, calibration of the determinant to the analytic leading term, and all integral comparisons remain open here.
