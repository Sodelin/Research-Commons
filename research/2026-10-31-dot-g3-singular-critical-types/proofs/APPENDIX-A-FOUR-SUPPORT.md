# AppendixA:91 types for four-active normals and rank-three words

This is an optional sharper refinement, not a competing general bound. All source assumptions and rank terminology are those of the main note.

At any strict critical point put d_λ=c_λ/f_λ(p,q). Criticality and c·Λ=0 imply

 Σd_λ(1−q^λ)=0,  Σd_λλq^(λ−1)=0,  Σd_λλ=0.

Therefore F(t)=Σd_λ(1−t^λ) has distinct double positive roots q and1. A nonzero vector with at most3 active entries would give at most4 monomials and hence at most3 positive zeros counted with multiplicity by Descartes' rule. Thus every critical normal has at least4 active entries.

Fix any four-element support J⊂Λ. Let M_J(q) be the3×4 matrix with rows λ,1−q^λ,λq^(λ−1). Its kernel is one-dimensional throughout0<q<1: if dimension were at least2, a nonzero linear combination could remove one coordinate, contradicting the preceding double-root argument. Every nonzero kernel vector has all four entries nonzero.

Take its signed3×3 cofactor vector d(q), which is polynomial and nowhere zero on this interval, and put e(q)=diag(q^λ)d(q). The vectors d,e are independent since their coordinate ratios are the distinct numbers q^λ. A critical normal c belongs to the projective span of d(q),e(q), because c_λ=f_λd_original and d_original is proportional to d(q).

If a fixed nonzero c had infinitely many critical points, distinct-pole partial fractions rule out a vertical line and bound each fixed-q fibre by5. Semialgebraicity then gives an interval in the q projection. Every3×3 minor of [d(q),e(q),c] vanishes on that interval, hence identically. Thus c belongs to the intersection of the spans at q=1/2,1/3,1/4.

For EACH of the15 possible supports this intersection is{0}. The exact rational check computes the two annihilator rows of each of those three planes, stacks them into a6×4 matrix, and records a nonzero4×4 minor. Every stack has rank4. Complete selected row indices, rational vectors and determinants are supplied in checks/FOUR-SUPPORT.json and reconstructed by checks/four_support.py. This is decisive because the hypothetical interval forces polynomial identities; it is not an inference from a numerical sample.

A quantitative bound follows. Each coordinate of d has degree≤35, and each coordinate of e has degree≤56. At least one of the3×3 minors above is a nonzero polynomial of degree≤91. Thus critical q has at most91 values. At a fixed q, the coefficients α,β in c=αd+βe are unique; an actual critical point has α+β≠0 and p=β/(α+β), so at most one p occurs. Hence every four-active normal has at most91 strict critical pairs, including for real transcendental coefficients.

For a nonempty free-map word of rank≤3, its annihilator has dimension≥3. Setting any two coordinates to zero leaves a nonzero normal of support≤4. The first paragraph excludes support≤3, so every cell lies in a four-active fibre and there are≤91 types. Furthermore any three output rows of the drift plus one cell's two derivative columns are independent: a dependence would give a prohibited normal with≤3 active coordinates. Thus the rank of a nonempty word is at least3, and under the hypothesis it equals3. None of this bounds integer repetitions or acquires a hidden rank/normal from observed data.
