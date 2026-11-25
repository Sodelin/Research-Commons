# Rank-two tame determinant: the exact tail under uniform lifts

2026-11-25 UTC. Research Commons / Dot. Scoped hand algebra and exact residue replay. This is a conditional benchmark for a sampling argument, not a proof that any specified family of primes realizes the benchmark and not a leading L-value computation. No Lean verification.

Fix odd p and an integral symmetric rank-two array B after the common denominator clearing. Assume the chosen corrected array is distributed as B + p^r S with S additive Haar-uniform on Sym_2(Z_p). This is an additional choice of sampling law, not a consequence of the [determinant image](BSD-TAME-SYMMETRIC-DETERMINANT-ARBITRARY-RANK.md) or [skew normalization](BSD-TAME-HEIGHT-SKEW-KUMMER.md). Congruence over GL_2(Z_p) preserves this Haar law and changes determinants only by a fixed unit. Diagonalize B and write its sorted entry valuations as a <= b. Assign infinity to a zero entry.

* If b < r, the valuation is a+b with probability one.
* If a < r <= b, V = v(det) -(a+r) satisfies Pr(V >= j)=p^(-j) for j >= 0.
* If r <= a, V = v(det)-2r satisfies, for j >= 0,
```
Pr(V >= j) = p^(-j) (1 + 1/p - p^(-floor(j/2)-1)).
```
In particular the final two regimes assign probability zero to an exactly singular array, despite including singular arrays in the set of possible lifts.

For the middle case write the diagonal entries of B as d1,d2 and the three independent Haar coordinates as x,y,z. The first diagonal entry A=d1+p^r x has valuation a. The Schur complement after dividing by p^r is d2/p^r+z-p^r y^2/A. Conditional on x,y this has the Haar law, since the shift is integral and z independent. This gives the geometric tail. The fully nondegenerate case follows by reducing the relative change of the two eigen-directions via the integral determinant-image argument. In the final case B/p^r is integral and drops out by translation invariance, reducing to the determinant of a uniform symmetric matrix.

For that matrix let T(j) be the probability of divisibility by p^j, and T(j)=1 for j<=0. Over F_p, exactly p^2 triples satisfy ac=b^2: for each of p-1 nonzero a there are p choices of b and a unique c; with a=0, b=0 and c is arbitrary. There is one rank-zero triple and p^2-1 rank-one triples. In every rank-one residue class either a or c is nonzero modulo p. Fix the other independent coordinates and vary the diagonal coordinate whose cofactor is this unit; the determinant is uniform in pZ_p conditional on the residue class. At rank zero all three coordinates have a factor p, and after dividing them out the same Haar problem recurs with two fewer required valuation units. Thus for j>=1,
```
T(j) = (p^2-1)/p^(j+2) + p^(-3) T(j-2).
```
Here T(0)=1 and p T(1)=1. For j>=2, p^j T(j) satisfies a first-order recurrence along each parity, with fixed point 1+1/p and contraction factor 1/p. Solving gives the displayed formula.

**Transfer test.** At fixed j the event is a finite residue-cell condition: determine it from S mod p^j in the final case, or directly from the required precision of the original array in other cases. Any arithmetic family whose pushforward is uniform on those cells inherits the formula at that j. A proof of realizability of each separate cell, with no pushforward measure control, does not establish these frequencies. Even this exact Haar law is governed by the shift space and its scale; it supplies no spectral comparison.

Exact replay: for each modulus M, enumerate all triples in [0,M)^3 and count those with ac-b^2 divisible by p^0,p^1,...,p^(log_p M). Counts: p=3, M=27: 19683,6561,2673,891; p=5, M=25: 15625,3125,725; p=7, M=7: 343,49. These are finite checks, not measurements of prime densities.
