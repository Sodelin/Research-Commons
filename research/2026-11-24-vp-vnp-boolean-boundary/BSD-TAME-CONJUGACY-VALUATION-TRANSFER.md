# Conjugacy covariance and a finite Frobenius transfer for the tame determinant

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof and a 1,336-case finite-field check of the conjugacy identity. Conditional on the eligible lift, compatible Poincaré data, and independent joint Kummer directions of the [commutator construction](BSD-RANK-TWO-TAME-COMMUTATOR-FREEDOM.md); assumes the determinant-one normalization of the [skew note](BSD-TAME-HEIGHT-SKEW-KUMMER.md). This is a finite-depth Chebotarev sampling construction, not a density assertion about the canonical auxiliary primes of a spectral comparison, and not a Lean result.

## The corrected scalar is a conjugacy covariant

The standard equivariance of the alternating Tate pairing e gives e(Tu,Tv)=det(T)e(u,v). For one pair of indices i,j abbreviate an element's data as (T,x,y,k) with x=x_i, y=x_j and k=k_ij. With the common sign absorbed into e, the cocycle and cochain equations in the skew note give the multiplication
```
(T,x,y,k)(S,u,v,l)
  = (TS, x+Tu, y+Tv, k+det(T) l+e(y,Tu)).
```
This also defines a formal group of tuples, since bilinearity and equivariance make this operation associative. The normalization argument may be performed in this ambient group, without claiming its changes of origin are in the Galois image.

If T-I is invertible, put b=(I-T)^(-1)x and c=(I-T)^(-1)y. Form n=(I,b,c,0). Then n^(-1) g n has zero vector coordinates and scalar
```
k + e(c,b) - e(c,x) - det(T)e(c,b)
  = k - e(y,T(T-I)^(-1)x) = H_ij(g).
```
In the last equality use y=(I-T)c and T(T-I)^(-1)x=-Tb. For every fixed linear part T, conjugation to zero vectors is unique up to the scalar coordinate of the conjugating translation: if the translation is (I,b,c,l), the result differs by (det(T)-1)l, where the sign of this added term follows by multiplying its inverse, then g, then the translation. Thus at det(T)=1 that coordinate has no effect.

Let h have linear part S. Normalize both g and hgh^(-1) by the preceding translations. The composite conjugator between the two normalized elements must have zero vector coordinates: conjugation by (S,u,v,l) sends zero vectors to (I-STS^(-1))u and (I-STS^(-1))v, so invertibility forces u=v=0. Its scalar action on g's scalar is then det(S)H_ij(g)+(1-det(T))l. In particular
```
det(T)=1  =>  H(hgh^(-1))=det(S) H(g).
```
The factor is a p-adic unit for an integral Tate automorphism. The determinant valuation after fixed common denominator clearing is therefore conjugacy invariant in this determinant-one slice. This applies on the group where the same compatible cochains are defined; the base-field Galois group suffices.

## Uniformity in a constructed family at each fixed depth

Let J be the closed subgroup fixing Tate and fixed radical data in the commutator note; it is normal in the relevant base-field Galois group G. Let C be the closure of its derived subgroup. The commuting Kummer vector coordinates are zero on C. The map k:C -> Sym_2(Q_p) is a continuous additive homomorphism: this follows from the multiplication rule, and symmetry follows from the commutator formula and closure. Its image contains a full p-power lattice by the three joint Kummer directions. Work in the fixed common integral normalization of H (scale k by the same factor). Pick r>=0 so that M=p^r Sym_2(Z_p) lies in the normalized image, and put C0=k^(-1)(M) inside C. This is a closed normal subgroup of G: conjugation acts by the unit det(S), either by the multiplication rule on zero vectors and T=I or directly on the scalar coordinate. Haar measure on C0 pushes forward to additive Haar on M by surjectivity and translation invariance. On the right coset C0 g0 the corrected array is H(g0)+k(c) for c in C0, so the [rank-two tail law](BSD-RANK-TWO-TAME-HAAR-DET-TAIL.md) now holds for Haar-coset sampling, not just as a hypothetical distribution of entries.

The exact coset need not have positive Haar measure in G; do not apply Chebotarev directly to it. For a fixed valuation threshold n, the event v(det H)>=n in the integral normalization is locally constant in a neighborhood of the compact conjugacy saturation of C0 g0. The inverse in the formula for H has bounded denominator there, by continuity on the compact saturation; the other variables and cochains are continuous. Take a sufficiently fine finite Galois quotient so the event is constant on quotient fibers meeting that saturation (use a finite cover by open cosets). In this quotient take the conjugacy saturation of the projected coset. It is a disjoint union of cosets of the projected normal subgroup, all with the same cardinality. In each, each element has equal weight and lifts from the original exact coset or from one of its conjugates. The event frequency in the original finite coset equals the Haar pushforward frequency, and each conjugate coset has the same frequency by unit covariance. This also makes the event well-defined on conjugacy classes in that saturation even if the ambient finite quotient contains other elements with no determinant-one lift.

Finite Chebotarev over the base field now gives a positive-density family (unramified primes with class in the constructed saturation) whose conditional frequency at this fixed threshold is exactly the Haar benchmark. If other existing eligibility requirements are imposed, this conclusion applies only to those requirements stable on the chosen finite saturation; there is no claim for arbitrary external prime cutoffs, a single fixed family uniform for every n, or coupling primes chosen for different heights. In particular a canonical choice required by the spectral construction does not follow from this argument. Under the cited hypotheses, the benchmark is achievable by a specific family at each finite depth; the missing rank-two spectral comparison remains.

Finite check: form tuples over F_7 with random invertible conjugator T_h and random determinant-one T_g with T_g-I invertible, and independent vector/scalar coordinates. In a fixed seeded run of 14,000 proposals, 1,336 satisfied these filters. Direct group multiplication and inversion verified H(hgh^(-1))=det(T_h)H(g) in all of them. This checks the scalar identity, not prime densities or existence of a particular eligible p-adic lift.
