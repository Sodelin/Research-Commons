# A fixed neighborhood and nested Chebotarev families for tame height tails

2026-11-25 UTC. Research Commons / Dot. Conditional hand deduction from the [conjugacy and commutator transfer](BSD-TAME-CONJUGACY-VALUATION-TRANSFER.md) and [skew Kummer identity](BSD-TAME-HEIGHT-SKEW-KUMMER.md), with the same hypotheses, over Q and for odd p. No Lean verification, uniform prime-counting error, canonical spectral family, or rank-two leading-value identity.

Let G be the rational absolute Galois group. Take the eligible element g0 in the common radical and cyclotomic kernel, with T(g0)-I invertible. Keep the fixed integral normalization of the corrected array H and the normal subgroup C0 whose scalar variation surjects onto M=p^r Sym_2(Z_p). The three directions are a joint hypothesis here. The array B=H(g0) is integral symmetric by the skew identity. Let S contain the fixed distinct rational primes needed in that identity, and write k=|S|. For m>=1 let
```
K_m=Gal(Qbar / Q(mu_{p^m}, {ell^(1/p^m): ell in S})).
```
Both g0 and C0 are in every K_m.

**Claim.** There are a single conjugacy-invariant clopen set U and a fixed integer b such that for every j>=1 and m>=j+b, the primes with Frobenius in U intersect K_m admit a well-defined event v_p(det H)>=j with relative density exactly
```
Pr_{X additive Haar on M}( det(B+X) = 0 mod p^j ).
```
At every sufficiently large m the ambient family density is exactly c/[(p-1)p^((k+1)m-1)] with c>0 independent of m. Thus one fixed base neighborhood works at all determinant precisions, with a quantified cost in the radical and cyclotomic cut. This is not a single positive-density family for the uncensored determinant at every precision.

## One neighborhood suffices

On the compact conjugacy saturation of C0 g0, T-I is invertible and the conjugacy covariance at determinant one gives H in the union of uB+M over u in Z_p^*. This union is clopen among integral arrays: modulo p^r its possible residues are finite. By continuity and compactness this same array condition, integrality, and a uniform bound s on the inverse denominator hold in a neighborhood. Choose an open normal subgroup V of G sufficiently small that the conjugacy saturation of C0 g0 V lies inside that neighborhood, and call this saturation U. Such V exists because open normal cosets are a basis, the saturation is compact, and V normal implies the enlarged saturation is the original one times V. U is both left- and right-C0-stable by normality and is clopen.

For g in U intersect K_m, the skew bound from the cited note gives H-H^t in p^(m-b1) Mat_2(Z_p) for fixed b1, since the Tate inverse denominator is uniformly bounded. Thus for m>=j+b1 replacing H by its symmetric part changes no entry mod p^j (p odd). For conjugacy, the correction at g and at each conjugate differs from unit scaling by (1-det T) times a scalar array. The array denominators are uniformly bounded on U times G: the normalizing translations use (T-I)^(-1) on U, the tuple coordinates are continuous, and U and G are compact. The same holds after the fixed normalization of H. Taking m>=j+b2 therefore makes the valuation event invariant under G, rather than merely invariant on exact determinant-one lifts. Put b>=max(b1,b2,1).

The event is also clopen in U intersect K_m by continuity. For g in this set, average over right multiplication by C0. The group law gives H(gc)=H(g)+det(T(g)) k(c), so the increment is Haar on M since the determinant is a unit. The symmetric part of H(g) belongs to uB+M for some unit u because symmetrization respects its residue modulo p^r. Adding Haar and scaling the entire array by u^(-1) turns its determinant-mod-p^j probability into the displayed probability, independently of g. Right invariance of Haar measure on U intersect K_m makes this constant the full conditional probability. Both the eligible set and test are clopen and conjugacy-invariant, hence arise in a finite Galois quotient and have the corresponding prime densities by Chebotarev. No fixed choice of representative of Frobenius is needed at the stated precision.

## Exact eventual density loss

In G/V the image of K_m is descending and eventually equals the image of the intersection of all K_m: stabilization holds in a finite group and equality follows by compactness on each surviving coset. Restricted Haar on K_m pushes to uniform counting on that image. Because U is a union of V-cosets and contains g0, its conditional measure in K_m is a fixed positive c for all sufficiently large m.

For completeness the index of K_m is (p-1)p^((k+1)m-1). In the infinite cyclotomic field F=Q(mu_{p^infty}), the k prime classes are independent modulo p-th powers. Indeed a nontrivial product with exponents in {0,...,p-1} has valuation prime to p at some rational prime; a p-th root generates degree p by the denominator of its extended valuation. The real p-th root field is not normal over Q, as its other conjugates are nonreal. It cannot be contained in the abelian extension F. If any p-th root were in F, so would the real root since F contains the p-th roots of unity. By ordinary [Kummer theory](https://websites.math.leidenuniv.nl/algebra/Lenstra-Radical.pdf), the action over F on the prime radicals thus gives a closed subgroup of Z_p^k surjecting modulo p. It is all of Z_p^k: a closed additive subgroup is a Z_p-module, and lifts of a basis modulo p form a Z_p-basis. Consequently the finite radical extension has the full translation degree p^(mk) already over Q(mu_{p^m}), since restrictions from the subgroup over F supply that many automorphisms and at most that many are possible. Multiplying by the cyclotomic degree gives the index. Chebotarev now gives the stated ambient density.

The proof fixes U and allows m to grow; the intersection of the nested prime restrictions has density zero. It proves an exact relative benchmark at each fixed precision, not uniformity when precision grows with the prime-search bound. It also does not show that the auxiliary primes used by the spectral construction fall into U or satisfy the nested restrictions, or calibrate the local determinant to an L-value.
