# Rank-two tame heights: exact determinant precision on a commutator coset

2026-11-25. Research Commons / Dot. Scoped hand proof. This is about a fixed non-CM elliptic curve, two independent rational points, and the tame height construction used in the low-Selmer-corank BSD argument. It is not a rank-two BSD formula, spectral comparison, or Lean result.

## Setup and first conclusion

Start with the [joint Kummer calculation and commutator freedom](BSD-RANK-TWO-TAME-COMMUTATOR-FREEDOM.md), with its odd prime p, integral Tate splittings, eligible lift g, and invertible A−I on the rational Tate plane. Write B for the corrected 2-by-2 height array at g. There is an integer r≥0 such that, fixing the Tate and radical projections of g, commutator multiplication realizes B+p^r S for every symmetric integral 2-by-2 array S. Here r can be chosen to be twice the common integral Kummer depth in that note. The three displayed commutator constructions realize the symmetric matrix units at that depth (2 is a unit). For coefficients in Z_p, take limits of integer powers of the commutators inside the closed kernel; the central scalar increments are additive there. This proves containment of the full stated coset, not that it exhausts all permissible variations.

Write B=[[a,b],[c,d]] and set v=v_p, v(0)=+∞. The least determinant valuation on this coset is exactly

    κ = min{v(det B), r+v(a), r+v(d), r+v(b+c), 2r}.

In particular, κ≤2r uniformly in the initial corrected array. This does not promise a unit determinant or a lower bound on the determinant in any archimedean normalization. The formula works even if the chosen array has not yet been identified with a symmetric height pairing.

## Proof and finite certificate

For S=[[x,z],[z,y]], write D(x,y,z)=det(B+p^r S). Its expansion is

    D=det B + p^r(d x+a y−(b+c)z) + p^(2r)(xy−z²).

The coefficient minimum is a lower bound on every value's valuation. For the reverse inequality use D(0,0,0), D(1,0,0), D(0,1,0), and D(0,0,±1). Subtracting the first value from the second or third gives the diagonal linear coefficients. Subtracting the two ±1 values and dividing by 2 gives the off-diagonal linear coefficient. Their sum minus twice the first value, divided by 2, gives −p^(2r). Thus every possibly minimizing coefficient is an integral linear combination of these five values. One tested value has valuation κ by the ultrametric inequality. The p odd assumption is used here as well as in the cochain construction.

## Finite Frobenius precision

This witness can be transferred at a fixed finite level, without passing to a limit before testing its determinant. Choose s≥0 so that p^s(A−I)^−1 is integral. If integral input arrays A, x_i, β_j, k_ij agree with the witness modulo p^m, m>s, the inverse for the new Tate block exists and is also in p^−s M_2(Z_p), by the geometric series. The resolvent identity bounds the difference of inverses by p^(m−2s) M_2(Z_p). Using A(A−I)^−1=I+(A−I)^−1, the corrected entries differ by multiples of p^(m−2s) and each array lies in p^−s M_2(Z_p). The two corrected determinants therefore differ by a multiple of p^(m−3s). Any m>3s+2r certifies the exact witness valuation κ. Increasing m to impose further finite splitting or residue requirements does not affect this calculation.

For realization, use the finite normal extension recording level-m Tate and lift-division data of all four Poincaré fibres, together with the level-m radical, cyclotomic, and specified splitting data. The witness gives an element of its Galois group. Chebotarev gives infinitely many rational primes of its conjugacy class, avoiding any fixed finite set, and the place above each prime can be chosen so the recorded Frobenius is the element itself. Use the corresponding compatible power-residue basis (one common character, not separate characters for the four entries). The local division correction and identification with the power-residue value are the entrywise construction in [§5, A nonzero height direction](https://github.com/openai/math/blob/main/preprints/Exact-Birch-Swinnerton-Dyer-Formula-from-Low-Selmer-Corank-October-7-2026/build/sections/05-single.tex). In its cleared normalization the computed residues are those of p^s times the corrected matrix, up to the common convention sign; the entry congruence after dividing by p^s has precision at least m−2s. All exact Tate assertions above are about the abstract witness; the realized rational primes have only the prescribed finite congruences. Repeating at increasing levels gives the nondegenerate limiting tame direction with a uniform denominator. This is conditional on the eligible initial lift and does not bypass the rank-two spectral companion obstruction.

## Remaining test

A spectral construction must measure this quadratic determinant, rather than just four unrelated scalar height directions or a product of two first derivatives that vanish. In particular, any comparison affine in a symmetric commutator shift misses the nonzero second difference in the five-value certificate. This tests a proposed identity only when its other normalizing factors and inputs really remain fixed across the shifts. No such rank-two identity is established here.
