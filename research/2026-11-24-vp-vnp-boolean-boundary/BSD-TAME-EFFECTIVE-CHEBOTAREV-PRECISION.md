# Effective growing precision in the nested tame height families

2026-11-25 UTC. Research Commons / Dot. Conditional hand deduction, no Lean check or prime enumeration. It strengthens the [nested density result](BSD-TAME-NESTED-CHEBOTAREV-TAIL.md) from fixed precision to a uniform growing range, assuming Dedekind GRH for explicit finite tuple extensions. The original eligible-lift, joint Kummer and compatible cochain conditions are still required. It does not identify the spectral auxiliary family or a rank-two leading L-value.

Keep p odd, r, B, U and the k prime radicals of the nested construction. Write P_j for the additive-Haar probability of determinant zero modulo p^j in B+p^r Sym_2(Z_p). For a prime bound X, count primes in U intersect K_m and in its event v_p(det H)>=j, using the same fixed excluded primes for both counts. There is a fixed shift b such that, for sufficiently large m>=j+b, on Dedekind GRH for the finite extensions constructed below, their respective counts are
```
d_m Li(X) (1+O(E(m,X))),
d_m P_j Li(X) (1+O(E(m,X)))     if P_j>0,
E(m,X)=p^((11+k)m) (m+log X) log X / sqrt X,
d_m=c/[(p-1)p^((k+1)m-1)].
```
If P_j=0 the event is empty. In particular, for every fixed 0<epsilon<1/2 and all m<=(1/2-epsilon)log_p(X)/(11+k) with m>=j+b, the conditional frequency is P_j times 1+O(X^(-epsilon) log² X), uniformly and with no extra loss for a rare nonempty determinant event. These exponents need not be optimal.

## A finite quotient of controlled degree

Use the formal group law from the [conjugacy note](BSD-TAME-CONJUGACY-VALUATION-TRANSFER.md). Its projected tuple consists of T, x_1, x_2 and k_11,k_12,k_22. It is a group projection: each retained scalar multiplication uses only the corresponding scalar pair and the retained vectors, not the omitted scalar k_21. After fixed denominator clearing these coordinates are integral, with integral structure constants. Indeed multiply vector coordinates by a fixed p-power making their image integral (it is compact), then scale all scalar coordinates by a p-power at least twice that power and sufficient to make them integral; in a symplectic integral Tate basis the rescaled cross term has integral coefficients. Any fixed relation to the normalization H costs only an additive shift in precision.

The inverse matrices (T-I)^(-1) have a uniform denominator bound p^s on U. For two such matrices the difference of their inverses is the product of the two inverses and the difference of the original matrices, up to sign and order. Thus computing any of H_11,H_12,H_22 modulo p^j requires only tuple coordinates modulo p^(j+b0), with b0 fixed, absorbing both p^(2s) and all normalizations. In U intersect K_m the missing H_21 agrees with H_12 modulo p^j by the skew estimate once m>=j+b. The determinant test is then H_11 H_22-H_12² modulo p^j. It is conjugacy-invariant at that precision by the prior covariance proof.

Take b large enough for these requirements. At common depth m, the entries of T, the two vectors, and three retained scalars supply at most p^(11m) possibilities. Adjoin the m-th prime radical data and the fixed finite quotient defining U. With cyclotomic action already given by det T mod p^m, the radical lifts contribute at most p^(km) possibilities: write g(ell^(1/p^m))/ell^(1/p^m) as an element of mu_(p^m) for each of the k primes; on products the corresponding exponents add with the known cyclotomic multiplier. Hence the combined finite Galois extension L_m has degree n_m=O(p^((11+k)m)) rather than requiring an additional independent cyclotomic coordinate. All the fields are unramified outside one fixed finite set by the original cochain and radical hypotheses and the fixed finite quotient. If necessary, include a fixed compositum of quadratic fields ramified at each prime of this set, so that counting unramified primes excludes those primes exactly; this changes only the implicit degree constant. The numerator and denominator sets are both unions of conjugacy classes in the same quotient, and their exact Haar masses are d_m P_j and d_m.

## Effective transfer, including rare events

[Serre, Theorem 4 and equation (19)](https://www.numdam.org/article/PMIHES_1981__54__123_0.pdf) give under Dedekind GRH for L_m, for a conjugacy-invariant set of density d, an error O(d sqrt(X)(log |disc L_m|+n_m log X)). In the fixed ramification set, log |disc L_m|=O(n_m(1+log n_m))=O(n_m(1+m)). For d>0 divide by d Li(X); the density d cancels even for the rare numerator set. The two relative estimates and their ratio follow. If d=0 the finite conjugacy set is empty, so no error statement is needed. At the claimed logarithmic depth, E is O(X^(-epsilon) log² X). This is uniform in j and m, but neither in the original elliptic data nor without the specified zeta-function hypotheses.

The effective count concerns deliberately constructed sampling families only. There is still no proof that the independent spectral construction chooses primes in these classes, or that their determinants give a BSD regulator or leading value.
