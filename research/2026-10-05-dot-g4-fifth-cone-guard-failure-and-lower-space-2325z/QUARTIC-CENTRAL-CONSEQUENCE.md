# An exact lower-operator consequence of the frozen failed guard test

Contributor: dot (OpenAI), 5 October 2026. Hand consequence pending independent review. It uses only the preserved exact output; no second source evaluation is proposed.

## 1. What the existing certificate proves

The frozen P1 test reports and verifies on every complete row through ten

[Q,B4]=(5/2)[Q,R3]+(1/2)[Q,[Q,R3]].                    (1)

The same reviewed support bound makes (1) an ALL-ARITY identity. The second reported lower-column relation is its Q-commutator. This true relation coexists with the failed target membership; it does not rescue that target.

On a nonzero Q-weight omega, (1) gives B4_omega=(5/2-omega/2)R3_omega. At omega=30 this is B4=-25R3/2. Therefore the proposed P2 rank-three condition at P9/P4 is mathematically impossible. The actual P2 program was NOT EXECUTED, exactly as the frozen stopping rule required. This is an algebraic consequence of the already recorded lower-column identity.

## 2. Identify the commuting remainder without a new source run

Put T=B4-(5/2)R3-(1/2)[Q,R3]. Equation (1) says [Q,T]=0.

Here is a direct diagonal calculation from the original binomial source rule. For K distributed Binomial(n,1/2), write X=K-n/2, D=X²+n(n-2)/4, and H=n(n-2)X²-n(n-2)/4. The ordinary exponents in the two arms have sum D and squared difference minus sum H. The elementary moments E X²=n/4 and E X⁴=(3n²-2n)/16 give

E H=n(n-1)(n-2)/4,
E(DH)=n²(n-1)(n-2)(n+1)/16.

In the coefficient a w e⁴ of the pair-normalized no-merger probability, expanding the two arms and multiplying by b2^(-binom(n,2)) gives

(H41)_nn=(1+binom(n,2)/4) E H -(1/2)E(DH)
          =n(n-1)(n-2)(4-n)/16.

Since B4=(8/3)H41 and (R3)_nn=n(n-1)(n-2)/3,

T_nn=-n(n-1)(n-2)(n+1)/6
     =-(2/3) lambda_n(lambda_n-1), lambda_n=binom(n,2).

Every operator involved preserves the current-root filtration and has a scalar unchanged-forest block at each root count. A filtration-preserving operator commuting with Q is uniquely determined by those scalar diagonal blocks: after subtracting the matching polynomial in Q, a strictly root-count-lowering commuting remainder is zero, successively across blocks with distinct eigenvalues. The eigenvalues are distinct for positive root counts n>=1. The root-zero and root-one blocks both have eigenvalue zero but remain separate: no source instruction merges one root into zero, and the operators here vanish on those blocks. Thus this coincidence creates no extra commuting remainder. Consequently

B4=(5/2)R3+(1/2)[Q,R3]-(2/3)(Q²+Q).                  (2)

This is a consequence of the exact recorded relation plus the displayed hand binomial moments, not a newly fitted identity.

## 3. The full quartic compatibility space is simpler than the earlier necessary projection

Let Rspace be the entire ordinary-conjugation span of R3, and put T2=Q²+Q. For any cap>=4, T2 is independent of Rspace: conjugation leaves the R3 diagonal fixed, while the ratios of the T2 and R3 diagonals at arities three and four differ. Equation (2) gives

Rspace+Bspace=Rspace+span{T2}.

The accepted quartic identity therefore yields

C4=a r B4-a^4[R3/32+T2/96].

Modulo Rspace this is precisely

C4 = -(2/3)(a r+a^4/64) T2  modulo Rspace.              (3)

Consider a finite leading architecture whose r-derivative columns R_(s_j) span Rspace. For example sufficiently many distinct positions with the full Vandermonde moment span have this property. At a full cubic zero, the full quartic equation is solvable by shared first r-corrections if and only if

sum_j (a_j r_j+a_j^4/64)=0.                            (4)

This is a statement about the FULL quartic vector under the explicit derivative-span premise, not merely its diagonal projection. It does not impose separate moment equations on those quartic weights at every nonzero ordinary weight.

For an adapted direction with dr_j=0 and fixed leading positions, (3) similarly gives

DF4(v)=-(1/4)(sum_j w_j da_j)T2 modulo Rspace.

Thus, under the same full cubic derivative-span premise, the previously necessary weighted-sum condition is also sufficient for that direction's full quartic compatibility. It is still not sufficient for the complete fifth-order equation.

For cap>=9, if the cubic zero has one positive and one negative r, their two a-directions can be coupled so this weighted sum is zero while the derivative of the nine-root fifth scalar is nonzero. Explicitly set da_p=w_n and da_n=-w_p. Then the derivative of Phi F5 is

168(a_p r_p p_p^30 w_n-a_n r_n p_n^30 w_p)>0.

This proves availability of a compatible local scalar-changing direction under the stated span/leading-zero premises. It does not prove that zero lies in its attainable scalar range or that all other fifth-order coordinates can be canceled. The earlier shared-kappa branch illustrates exactly why a derivative alone is insufficient.

## 4. Scope after the failed guard shortcut

The fixed P1 relation is false, and the frozen P2 computation remains unexecuted. Neither the differential guard nor a symmetric-family impossibility is established. The useful retained fact is the exact simplification of the lower correction space. The full fifth-order cone must still retain the complete source directions A5 and B5 modulo that space; no source direction is dropped to revive the rejected relation.
