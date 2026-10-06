# Fixed-pair arithmetic refinement for a complete joint protected-core fibre

Contributor: dot (OpenAI), 6 October 2026. Stronger working hand proof, preserving the earlier `WORKING-PROOF.md` e24f4aadf2ff87cbea97eb812df2a99f8b37dbd4a0828d5d377d4711acb755fb unchanged. No execution.

## 1. Conclusion and exact limitations

Use the earlier prime-radical COMMON targets

    K(q,ell)_lambda=b^[lambda+R_lambda(1/q)],
    b=1−1/ell,    Lambda={1,3,6,10,15,21},

where q and ell are prime and ell is large enough for the accepted all-fixed-residue small-loss nonattainment theorem. The condition ell≥q² is no longer needed below. These targets remain algebraic, full-kernel actual-closure points outside the physical COMMON word image.

Let T be ANY fixed semialgebraic predicate over a real number field F in the six moment coordinates, with a quantifier-free polynomial presentation of maximum degree D. If q>max(D,[F:Q]), then

    K(q,ell) in T  implies  T contains an actual strict COMMON kernel.

The actual alternative can be chosen with the SAME pair moment b². There is no exceptional-pair set in this refinement. Hence a negative target set contains no such prime-radical target with q above this input-effective bound.

For finitely many genuinely fresh independent COMMON slots, the same implication holds jointly if their primes q_i are pairwise distinct and each exceeds max(D,[F:Q]). The alternative uses one physical word per slot and satisfies the ENTIRE joint predicate. Source-level cross-slot parameter ties, exposed shared routing registers inside the slots, or paired-mechanism tuples are not covered. Repeated uses of a single kernel are kept as one variable, not replaced by independently selected slots.

## 2. Source-faithful approximants on an exact pair slice

Fix b,r with 0<b,r<1. For sufficiently large integer n set

    p_n=(1−b^(1/n))/(1−r),
    u_n=b^(1/(2n+1)).

Then 0<p_n<1. The actual strict COMMON word

    W_n=E(u_n) product_(i=1..n) [B(u_n,u_n r,1−p_n) E(u_n)]

has the same physical parameters across every forest coordinate. Its leading population, arm scales and connectors are all strictly positive and finite. In normalized moments it is

    (W_n)_lambda=b^lambda[1−p_n+p_n r^lambda]^n.

At lambda=1 the bracket equals b^(1/n), so

    (W_n)_1=b² EXACTLY for every n.

Moreover n p_n tends to (−log b)/(1−r), and therefore every moment tends to b^[lambda+R_lambda(r)]. The finite affine spectral compiler gives convergence of the whole capped labelled forest kernel. All parameters are algebraic when b,r are algebraic. This is the ordinary binomial/Poisson approximation with exact pair calibration; no word-length bound, hidden preparation or negative population is used.

Consequently K(q,ell) is in the closure of ACTUAL source kernels inside the affine slice m_1=b², not merely in the unconstrained source closure.

## 3. Arithmetic local constancy on that slice

The earlier exact field proof gives t=b^(1/q^20) with [F(t):F]=q^20 when q is prime and exceeds [F:Q]. For an atom P of degree at most D<q, decompose

    P=sum_alpha P_alpha(m_1) prod_(lambda≥3)m_lambda^(alpha_lambda).

The higher-coordinate monomials have distinct exponent residues modulo q^20. Thus, after substituting the RATIONAL value m_1=b², either every P_alpha(b²) vanishes and the atom is identically zero on the slice, or P(K(q,ell)) is nonzero. This follows from one radical power basis, with one coherent target tuple.

Atoms identically zero on the slice have constant truth values there. Every other atom has a locally constant sign at K. The complete Boolean predicate therefore has locally constant truth value on this affine slice. If T contains K, it contains a relative neighborhood of K on the slice. The exact-pair W_n eventually lie in that neighborhood, so T contains an actual word. This proves Section 1 without root exceptions or a lower pair-moment margin.

This is not an invariance assertion for the fixed-pair slice: appends normally decrease the pair moment. The argument uses complete source words W_n whose endpoint pairs are calibrated exactly.

## 4. Several slots under one joint algebraic formula

Let there be s genuinely fresh independent slots. Set n_i=q_i^20 and t_i=b_i^(1/n_i), with pairwise distinct primes q_i>max(D,[F:Q]). Eisenstein gives [Q(t_i):Q]=n_i. Inductively,

    [F(t_1,...,t_i):Q]=[F:Q] product_(j≤i)n_j,

because n_i is coprime to the preceding degree and the tower argument forces its full degree. Products of the individual power bases consequently form a basis over F.

View any degree-D atom in all slot variables as a polynomial in the five higher moments of every slot, with coefficients polynomial in the s pair variables. Fix those pair variables to beta_i=b_i², all rational. Distinct joint higher-coordinate monomials give distinct exponent-residue tuples, by the earlier per-slot argument. Hence a specialized atom is either identically zero on the PRODUCT of fixed-pair slices or nonzero at the joint target tuple.

The complete joint predicate is locally constant there. If it contains the tuple, it contains a relative neighborhood. Choose the exact-pair physical approximants from Section 2 simultaneously in all s slots. The number of slots is finite, so their joint tuple eventually lies in this neighborhood. This yields actual source words satisfying the entire predicate at once.

This step uses the genuine product source grammar of fresh slots only. It does not replace an originally correlated or tied source domain by a product, and it does not choose different approximants for different observation rows. Coupling in the OBSERVATION polynomial is unrestricted; coupling in the SOURCE generation is the stated restriction.

## 5. Original joint compiler consequence and constructive witness search

For a finite protected core retain its full shared static parameter tuple theta, exact legal domain D_c, all registers outside the fresh slots, and its one compiler F_c(theta,K_1,...,K_s). Project the complete algebraic target equations with theta by RCF:

    T_p={ (K_i): exists theta in D_c,
                    F_c(theta,K_1,...,K_s)=p }.

All coordinates of p and all declared static coefficients are algebraic, so the projected formula is over a computable real number field. Compute its actual finite polynomial degree D. Under Section 4's prime conditions, membership of the coherent closure tuple implies an actual tuple of words in T_p. The projected formula supplies ONE compatible theta, and original core reconstruction supplies ONE legal source satisfying every supplied response row. No source is inferred from individually attainable marginals.

A concrete terminating witness procedure is available in this branch. Enumerate sufficiently large n (or joint n_i) in the explicit pair-exact approximants and decide the entire static feasibility sentence F_c(theta,W_(i,n))=p with theta in D_c by RCF. The relative-neighborhood proof guarantees success eventually. Recover an algebraic theta and the actual finite source. No numerical running time or executed word count is reported.

For one fresh slot, a negative original fibre cannot contain any member of this family with prime q>max(D,[F:Q]). For several fresh slots the established conclusion excludes tuples whose primes are all above that bound and pairwise distinct. It does not independently bound every prime when some slots fall outside those conditions, nor does it decide all remaining critical explanations.

## 6. What is inherited and what remains open

The exact target nonattainment, full COMMON spectral compiler, original joint protected-core compiler, Eisenstein criterion, degree tower law and RCF are inherited or classical. The arithmetic residue calculation is proved in the preserved companion note. The refinement here is the exact pair calibration and its use to obtain local constancy on a physically approximable joint slice.

This is a source-specific input-arithmetic consequence for the stated hard family. It shows concretely why a cap-only separator-degree obstruction does not become an obstruction to every input-dependent budget. It does not extract all unknown residues or retained factors, provide a general witness-size bound, handle genuinely coupled unbounded slots, or close original G3. No numerical, symbolic, number-field or QE computation was run.
