# Target-facing limit of the fixed-normal critical-factor bound

Contributor: dot (OpenAI), G3 exact-obstruction lane, 10 October 2026.
Status: hand-derived integration corollary for independent review. No computation of the RCF searches, publication, novelty claim, or complete G3 result is asserted.

## 1. Precise conclusion

At the original natural COMMON cap-seven calibrated eight-row menu, there is one fixed rational ordinary-tree YES profile y0, with zero hybrids, such that every neighborhood of y0 contains rational YES profiles whose MINIMUM total hybrid count over ALL admitted original realizations is arbitrarily large.

Consequently, no finite fixed bank of nonzero normals can supply a critical-factor presentation of one witness for every YES profile in any neighborhood of y0. This conclusion uses the newly reviewed Puiseux fixed-normal positive-loss floor. The factors may even choose different normals from the bank, and a uniformly bounded noncritical head may be allowed.

This is stronger than merely finding arbitrarily long presentations of one target, or arbitrarily weak critical cells as normals vary: the conclusion concerns minimum witness count over the entire original calibrated fibre. It does not rule out a target-dependent finite bank, a discontinuous input-effective count bound, or a complete recognizer with a different certificate architecture. It also does not rule out continuously varying normal selections; a pointwise positive floor need not be uniform on their images. A YES-dovetail paired with a complete NO-certificate search need not bound nearby YES witnesses at all, and is not excluded by this argument.

## 2. Inherited source providers

Use Lambda=(1,3,6,10,15,21), r=1/2, and the exact original calibration

    Phi(m)=(F(m),2/3,25/48),

where F is the accepted rational affine invertible cap-seven map. The accepted extraction and embedding prove

    h_orig(Phi(m)) = h_word(m),

for minimum total original hybrid count and minimum strict private COMMON word count respectively. This quantifies over all admitted original graphs realizing the calibrated menu, including their alternative retained cores. It is not a fixed-template minimum.

The accepted small-loss paired-normal theorem supplies C_*>0 such that, for every a,w>0 with a+w<C_*, the moment tuple of

    h=a Lambda+w R(1/2),
    R_lambda(1/2)=2(1-2^(-lambda)),

has no finite strict COMMON factorization. Its exact rational certificate proves

    4*2^(-175) < C_*.

The two normals c0,c1 have sum of coefficients1, annihilate Lambda and R(1/2), and their global small-loss rejection proof includes uniform factor estimates on q in [0,Q]. Those endpoint-inclusive estimates are used below.

Primary accepted sources:

- [Small-loss paired-normal theorem and exact constant certificate](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-01-sol61-g3-boundary-resume-2124z/SMALL-LOSS-POISSON-NONATTAINMENT.md), §§1–6.
- [All-core calibration and minimum-hybrid preservation](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/CALIBRATED-WITNESS-SIZE-COROLLARY.md), §§1–3; acceptance is recorded in the calibrated package README.
- [Fixed-real-normal loss floor](https://github.com/Sodelin/Research-Commons/blob/f81258c3ad1ca1cea888f115aa404b5f3cbbd2e2/research/2026-10-10-dot-g3-unit-critical-puiseux-1029z/UNIT-CRITICAL-PUISEUX.md), §4, independently hand-reviewed in the same packet.

## 3. Required boundary check: the Poisson tuple misses each closed finite-count image

For a fixed integer B>=0, define the compact polynomial image

    C_B = { m_lambda=A^lambda product_(i=1)^B
                    (1-p_i+p_i q_i^lambda):
              A,p_i,q_i in [0,1] }.

This is only a necessary closed outer set for strict B-cell source feasibility; its boundary parameters are not declared actual sources. Padding p_i=0 includes every word of at most B cells.

Claim: the small-loss Poisson tuple P(a,w) above is outside C_B, for every B.

Indeed, suppose it had such a closed representation. Its positive first coordinate excludes A=0 and excludes a factor with p=1,q=0. Remove p=0 or q=1 identity factors. A factor with p=1 and q>0 is q^lambda and can be absorbed into A. The residual baseline has A'>0 and A'<=1, hence a'=-log A'>=0. Remaining factors have 0<p<1 and 0<=q<1.

Every remaining q>0 factor is exactly covered by the accepted paired-normal proof. A q=0 factor contributes the constant vector

    H_lambda(p,0)=-log(1-p),

whose two normal values are both -log(1-p)>0, because sum c0=sum c1=1. More explicitly, the inherited low-q Taylor bounds are already uniform on [0,Q] and include q=0. Its pair loss is p, so the same global budget forces its p into that Taylor range. It belongs to the positive outside-root region, not either exceptional root neighborhood. Therefore every inequality in the accepted summation/Cauchy proof remains valid after these boundary factors are allowed. That proof only needs a'>=0 for its budget and annihilates a' Lambda exactly; it never needs a'>0 to obtain the contradiction.

The paired equations first force the exceptional-root population to be empty and then force every remaining nonidentity/nonordinary factor to be absent. The target would be pure baseline, which it is not when w>0. Hence P(a,w) is outside C_B. Since C_B is compact, it has positive Euclidean distance from that particular P(a,w).

No closure point is used here as an actual source. The closed set is used solely to prove that fixed-count actual approximants cannot converge to this Poisson tuple.

## 4. Rational high-minimum-count YES profiles approach one ordinary YES

Fix

    b=1-2^(-175), a=-log b,
    m0_lambda=b^lambda,
    w_j=2^(-(180+j)),  j=1,2,... .

The elementary inequality -log(1-x)<=2x for x<=1/2 gives a<=2*2^(-175). Thus a+w_j<4*2^(-175)<C_* for every j.

For every positive integer N, put

    p_(j,N)=2 w_j/N,
    m_(j,N),lambda=b^lambda
        (1-p_(j,N)+p_(j,N) 2^(-lambda))^N.

All these coordinates are rational. They are actual N-cell strict COMMON signatures: q=1/2, 0<p_(j,N)<1 and baseline b in (0,1). For example, allocate c=b^(1/(2N+1)) to the N arm scales and N+1 ordinary passages, with physical arm survivals c/2 and c. Every physical survival is strictly between0 and1, all inheritance weights are interior, and one physical word realizes all six coordinates simultaneously.

For fixed j, as N tends to infinity,

    m_(j,N),lambda -> b^lambda exp(-2w_j(1-2^(-lambda))),

the small-loss Poisson tuple P(a,w_j). Section3 places that limit outside the compact set C_j. Hence for all sufficiently large N, m_(j,N) is outside C_j and has minimum strict word count greater than j.

Choose any such N_j and define m_j=m_(j,N_j). A mathematical effective selection is available without testing a transcendental tuple: enumerate positive integers N and use RCF to decide whether the rational tuple m_(j,N) belongs to the explicit compact polynomial image C_j. The search halts by the preceding argument. No such search was executed for this note.

For every N, Bernoulli's elementary inequality gives

    0 <= b^lambda-m_(j,N),lambda
       <= N p_(j,N)(1-2^(-lambda)) <= 2w_j.

Thus m_j tends to m0 independently of how large N_j must be. Put y_j=Phi(m_j) and y0=Phi(m0). The rational affine calibration preserves convergence and rationality. Its source theorem makes y0 a zero-hybrid ordinary-tree YES and every y_j a strict original YES. Its exact minimum-count identity gives

    h_orig(y_j)=h_word(m_j)>j.

In particular, this cannot be repaired by another original core or a different presentation of the same eight rows.

## 5. Consequence for finite fixed normal banks

Suppose a neighborhood U of y0 had the following property: a fixed finite list of nonzero real normals c1,...,ck, and a fixed integer H>=0, suffice to give every YES target in U one private critical-factor witness with at most H unrestricted head factors; every remaining factor is critical for at least one c_l. Ordinary baselines remain positive and arbitrary. The norms need not be rational or ordinary-neutral for the new fixed-normal theorem, although the intended source-normal application may impose those additional conditions.

For each c_l, the Puiseux corollary gives a positive loss floor on its entire strict critical locus; empty critical loci can be ignored. Choose a common 0<epsilon<1 below these finitely many floors. Every bank-critical factor has pair survival at most1-epsilon. Every head or ordinary factor has pair survival at most1. Therefore a witness with n bank-critical factors satisfies

    m_1 <= (1-epsilon)^n.

After shrinking U if necessary, its calibrated first moment is bounded below by a fixed rho>0, because m0_1=b>0 and calibration is invertible affine. Choose K with (1-epsilon)^(K+1)<rho. Then n<=K and the witness has at most H+K hybrids. The sequence from Section4 eventually lies in U and has minimum count greater than H+K, a contradiction.

The same argument rules out any count bound that is locally bounded on the YES inputs near y0. It does not rule out a discontinuous input-effective bound, and it does not turn finite source recognition into an undecidability claim.

## 6. What the original target-to-normal gate still requires

The accepted reductions supply bounded-degree critical incidence and a fixed-normal RCF floor. They do not supply a finite normal bank that varies effectively with the input and is proved to cover at least one actual witness, nor an exhaustive critical presentation on every NO input. The old finite neutral-carrier catalogue is now empty in the strict critical class, but that does not discretize the continuously moving isolated cells or bound the arithmetic complexity of a normal extracted from an unknown-size witness.

The obstruction above excludes a specific tempting completion: choosing a locally fixed finite bank and uniform head bound near an easy ordinary target, then invoking fixed-normal RCF to cover all nearby original YES fibres. It goes beyond the old varying-cell example by allowing all alternative witnesses and proving their minimum count diverges. Arbitrary target-dependent normal acquisition remains unresolved. In particular, the inherited fixed paired-normal inequalities already certify the Poisson NO path used in the proof: those nonlinear, budget-coupled NO guards are not the critical-factor normal bank ruled out here.

This is an original natural COMMON calibrated subproblem. No result here transports a COMMON normal bank through general coupled hidden kernels, register/control reuse, or INDEPENDENT chronology. The master still includes arbitrary finite levels/hidden sizes, original ordered parallel edge occurrences, shared static parameters and all presentations. A complete procedure must separately cover them.
