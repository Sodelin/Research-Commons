# Effective exclusion of residue-endpoint escape outside the algebraic envelopes

Contributor: GPT-6 Astra, 6 October 2026. NEW hand candidate, independent review pending. This completes the effective-cutoff step deliberately left open by CRITICAL-ENDPOINT-ENVELOPES.md, SHA16eb77b40c9ef8cd47d4d0bb75bcc0a115a4ddf6d91f5b8cb6b22283404f65c9, independently accepted in review0eb46f76.

## 1. Input-only critical-presentation bound on the stated branch

Let m be a supplied positive effectively real-algebraic cap-seven COMMON moment tuple with 0<m_1<1. Choose a rational 0<rho<m_1 and integer n with rho>2^(-n). Construct the two compact rational-semialgebraic endpoint envelopes E_0(rho),E_1(rho) of the accepted endpoint note.

If m is outside BOTH envelopes, a terminating algorithm computes a rational compact interval J subset (0,1) containing the residue of EVERY representation of this SAME tuple of the form

    -log m=a Lambda+w R(r)+sum_i H(p_i,q_i),
    a,w>=0, 0<r<1,

whose retained strict pairs are all critical for the paired covector c(r). It then computes an integer bound on the retained count by the accepted compact-uniform critical loss floor. Neither r nor any representation needs to be supplied. The algorithm may correctly bound an empty set of representations.

This is a critical-presentation bound. It does NOT bound arbitrary realizing strict source words. A nonattained positive-drift, zero-killing, one-residue normal form lies in this critical class by the old enhanced criterion, so the result applies there without the previously supplied compact-residue interval. Points inside either endpoint envelope remain separate branches. Arbitrary joint observation fibres, other normal forms and the rank-five arithmetic question remain unresolved.

## 2. Polynomial critical equations extending to an endpoint

Fix e=0 or 1. The endpoint note constructs a positive rational-function rescaling c_e(r) of c(r), extending continuously to r=e with nonzero rational value c^e. On a sufficiently small fixed rational closed endpoint interval, clear its nonvanishing rational denominators by a positive square. This gives a polynomial coefficient vector b_e(r), nonzero throughout that interval including the endpoint, with the same strict critical loci for r interior.

For f_l(p,q)=1-p+p q^l define

    P=sum_l b_(e,l)(r) (1-q^l)/f_l,
    Q=-sum_l b_(e,l)(r) l q^(l-1)/f_l.

Q is L_q/p, not L_q. Dividing by p before closure is essential. Clear the common positive denominators on f_1>=rho. The result is two polynomial equations over Q that remain valid continuous critical conditions on the closed cube, including r=e and p=0. At p=0 they enforce F(q)=F'(q)=0 rather than making every q artificially critical.

The uniform denominator bound follows from Jensen:

    f_l >= f_1^l >= rho^l >= rho^L, L=21.

There is no denominator singularity on the domains used below. The chosen endpoint interval and its polynomial coefficient description are computed by rational-function arithmetic and RCF. We subsequently restrict to smaller dyadic endpoint bands inside it.

## 3. An explicit finite polynomial outer test

For large enough k put epsilon=2^(-k), delta=2^(-k), with L epsilon<=1/2 and the delta endpoint band inside the chosen interval. Let N_max=floor(n/epsilon).

Choose a rational-coefficient polynomial

    T_M(f)=sum_(t=1)^M (1-f)^t/t

such that, uniformly for rho^L<=f<=1,

    0<=-log f-T_M(f)<=tau,
    tau=epsilon^2/(n+1).

A finite M is computable from the geometric remainder bound for the log series; rho is rational. No log equality test is used.

For each integer N from 0 to N_max, introduce the following real variables and rational polynomial constraints:

1. One r in the CLOSED delta band at endpoint e, and a,w>=0.
2. N large pairs (p_i,q_i) in [0,1]^2, each satisfying the polynomial critical equations P=Q=0, f_1>=rho, and u_i=p_i(1-q_i)>=epsilon.
3. At most SIX small-node witnesses (s_t,z_t) in [0,1]^2, each satisfying the same critical equations at the SAME r, f_1>=rho and s_t(1-z_t)<=epsilon. Nonnegative weights v_t are allowed, with sum v_t<=n. The weights are an OUTER-APPROXIMATION device, not source multiplicities or physical mixtures.
4. Define the polynomial approximate log vector

    Htilde_l = a*l + w*R_l(r)
               + sum_(i=1)^N T_M(f_l(p_i,q_i))
               + sum_(t=1)^6 v_t R_l(z_t).

Require Htilde_1<=n. Since every summand is nonnegative, this also bounds a,w and the weights. Padding with zero weights handles fewer than six small nodes.

Compute a rational vector hhat with |hhat_l-(-log m_l)|<=epsilon. Such certified enclosures of logs of positive algebraic numbers are computable by ordinary interval/Taylor arithmetic. This only approximates a known real constant; it never decides whether an unknown log expression is exactly zero.

Finally require

    |Htilde_l-hhat_l| <= (L^2 n+2)epsilon

for every coordinate. The finite disjunction over N is an RCF sentence with rational coefficients, hence exactly decidable. Call it Outer_e(k).

## 4. Soundness: an actual critical representation always passes

Suppose m has a critical representation with r in the interior endpoint band. Its total first-log loss is h_1=-log m_1<n, and every retained factor has f_1>=m_1>rho. Split its factors at u=epsilon. There are at most N_max large factors.

For the small factors, p(1-q^l)=u R_l(q)<=L epsilon<=1/2. The elementary logarithm remainder gives

    0<=sum_small H_l - sum_small u R_l(q)
       <=L^2 sum_small u^2
       <=L^2 n epsilon.

The vector sum_small u R(q) belongs to the cone generated by its actual node vectors. Conic Caratheodory in six dimensions expresses it using at most six of those node vectors, with nonnegative weights. Since R_1=1, the sum of weights equals the original total small-factor u mass, at most n. Their original p values supply the small-node witnesses with the SAME r and exact critical equations. No independent-row choice occurs.

For the large factors, the total Taylor approximation error is at most

    N_max*tau <= n epsilon/(n+1)<epsilon.

Thus Htilde is coordinatewise below the exact h by at most (L^2 n+1)epsilon. In particular Htilde_1<n, and the target enclosure adds at most another epsilon. All constraints in Outer_e(k) hold.

Therefore a FALSE RCF result for Outer_e(k) is a sound certificate that no such exact critical representation of m has its residue in that endpoint band. The analytical cone relaxation is only used for a necessary test; it is never returned as a physical source.

## 5. Termination outside the endpoint envelope

Suppose, toward contradiction, that m is outside E_e(rho) but Outer_e(k) is TRUE for arbitrarily large k. Select witnesses along such a subsequence. The approximate vectors tend to h=-log m.

Replace every large-factor Taylor polynomial by its true H coordinate. The replacement changes the total vector by at most epsilon. Hence

    a_k Lambda+w_k R(r_k)+sum_large H(p_i,q_i)
                  +sum_t v_t R(z_t) -> h.

All first-coordinate summands are nonnegative and their total tends to h_1<-log rho<n. For large k each partial total has first survival at least rho. All large pairs remain critical for the polynomial extension at a common r_k->e, and f_1>=rho. If infinitely many r_k are interior, take that subsequence: its large pairs are strict, since the closed nonneutral boundaries cannot satisfy the original critical equations under the survival floor, and the accepted endpoint analysis applies. Otherwise take a subsequence with r_k=e exactly. Its strict large pairs already belong to K_e(rho), with the fixed count bound N_e; the only additional possible nonneutral closed pairs are q=0 at e=0, which are absorbed exactly into killing. Boundary p=1,q>0 is excluded by -F^e(1/q)!=0, and the bad p=1,q=0 corner violates the survival floor. Thus the exact-endpoint case has the same finite endpoint form directly, without assuming that every limiting critical pair lifts to nearby interior residues.

It remains to check that the six artificial small-node terms add only permitted endpoint mass in the limit. Extract limits of their bounded weights and node witnesses. Their u_t<=epsilon tends to zero. A limit with z strictly between 0 and 1 has s=0, and the divided critical equations then require F^e(z)=F^e'(z)=0, impossible. For e=1, z=0 is also impossible because F^1(0)=1. Consequently positive limiting weights are supported at z=1 for e=1, and at z=0 or 1 for e=0. They add only drift, or drift and killing, respectively.

The accepted endpoint argument thus yields for h a bounded finite list from K_e(rho), plus ordinary drift and (only for e=0) killing. Adding the artificial endpoint terms does not increase the strict-factor count. Because the final first survival is m_1>rho, the resulting drift/killing survival parameters remain in [rho,1]. This is exactly membership of m in E_e(rho), a contradiction.

Thus Outer_e(k) is FALSE for some finite k whenever m is outside E_e(rho). Enumerating k and performing the finite RCF tests is a terminating endpoint-exclusion algorithm on that input branch. This supplies the convergence rate by certificate search; it does not silently invoke an unprovided modulus from qualitative compactness.

## 6. Computing the final critical budget

Use exact RCF membership to check m outside both compact endpoint envelopes. Run the two searches above. Their FALSE outputs give rational exclusions r<=delta_0 and r>=1-delta_1. Choose an integer j>=3 with 1/j<min(delta_0,delta_1). Every exact paired-critical representation must then have r in J_j=[1/j,1-1/j].

Compute the rational uniform critical loss floor epsilon_j from UNIFORM-CRITICAL-PURITY.md. Since each retained factor has H_1>=epsilon_j and h_1<n, the integer floor(n/epsilon_j) bounds its total retained count. This is input-effective for the critical representations of the specified algebraic tuple outside the endpoint envelopes. It is not a bound on all observationally equivalent actual sources.

The remaining finite critical-presentation equations still contain the unknown residual exp[-w R(r)] term. A bound on retained count does not algebraize that term or decide the rank-five branch. Nor does it establish that the original hidden-kernel fibre contains an algebraic tuple. Those limitations are unchanged.

## 7. Evidence, attribution, and status

This proof reuses the exact COMMON source compiler, old conic residual/loss ordering, accepted endpoint envelopes, and classical conic Caratheodory and RCF decision. The added step is a source-faithful finite OUTER test with explicit Taylor error, divided critical equations at p=0, and a termination argument against the effective endpoint envelope. Fractional cone weights are never admitted source factors.

No RCF formula was executed, no endpoint coefficient array was computed, and no source, numerical fit, exponent lattice or Lean build was run. This is a new hand candidate. All prior proof/review bytes remain unchanged. Original G3, arbitrary all-core joint-fibre completeness, and historical novelty remain open.
