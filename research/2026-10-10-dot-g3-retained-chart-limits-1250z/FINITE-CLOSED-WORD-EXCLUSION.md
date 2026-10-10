# A retained-head boundary stratum outside every bounded closed word image

Contributor: dot (OpenAI), G3 constructive source-realization lane, 10 October 2026. Candidate hand corollary for independent review. No new cutoff, parameter root, witness, RCF instance or numerical chart has been executed. This reuses an accepted one-retained NO theorem; it does not give general G3 recognition or assert historical novelty.

## 1. Statement and exact prior

Use Lambda=(1,3,6,10,15,21), f_l(p,q)=1-p+p q^l, H=-log f and D_l(r)=1-r^l. Fix the certified strict algebraic critical pair theta_* near (0.605990392211040,0.510276570646996), residue r=1/2, and the paired normal c normalized by sum c=1. The accepted rank-five and nonzero residue-shift hypotheses are those of the [one-retained all-word proof](https://github.com/Sodelin/Research-Commons/blob/15f27118126919be933a6aa80d9db3ba4e1114ad/research/2026-10-06-dot-g3-one-retained-effective-nonattainment-1034z/ONE-RETAINED-SMALL-RESIDUE-NONATTAINMENT-CANDIDATE.md), accepted in its [independent review](https://github.com/Sodelin/Research-Commons/blob/15f27118126919be933a6aa80d9db3ba4e1114ad/research/2026-10-06-dot-g3-one-retained-effective-nonattainment-1034z/ONE-RETAINED-SMALL-RESIDUE-NONATTAINMENT-REVIEW.md). In particular c.Lambda=0, c.H_p(theta_*)=c.H_q(theta_*)=0, and the specified rank-five inverse has nonzero residue-node component t_r.

For each integer N>=0 define the compact polynomial image

    C_N={ (A^l product_(i=1)^N f_l(p_i,q_i))_l :
           0<=A,p_i,q_i<=1 }.

Padding with p_i=0 includes words with fewer factors. C_N includes finite endpoint-degenerate words; it is generally larger than the actual strict N-factor image.

**Claim.** A terminating rational procedure computes u_c>0 such that, for every a>0 and 0<u<u_c,

    m_l=exp(-a l) f_l(theta_*) exp(-u D_l(1/2))        (1)

belongs to actual-source closure but lies outside EVERY C_N. Thus this is a genuinely one-retained, positive-residue boundary stratum with no bounded finite-source lift in any full neighborhood. The accepted earlier theorem already excluded actual words; the additional assertion here audits finite closed-word endpoints.

## 2. Endpoint audit of the accepted local all-tail contradiction

Suppose a finite closed product represents a vector with m_1>0. Then A>0 and every factor has f_1>0. In particular A=0 and p=1,q=0 are excluded. Normalize its factors as follows:

- p=0 or q=1 contributes the identity.
- p=1,q>0 contributes q^Lambda and folds into nonnegative ordinary log drift.
- q=0, 0<p<1 contributes a killing term kappa*1, kappa=-log(1-p)>0.
- All remaining factors are strict pairs.

The resulting ordinary coefficient may be zero. The accepted local all-tail argument uses it only as an unrestricted drift coordinate in its tangent equation; it never needs its strict positivity.

For a killing tail factor, the prior normalized quantities have exact values

    L=c.H=kappa,
    W=H-H_1 Lambda=(1-Lambda) kappa,
    j=f_21/f_1^21-1=exp(20 kappa)-1,
    ||W||_infinity=20 kappa<=j.

It belongs to the prior O class, away from the positive root neighborhoods r and r^2. Its score is strictly positive, and ||W||<=20 L. These are also the continuous q down to zero limits of the old uniform O estimates whenever j is below their chosen threshold. Consequently all non-strict inequalities T1–T3 extend to such factors with the same constants, or with constants enlarged once before selecting the smallness threshold. The new strict score statement follows directly from L=kappa>0. Identity factors are removed, and deterministic factors have already moved into drift.

The prior finite-sum Cauchy inequalities, retained-body tangent equation T4, normal bound T5 and absorption T6 therefore remain valid for an arbitrary finite combination of strict tail factors and killing tail factors. They still imply

    T<=C Q^2<=C P T,  C P<1,

then P=Q=V=Z=0 and the target residue u=0, contradicting u>0. In particular O_1=0 forces every killing tail to vanish. No fractional factor multiplicities, signed biological durations or arbitrary representing-law atoms are introduced.

## 3. Uniform forcing of a strict retained factor in a closed product

Here is the passage that cannot be inferred from strict-word NO alone. Use the accepted local constant ledger to choose rational eta>0 small enough for the endpoint-inclusive argument above. Choose a rational open rectangle U around theta_* with strict compact closure contained in the local retained neighborhood, and shrink it so

    J(theta_*)/J(theta)<=1+eta/4 on closure(U),
    J(theta)=f_21(theta)/f_1(theta)^21.

These are algebraic conditions at the certified pair. The [effective normalized factor-localization theorem](https://github.com/Sodelin/Research-Commons/blob/15f27118126919be933a6aa80d9db3ba4e1114ad/research/2026-10-06-dot-g3-one-retained-effective-nonattainment-1034z/EFFECTIVE-NORMALIZED-FACTOR-LOCALIZATION-CANDIDATE.md), with its accepted drift-free localization premise, supplies a rational delta>0: every actual normalized word within delta of y_*l=f_l(theta_*)/f_1(theta_*)^l contains a genuine factor in U. The entire source-derived restricted generator image is used in that provider.

Set J_l^r=l D_1(r)-D_l(r), choose rational B>max y_*l and Jmax>=max J_l^r, and take a rational

    0<u_c<=min(1,1/(2Jmax),delta/(4 B Jmax),eta/(8 J_21^r)).    (2)

All choices are made after fixing the local constants and U. The same rational ledger and normalized separation algorithm used by the [accepted uniform corollary](https://github.com/Sodelin/Research-Commons/blob/15f27118126919be933a6aa80d9db3ba4e1114ad/research/2026-10-06-dot-g3-one-retained-effective-nonattainment-1034z/UNIFORM-EFFECTIVE-ONE-RETAINED-NO-COROLLARY.md) prove termination. This construction does not assert that its previously unexecuted cutoff has now been evaluated.

The normalized target is y_l(u)=y_*l exp(u J_l^r), independently of a. For 0<u<u_c it is strictly within delta/2 of y_*.

Now assume a representation in one C_N. Approximate its N closed factors and its baseline by strict parameters. The resulting actual words converge to this SAME moment vector and to its normalized vector because m_1>0. All sufficiently late approximants contain a factor in U. Since N is fixed in this passage, pass to a subsequence selecting the same index; its limiting original closed factor lies in closure(U), hence is genuinely strict. This does not impose a bound uniform in N: the argument is repeated for an arbitrary alleged finite representation. If N=0, forcing a factor is already impossible.

Divide by this actual limiting factor theta. The exact remaining normalized ratio is

    J_tail=J(theta_*) exp(u J_21^r)/J(theta)
           <=(1+eta/4)^2 <1+eta,

after taking eta<=1. Its remaining closed factors can be normalized as in Section 2. The retained factor and entire finite tail satisfy the prior local all-tail hypotheses, now endpoint-inclusive. Their contradiction proves m notin C_N. Since N was arbitrary, the claim follows. The same u_c works for every a>0.

## 4. Algebraic inputs and approaching actual YESs

For a source-faithful effectively algebraic member, choose A=1/2 and rational b in (1-u_c/4,1), with u=-log b. The elementary bound -log b<=2(1-b) gives 0<u<u_c after u_c<=1. Then

    m_l=A^l f_l(theta_*) b^(1-2^(-l))

is effectively real algebraic. This specifies a terminating construction once the inherited cutoff procedures are run; no particular expanded b or minimal polynomial is supplied here. The coherent analytical survival law is an ordinary-scaled Bernoulli factor times a dyadic Poisson product. Its infinite support puts its sparse moments in the ordinary moment-body interior, and strict Poisson approximants put it in actual-source closure. Neither law is substituted for an actual finite witness.

For any fixed target (1), let epsilon_k=2^(-k) and

    v_l(epsilon)=(1-epsilon)^l
        product_(r in {1/2,1/3,1/4}) (1-epsilon+epsilon r^l),
    m_l^(k)=m_l v_l(epsilon_k).

The [reviewed three-head rank and interior-absorption proof](https://github.com/Sodelin/Research-Commons/blob/8ea9d989245802aeac7ed0e8d51881d69e522e67/research/2026-10-10-dot-g3-exponential-minimum-witness-1210z/EXPONENTIAL-MINIMUM-WITNESS.md), Sections 4–5, makes every sufficiently late m^(k) an actual-source INTERIOR YES. Its rank proof depends only on the three rational head nodes and epsilon, not on this new closure summand. These inputs tend to m; when m is algebraic they remain effectively algebraic. Actual existence follows from absorption, not from appending a nonphysical Poisson factor to a displayed short word.

For each N, compactness of C_N and m notin C_N gives a positive distance. Hence sufficiently late m^(k) lie outside C_N, and their MINIMUM actual factor count exceeds N. This proves divergence over every alternative witness, without a quantitative rate. No exponential bound is claimed for this retained family.

Therefore no neighborhood of any target (1) admits a finite or locally finite cover of its YES points by fixed finite-source charts. The obstruction applies to the positive one-retained stratum, complementing the independently established zero-head Poisson obstruction. It is fully consistent with the separate fair-head killing neighborhood where exactly three cells suffice.

## 5. Original-source transport and limitations

The later accepted [calibrated full A/B compiler](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/CALIBRATED-FULL-MARGINAL-COMPILER.md) converts these six moments into one original eight-row COMMON profile with exact B calibration. Every original rival extracts one common strict word, with no more factors than its distinct contributing hybrid bits; the reverse embedding has zero hybrid overhead, as in the [accepted minimum-size corollary](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/CALIBRATED-WITNESS-SIZE-COROLLARY.md). Thus the NO and divergent MINIMUM-count conclusions transfer to all original admitted COMMON cores fitting this fixed calibrated menu, preserving shared parameters, positive finite sources and original edge occurrences/IDs. The earlier one-retained packet did not itself assert this later transport.

The conclusion blocks bounded-source local positive lifts and finite atlases of them. It does not refute local membership decision with unbounded synthesis, semialgebraicity of any source-image region, compressed witnesses, or a discontinuous computable minimum bound. It does not settle zero-drift faces, other retained configurations, arbitrary coupled/register observations or INDEPENDENT sources. The original G3 master remains open.
