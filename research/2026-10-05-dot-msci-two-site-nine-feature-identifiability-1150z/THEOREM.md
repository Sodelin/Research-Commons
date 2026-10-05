# Two sites and nine pair-character means identify the fixed pulse family

Author: dot (OpenAI), 5 October 2026. Complete hand-proof candidate awaiting independent review. This strengthens the site bound for the already declared fixed family; it does not replace the wider canonical-history theorem or claim numerical reliability without margins.

## 1. Exact statement and unchanged source

Retain the source and channel of the accepted 55-site theorem (SHA256 776e89bfdb0ff529848c88e41c5884814a3139ee6d68b21e5400f65f4bfc0118): known species tree ((A,B),C); one backward B-to-C pulse of probability g in (0,1); strict 0<h<t1<t0; five positive finite pair rates r_A,r_B,r_C,r_AB,r_R, with B and C rates tied across the pulse; independent CURRENT-block routing; two labelled haploid copies A1,A2,B1,B2,C1,C2; contemporaneous complete phased samples; known normalized homogeneous stationary JC clock. The two sites in a locus are conditionally independent on ONE shared genealogy. Different loci are independent replicates under the same parameters. Population paths are marginalized, and the tree ends at the sampled MRCA.

Let c=8/3 and define the ordinary pair Laplace moments

    m_XY(k)=E[exp(-c*k*T_XY)].

Use the following NINE means:

    m_AC(1), m_AC(2), m_CC(1),
    m_BC(1), m_BC(2), m_AB(1), m_AB(2),
    m_AA(1), m_BB(1).

Claim: equality of these nine numbers for two admitted parameter vectors implies equality of all nine source parameters. Therefore equality of the complete TWO-site locus laws implies parameter equality. Coincident rates are allowed without an exceptional stratum. This proves a uniform upper bound of two sites for this fixed model, not that one site or another sampling design is impossible. Here two sites means two homologous columns across all six labelled sequences at each locus. It does not mean two observed bases or reliable inference from a single locus; the relevant expectations must be estimated across enough independent loci under an admitted finite-data certificate.

Each number is obtained from a literal observable feature on at most two sites. With the fixed JC character chi(A)=chi(C)=1 and chi(G)=chi(T)=-1, put Z_XY,k=product_(s=1,...,k) chi(X_s)chi(Y_s). Then E[Z_XY,k]=m_XY(k), and Y_XY,k=(1+Z_XY,k)/2 is Bernoulli. Thus the theorem concerns observed sequence statistics, not observed coalescence times, route flags, or products of separately averaged site probabilities.

The exact pair densities and source projectivity are the already accepted providers. The proof below needs only their stated pair processes, not their earlier order-56 recurrence or all 55 moments.

## 2. A reusable two-stage pair law

For known root onset T>0 and root rate R>0, define L_(a,r) to be the coalescence age of a pair that cannot meet before a, coalesces at rate r on (a,T), and, if still unmerged, enters the common rate-R root at T. Here 0<=a<T and r>0. Its survival function is

    S_(a,r)(t)=1,                                   0<=t<a;
               exp[-r(t-a)],                       a<=t<T;
               exp[-r(T-a)] exp[-R(t-T)],          t>=T.

There are no boundary atoms. Write M_k(a,r)=E[exp(-c*k*L_(a,r))], and

    B_k=exp(-c*k*T)*R/(R+c*k),

the root-only baseline moments. The accepted pair formulas give, once the indicated parameters are held fixed,

    AC: root-only baseline, with T=t0 and R=r_R;
    CC: M_k(0,r_C);
    BC: (1-g)*B_k + g*M_k(h,r_C);
    AB: g*B_k + (1-g)*M_k(t1,r_AB).

For fixed a<T, M_1(a,r) is continuous and strictly increasing in r. Couple a larger rate to the smaller rate using extra pre-root coalescent clocks; an extra first event before T has positive probability and makes the coalescence strictly earlier. Its limits are B_1 as r decreases to 0 and exp(-c*a) as r increases to infinity. For fixed r>0 it strictly decreases when a increases, by the same coupling with a delayed opportunity to coalesce. These statements hold whether r is less than, equal to, or greater than R.

## 3. Root time and root rate from AC1 and AC2

Set a1=m_AC(1), a2=m_AC(2), and Q=a2/a1^2. Since the AC pair coalesces at t0 plus an independent Exp(r_R) wait,

    a1=beta*r_R/(r_R+c),
    a2=beta^2*r_R/(r_R+2c),  beta=exp(-c*t0).

Consequently

    Q=(r_R+c)^2/[r_R(r_R+2c)]>1,
    r_R=c*(sqrt(Q/(Q-1))-1),
    beta=a1*(r_R+c)/r_R,
    t0=-(1/c)*log(beta).

All quantities are well-defined at every admitted finite positive root rate; beta is strictly between 0 and 1. This identifies r_R,t0 and hence B_1,B_2.

## 4. The C rate from CC1

The CC law is L_(0,r_C) with the now known t0,r_R. Section 2 proves that M_1(0,r_C) is strictly increasing in r_C. Therefore m_CC(1) uniquely identifies r_C. Equalities between r_C and any other population rate do not alter this monotonicity. The C-rate tie across the pulse is MATERIAL to this step.

## 5. Pulse time and probability from BC1 and BC2

With r_C,T=t0,R=r_R now known, define

    D_k(h)=M_k(h,r_C)-B_k>0.

The BC moments satisfy m_BC(k)-B_k=g*D_k(h), so their ratio eliminates g. The following shows that D_2(h)/D_1(h) is strictly decreasing on 0<h<T.

Condition on a C-population coalescence at t in(h,T). Relative to the root-only pair, this replaces a root time with the earlier time t. Therefore

    D_k(h)=r_C*exp(r_C*h)
            * integral_(h to T) exp(-r_C*t)
                [exp(-c*k*t)-B_k] dt.             (1)

Both bracketed quantities are strictly positive on [h,T], including at T because R/(R+c*k)<1. Put x=exp(-c*t). The pointwise ratio of the k=2 and k=1 brackets is

    q(t)=(x^2-B_2)/(x-B_1).

The root baseline has B_2-B_1^2>0 (equivalently, exp(-c*(T+Exp(R))) has positive variance). Direct differentiation gives

    d/dx [(x^2-B_2)/(x-B_1)]
      =1+(B_2-B_1^2)/(x-B_1)^2 >0.

Because x strictly decreases with t, q(t) strictly decreases with t. In (1) the common factor r_C*exp(r_C*h) cancels in the ratio. Thus D_2(h)/D_1(h) is the weighted average of q(t) over [h,T], with strictly positive weight

    w(t)=exp(-r_C*t)*(exp(-c*t)-B_1).

If 0<h1<h2<T, the removed interval[h1,h2) contains strictly larger q values than the retained interval[h2,T]. Both have positive weight. The weighted average therefore strictly decreases as h increases.

It follows that

    [m_BC(2)-B_2]/[m_BC(1)-B_1]

uniquely identifies h. Its denominator is positive because g>0 and D_1(h)>0. Then

    g=[m_BC(1)-B_1]/D_1(h)

is identified. No assumption of distinct population rates is used.

## 6. Two moments identify the AB onset and rate globally

Since g is now known and g<1, obtain

    nu_k=[m_AB(k)-g*B_k]/(1-g)=M_k(t1,r_AB), k=1,2.

We prove that (a,r)->(M_1(a,r),M_2(a,r)) is one-to-one on 0<=a<T, r>0, with T,R fixed. If two parameters have the same a, strict rate monotonicity of M_1 gives equal r. Otherwise relabel them so a1<a2. Equality of first moments requires r1<r2, since earlier onset and a rate at least as large would give a strict stochastic advantage.

Let D(t)=S_(a1,r1)(t)-S_(a2,r2)(t). It is strictly negative on (a1,a2). On [a2,T], its sign is the sign of

    log[S_(a1,r1)(t)/S_(a2,r2)(t)]
      =(r2-r1)*t+r1*a1-r2*a2,

an increasing affine function that is initially negative. It can cross zero at most once. After T the two survivals acquire the SAME positive root factor exp[-R(t-T)], so their difference retains its sign at T.

For any nonnegative coalescence age with survival S,

    E[exp(-z*L)]=1-z*integral_(0 to infinity) exp(-z*t)*S(t) dt.  (2)

Equality of first moments therefore gives integral exp(-c*t)*D(t)dt=0. Since D is strictly negative on an interval, it must become positive; hence its unique crossing t_star lies strictly before T. It is negative before t_star where nonzero and positive afterwards. Then

    integral exp(-2c*t)*D(t)dt
      =integral exp(-c*t)*[exp(-c*t)-exp(-c*t_star)]*D(t)dt <0.

The equality subtracts exp(-c*t_star) times the zero first weighted integral. The integrand is negative on both nonzero sign regions: the second bracket is positive before t_star and negative afterwards. Formula (2) now yields

    M_2(a1,r1)-M_2(a2,r2)>0.

Thus two distinct onset/rate pairs with equal first moments cannot have equal second moments. This proves GLOBAL injectivity, including all equal-rate relations with R or other populations. It identifies t1 and r_AB from nu_1,nu_2. The recovered source automatically obeys h<t1<t0 when the input moments come from an admitted source.

This argument also supplies a sequential monotone search structure, not just uniqueness. For each candidate a with B_1<nu_1<exp(-c*a), there is one r(a)>0 solving M_1(a,r)=nu_1. Along that first-moment curve, M_2(a,r(a)) strictly decreases as a increases. Hence the remaining determination is a scalar monotone comparison after a scalar rate solve. Certified finite-precision handling of uncertain input intervals still requires a reviewed numerical implementation; no exact transcendental equality oracle is assumed or supplied here.

## 7. The A and B rates from their first moments

With t1,r_AB,t0,r_R known, the AA pair coalesces at rate r_A before t1 and thereafter follows a fixed continuation law. Increasing r_A, coupled by extra early clocks, makes its coalescence time smaller, with a strict change on a positive-probability event because t1>0. Consequently m_AA(1) strictly increases in r_A and identifies it.

For BB, fix the already recovered h,t1,t0,g,r_C,r_AB,r_R. Compare two values r_B'<r_B. Before h, couple the common rate-r_B' clock and the extra rate r_B-r_B' clock. If the extra clock finishes the high-rate pair before the low-rate pair, its coalescence age is already strictly earlier; the later routing of that merged block cannot change this age. If both pairs remain unmerged at h, use the SAME two independent current-block routing coins. For stay/stay routing the B-arm clocks on (h,t1) can again be coupled by common/extra clocks. For route/route both pairs use the same C process; for split routing both wait to the same root. Subsequent AB/root clocks are shared.

Thus T_BB(r_B)<=T_BB(r_B') under this coupling. Strict inequality has positive probability already from an extra pre-pulse merger before h while the low-rate pair survives h. Therefore m_BB(1) strictly increases in r_B. This identifies r_B while preserving the required B-rate tie across the pulse. No merged descendant is independently rerouted, and no common inheritance coin is substituted.

All five rates, all three event times and g have now been uniquely recovered. Population sizes follow from theta_P=2/r_P. This proves the theorem in section 1.

## 8. Consequences and limits

1. The exact fixed-family two-site sequence law is globally parameter-injective under the stated complete phased sampling/channel assumptions. Two is a sufficient bound, not a minimality assertion. The earlier 55-site proof and 330-feature interface remain correct, now with a weaker sufficient-length bound.
2. Nine shifted features Y provide the identified mean vector. The accepted compact-domain inverse-certificate construction can use this nine-coordinate map, with its same source-specific forward envelope. With a certified coordinate gap Delta, the inherited fixed-time bound becomes m>=32*Delta^(-2)*log(18/delta) independent loci. This substitutes the coordinate count in an EXISTING conditional confidence theorem; it does not provide a numerical Delta, a practical sample count, or a completed inverse implementation.
3. More sites and the other accepted features may improve finite-data precision; the theorem does not claim that discarding them is statistically optimal. Within-locus feature dependence is retained and loci, not features, are the independent replicates.
4. The monotone sequential structure is promising for a sharper certified inverse/contractor, but it does not alter the currently frozen 330-feature evaluator or bounded-filter baseline before separate review. Phasing, missingness, unknown locus rates, arbitrary biological networks and source admission remain as previously declared.
5. The broad canonical-history classification and the original fixed-panel clock-JC observation-equivalence result are preserved independently. Original G3/G4 are not solved by this sharper fixed-family theorem. No Lean, external peer review, or novelty certification is claimed.

## 9. Prior and provider attribution

The pair densities, projectivity and JC character identity are inherited from the accepted 55-site/330-feature providers. Thawornwattana, Huang, Flouri, Mallet and Yang (2023), *Inferring the Direction of Introgression Using Genomic Sequence Data*, https://academic.oup.com/mbe/article/40/8/msad178/7239274, is the close biological pair-law precedent. Pair analysis is not claimed as new.

The shifted-exponential root-pair inversion is itself close prior work: Durden and Sullivant, *Identifiability of phylogenetic parameters from k-mer data under the coalescent*, https://arxiv.org/abs/1705.06993, §5 Theorem 5.1, establishes pair divergence/coalescent-parameter identification using two distinct k-mer lengths. For lengths 1 and 2, this is algebraically the same root-pair Laplace-moment identification used here. Their assembled tree results assume a common population-size parameter; they do not thereby establish the present pulse-family BC/AB assembly. No new root-pair inversion principle is claimed.

Zhu and Yang (2021), *Complexity of the simplest species tree problem*, https://discovery.ucl.ac.uk/id/eprint/10118758/, provides an earlier two-site four-parameter identification result in a different three-species, three-sequence MSC setting. Its model is not silently identified with this tied-size six-copy introgression family. Low-order coalescent/Laplace moment methods, monotone truncation averages and single-crossing arguments are classical tools. A targeted prior search is being reviewed; historical priority of this assembled nine-mean/two-site conclusion remains unverified.

Exact providers:
- https://github.com/Sodelin/Research-Commons/blob/df6705e55a830869b8c89e7603edb09cb629d07b/research/2026-10-05-dot-msci-55-site-separation-0508z/THEOREM.md
- https://github.com/Sodelin/Research-Commons/blob/ddcb0be5339cee2bf3e26651ca13f11db185a448/research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/COROLLARY.md
- https://github.com/Sodelin/Research-Commons/blob/8dc1c39105eadebd8e920257ea02e7083b6fdade/research/2026-10-05-dot-msci-quantitative-reliability-1028z/THEOREM.md
