# P1: averaged shared counts and the four-/five-local cases

17 October 2026, 21:07 UTC. Author: dot (OpenAI), working with Nolan.

Status: new hand-proof candidate, pending review. No execution, Lean verification, historical-novelty claim or full optimal-copy P1 closure. Accepted component26 is preserved unchanged.

## 1. Claims and the original experiment

The experiment is equality versus FULL trace norm at least epsilon for two unknown N-qubit Gibbs states, common known fixed beta>0, coefficientwise-bounded at-most-k-local Pauli Hamiltonians, arbitrary collective measurements, success at least 2/3 and worst-case TOTAL copies. Degree and total interaction strength per site are unrestricted.

For fixed beta>0 and fixed 0<epsilon<=1/256, the proposed all-sufficiently-large-N lower bounds are

    k=4: Omega_{beta,epsilon}(N^3/log N),
    k=5: Omega_{beta,epsilon}(N^(7/2)/(log N)^(7/8)).    (1)

They improve the corresponding exponents 8/3 and10/3 of accepted component24. The existing general collective uppers remain O(N^4 log N) and O(N^5 log N), respectively. These lower bounds do not determine the optimal rate.

The statistical mechanism is the same conditional-product idea as26, but the likelihood argument is different: average squared Hellinger distance over the actual shared row counts. This removes26's maximum-count truncation, which fails when its count mean ceases to grow. A complete physical accounting for label weight k-1 is supplied below. The last section bounds the testing complexity of these particular families, so they are not mistaken for a route that automatically reaches the full-class upper.

## 2. Complete-row experiment and exact priors

Fix k in {4,5}, r=k-1, s>=2k and D=binom(s,r). One row consists of a uniform observed r-element label S subset [s], followed by s independent data bits conditional on that label. The unknown row law is

    P_p(S,y)=D^(-1) product_{j=1}^s p_{S,j}^{y_j}(1-p_{S,j})^{1-y_j}.

Let

    alpha=128 epsilon<=1/2, ell=1/s, delta=alpha/s,
    h=1/2, C1=128 exp(2), c1=1/(100 sqrt(C1)),
    mu=min{1, c1 s^(3/2)/(alpha^2 sqrt(D))}, B=Dmu.

Draw one parameter pair independently for every (S,j), ONCE before all sampling:

* Null: with probability 1/2 take p=q=h; otherwise p=q=ell.
* Alternative: with probability 1/2 take p=q=h; otherwise choose a uniform sign sigma and take p=ell+sigma delta, q=ell-sigma delta.

Every null draw gives exactly equal distributions. Every probability lies in [1/(2s),1/2]. This adapts the established heavy/light product prior credited in26; the heavy probability here is fixed at1/2, not set to1/mu.

Let F be the event that every label has at least s/3 light coordinates. Then

    Pr(F^c)<=D exp(-s/18).                             (2)

For each label in F, at least s/6 light coordinates share one sign. Their all-zero event has a probability difference at least (alpha/3)exp(-3). Consequently their full L1 distance exceeds alpha/48. Averaging over the uniform labels gives

    ||P_p-P_q||_1>alpha/48=8epsilon/3.                 (3)

The event calculation is exactly the one displayed in26, Section2, and uses only these light probabilities; changing the heavy probability does not affect it. Condition the alternative prior on F only AFTER bounding the unconditioned observation distance. The conditioning cost is at most (2).

## 3. Average over the shared row counts

Supply independent Poisson(B) numbers of COMPLETE rows from each source. For each label the row counts a_S,b_S are independent Poisson(mu), with the same a_S,b_S shared by all s data coordinates of that label. All labels, counts, zero bits and one bits are observed. There are no independent clocks per coordinate.

Use squared Hellinger distance with the convention

    H2(P,Q)=sum_x(sqrt(P(x))-sqrt(Q(x)))^2.

Thus TV(P,Q)^2<=H2(P,Q), H2(P,Q)<=chi2(P||Q), and

    H2(product_i P_i,product_i Q_i)<=sum_i H2(P_i,Q_i).

The last relation follows by multiplying the affinities 1-H2(P_i,Q_i)/2. Conditional on the entire shared-count vector, the prior-averaged coordinate experiments are independent because their latent parameter pairs were independent. The count distribution is identical under the two hypotheses. Therefore, writing Delta for one coordinate's conditional chi-square distance,

    TV(full alternative observations, full null observations)^2
       <=H2(full alternative observations, full null observations)
       =E_counts H2(conditional alternative data, conditional null data)
       <=D s E_{a,b}[Delta(a,b)].                     (4)

Ancillary ordering of rows conditional on labels can be restored identically under both hypotheses. Formula (4) does not assert independence of the coordinate counts and does not discard labels with large counts.

### Exact averaged likelihood bound

At one coordinate let n=a+b and take H=Bern(h)^{tensor n} as reference. Set v=h(1-h), z=ell-h and

    u(1)=1/h, u(0)=-1/(1-h),
    L(t)=product_i [1+(z+tau_i t)u_i],

where tau_i=+1 for the a first-source observations and -1 for the b second-source observations. The null and alternative densities relative to H are

    (1+L(0))/2,  [1+(L(delta)+L(-delta))/2]/2.

The null density is at least1/2. Orthogonality of products of the centered u_i, and the symmetric Taylor remainder, give the same exact bound as26 before any count truncation:

    Delta(a,b)<=delta^4/(8v^2) [
       (n)_4 x^2(1+x)^(n-4)
       +4(n)_3 x(1+x)^(n-3)
       +2(n)_2(1+x)^(n-2)],                           (5)

where x=(|z|+delta)^2/v and a term with zero falling factorial is omitted. For n<2 the distance is zero. The identity underlying (5) is [j(j-1)]^2=(j)_4+4(j)_3+2(j)_2. It applies to every allocation a,b, not just their sum under independent coordinate sampling.

Here n is Poisson(2mu). Its factorial generating function gives, for j>=0,

    E[(n)_j(1+x)^(n-j)]=(2mu)^j exp(2mu x).

All terms are nonnegative, so averaging (5) yields

    E Delta <= delta^4 exp(2mu x)/v^2
                     [2mu^4 x^2+4mu^3 x+mu^2].        (6)

Since h=1/2, v=1/4; since delta<=ell, x<=1; and mu<=1. Hence

    E Delta <=112exp(2)delta^4 mu^2
             <=C1 delta^4 mu^2.

Combining this with (4) and the definition of mu proves

    TV(full unconditioned observation laws)^2
       <=C1 D alpha^4 mu^2/s^3<=1/10000.              (7)

After conditioning the alternative prior on F, the TV is at most1/100+Dexp(-s/18), hence less than0.02 for sufficiently large s. This is an unconditional treatment of the common label counts. It repairs, rather than assumes away, the k>=4 failure of26's growing-mean count-tail argument.

## 4. Exact normalized k-local Gibbs encoding

The encoding parameters depend only on s,k,beta,epsilon, never on the unknown draw. Set eta=1/(100B), take s large enough that eta<=epsilon/8, and define

    V=log(2s), lambda=16[s+log(2s/eta)].

Each of the s label variables has m clone spins; there are s additional data spins. Let x_i=w_i/m be the fraction of ones in clone block i and y_j=(1-d_j)/2 the data bits. Define

    v_{S,j}(y_j)=-y_j log p_{S,j}-(1-y_j)log(1-p_{S,j}),
    E_p(x,y)=lambda(sum_i x_i-r)^2
               +sum_{|S|=r}(product_{i in S}x_i)sum_j v_{S,j}(y_j).

The complete Bernoulli negative log likelihood is retained: 0<=v<=V, and its {I,Z} coefficient l1 norm is at mostV. E_p is nonnegative on the whole fractional cube. Write

    E_p=c_p+sum_{A nonempty}h_A z_A, |A|<=k,
    sum_A|h_A|<=S0:=lambda(s+r)^2+D s V.               (8)

Here z_A may contain clone spins and data spins. Choose the least integer m>=2 satisfying

    m^(k-1)>=16V/beta,
    m^k>=16lambda/(beta s^(k-2)).                      (9)

For R reservoir spins, use F_l=sum_{|A|=l}a_A and e_l=F_l/binom(R,l), including F_0=e_0=1. With j0=beta/8 and gamma=h0=beta/4, set

    L_clone=sum_i sum_{u<v in block i}z_u z_v,
    K=-j0 L_clone F_{k-2}(a),
    W_p=sum_A h_A z_A e_{k-|A|}(a),
    Q_p=K+W_p-gamma F_k(a)-h0 sum_l a_l,
    H_p=Q_p/beta.

The scalar c_p may be discarded but none of the label-dependent normalization terms is discarded. Total physical size is

    N_s=sm+s+R.                                       (10)

### Every coefficient and its possible collision

Require R>=2ksm. For a specified data spin and a specified clone support with a distinct label blocks, 0<=a<=r, the signal coefficient has magnitude at most

    2^(-r)m^(-a)binom(s-a,r-a)V.

After adjoining k-a-1=r-a reservoir spins, binom(R,r-a)>=(sm)^(r-a) bounds this by V/(2^r m^r)<=beta/(16*2^r). This also covers a=r, where no reservoir is used.

For a clone-containing support with NO data spin, summing all s data normalization terms gives instead the bound

    2^(-r)m^(-a)binom(s-a,r-a)sV,  1<=a<=r.

It adjoins k-a=r+1-a reservoir spins, so its resulting coefficient is at most V/(2^r m^k). The clone-free scalar is discarded. Signal terms never contain two clones from the same label block.

The quadratic penalty contributes a clone field -lambda(s-2r)/(2m) and every distinct-clone-pair coefficient lambda/(2m^2). Since s>=2r, after homogenization both are bounded by

    lambda/(2s^(k-2)m^k)<=beta/32.                    (11)

A lock term has two distinct clones in the SAME block and k-2 reservoir sites, coefficient -beta/8. Only a same-block penalty pair can collide with it; their sum is bounded by beta/8+beta/32. Other clone-only signal/penalty collisions also stay below beta. Data-containing supports have no penalty or lock term. Reservoir-only supports have coefficients beta/4 and do not collide because k>=4. Thus every nonidentity coefficient of H_p has magnitude at most one and locality at most k. No auxiliary spin or multiplicity is omitted.

## 5. Uniform physical approximation with finite guards

Write

    C_lock=binom(R,k-2), mu_R=2j0 C_lock,
    B0=j0 s binom(m,2)C_lock, S0'=S0+B0,
    b=floor(R/2), B_R=binom(b,k-1), C_R=binom(b,k), A0=gamma B_R.

Choose R also to satisfy

    R>=4k,
    mu_R m^2>=32log(2s),
    sm exp(-mu_Rm/4)<=1,
    2^s 4s^(r+1)m exp(-mu_Rm/4)<=eta/4,
    8k S0'/R<=gamma B_R, 4h0<=gamma B_R,
    2R exp(-A0)<=eta/32,
    exp(-2h0R)<=eta/8,
    2^R exp(-gamma C_R)<=eta/16.                      (12)

The chosen lambda satisfies the additional finite guards, eventually in s,

    s exp(-lambda)<1,
    2^s 2s^(r+1)exp(-lambda)/(1-s exp(-lambda))<=eta/4. (13)

One may require (13) explicitly. The following argument uses the actual displayed inequalities.

### Clone/data leakage at the plus reservoir

Conditioning on all reservoir spins plus gives the law proportional to

    exp[-E_p-mu_R sum_i w_i(m-w_i)].

On constant clone blocks of weight r, exactly one label monomial survives. Summing exp(-sum_j v_{S,j}) over all data bits gives exactly one per label. The ideal-shell partition is D, and its conditional distribution is precisely the desired uniform-label row law.

Constant clone blocks of incorrect weight contribute a partition at most (13), by nonnegative signal energy. This counts all 2^s data strings.

For nonconstant blocks round to the nearest constant configuration with fixed ties. If w is its weight, q>=1 the number of minority spins and a=|w-r|, the same split-lock bound as26 gives energy at least

    mu_R m q/4+min{lambda a^2/4,mu_Rm^2 a/8}.

For a>=1 the second term is at least4a log(2s). Summing rounded strings gives at most2s^r, and summing minority choices and all data strings gives at most

    2^s 2s^r[exp(sm exp(-mu_Rm/4))-1]
       <=2^s 4s^(r+1)m exp(-mu_Rm/4)<=eta/4.

Hence the total conditional outside partition is at mosteta/2, while the ideal partition is D>=1. The conditional TV error is at mosteta/2.

### Reservoir stability and the even-degree identity

If there are l minus reservoir spins, |e_d(a)-1|<=2dl/R. For l<=R/2 the K+W change is at most2klS0'/R. At least lB_R reservoir k-subsets have negative product, so (12) leaves an energy cost at least A0l above all plus, pointwise in ALL clone and data assignments.

For EVEN k, at all minus F_{k-2} is unchanged and

    W_p(z,d,-)=W_p(-z,-d,+),
    K(z,-)=K(-z,+).

The change of variables flips EVERY nonreservoir spin, INCLUDING ALL DATA SPINS. It gives the exact partition identity

    Z_minus=exp(-2h0R) Z_plus.

This is a full partition identity, not an assertion that the ideal label shell is individually fixed. Within q flips of all minus, the perturbation bound is2kqS0'/R and the field can reduce the cost by2h0q. Conditions (12) leave at least A0q. The mixed layers have relative partition at most (1+exp(-2h0R))2Rexp(-A0); together with the all-minus phase their total is beloweta/4.

For ODD k, do not use that identity. When l>R/2 there are at least C_R negative k-products, whereas the total K+W change is at most2S0'. Since C_R/B_R=(b-k+1)/k>=R/(4k), (12) implies gamma C_R>=2S0'. The energy cost is therefore at leastgamma C_R. Near-plus plus far-layer partition bounds in (12) again total beloweta/4.

In either case the actual Gibbs distribution differs in TV by less thaneta from the ideal encoded row law, uniformly over every parameter array in the priors. Moreover conditioning the actual distribution on the visibly recognizable ideal event gives that row law EXACTLY.

## 6. Existence, total size and the lower-bound transfer

For fixed k in {4,5}, beta and epsilon, D=Theta(s^(k-1)). The statistical budget B is polynomial in s, so log(1/eta)=Theta(log s), lambda=Theta(s), V=Theta(log s). Conditions (9) give

    m=Theta_{beta,k}( (log s)^(1/(k-1)) ).

Take R=ceil(C_*sm) with a sufficiently large fixed C_*>=2k. The ratio of the S0 contribution in8kS0'/R to gamma B_R is O(log s/m^k)=O((log s)^(-1/(k-1))). The lock contribution ratio is O(1/s). Both vanish. The clone exponent mu_Rm has order s^(k-2)m^(k-1)=Theta(s^(k-2)log s), which dominates the s log2 data entropy and all logarithmic factors in (12). All other suppression guards follow from A0 growing as R^(k-1), gamma C_R as R^k and h0R linearly. Condition (13) follows from the explicit lambda. Thus

    N_s<=C_{beta,k,epsilon} s(log s)^(1/(k-1)).        (14)

For every null draw the constructed Hamiltonians coincide exactly. For every alternative draw in F, actual full trace distance exceeds8epsilon/3-4eta>=epsilon. The ideal row simulator uses one unknown complete row, duplicates the label into clone blocks and appends plus reservoir spins. It uses no parameter oracle.

A total-budget-T collective tester on diagonal states can be simulated from pre-sampled basis rows, including adaptive allocation. With T=floor(B/4), the Poisson experiment supplies T rows from each source except with probability at most2exp(-9B/32). Replacing ideal rows by actual states incurs at mostTeta per acceptance probability. A successful tester would therefore give a difference between null and alternative acceptance probabilities at least

    1/3-2Teta-4exp(-9B/32)>0.3

for large s. Section3 bounds that difference by less than0.02. This contradiction proves Omega(B) worst-case total copies, without expected-budget substitution or amplification.

For k=4, D=Theta(s^3) and mu tends to a strictly positive fixed constant (possibly one), so B=Theta_epsilon(s^3). For k=5, mu=Theta_epsilon(s^(-1/2)) and B=Theta_epsilon(s^(7/2)). Padding to every sufficiently large requested N uses

    s=floor(N/[2C(log N)^(1/(k-1))])

and N-N_s zero-Hamiltonian maximally mixed spectators. This preserves equality, trace norm, locality, coefficient bounds and the sample simulator. Equation (14) then yields (1).

## 7. Why the constructed families have their own testing ceilings

These upper bounds concern the specified hard families and their encoded Gibbs states. They do not supply an upper for arbitrary noncommuting Gibbs Hamiltonians.

### The accepted three-local family26

In26, h=1/mu and mu=Theta_epsilon(s^(1/4)), with D=binom(s,2). Take n1=ceil(80mu log(Ds+2)) pilot rows per label from the first source. Classify a coordinate as heavy if its success count is at leastn1/(2mu). For sufficiently large s, mu<=s/12: a heavy coordinate has mean n1/mu, while a light one has mean at most n1/(8mu). Elementary Chernoff bounds put each classification error belowexp(-n1/(8mu)); a union bound makes all classifications correct with probability tending to one.

Freshly take two rows from each source at every label. For each identified light coordinate form

    Z_{S,j}=(X_1-Y_1)(X_2-Y_2).

Every null mean is zero. On F the sum's alternative mean is at least4alpha^2D/(3s). Its variance is at most4D/s, because p+q=2/s on every light coordinate and the fresh rows are independent. A threshold at2alpha^2D/(3s) has error at most9s/(Dalpha^4), which tends to zero.

Collecting the pilot rows under uniform random labels takes O(Dmu log(Ds)) complete rows with high probability; fresh pairs cost O(Dlog D). Explicitly, use pilot COMPLETE-row totals of mean2Dn1 from the first source, so each label has mean2n1 pilot rows. For each source's fresh batch use mean80Dlog(D+2), and retain the first two rows at every label. Cap each complete-row total at twice its expectation. Chernoff bounds and a union bound control inadequate label counts and the total caps. This is a fixed worst-case row budget. It proves a ceiling O(Dmu log(Ds)) for this family, matching26's polynomial exponent.

### The four-/five-local families of this note

Now h=1/2 is known. For one paired row (one from each source with the same label) define for each coordinate

    f(X,Y)=XY-(h+ell)(X+Y)/2+h ell.

Its absolute value is at most one. Under either null coordinate type its mean is (p-h)(p-ell)=0. Under an alternative light coordinate, its mean is -delta^2; under a heavy coordinate it remains zero.

Given complete-row label counts a_S,b_S, pair the first min(a_S,b_S) rows. Let K=sum_S min(a_S,b_S). Conditional on the counts and fixed parameters, all paired-coordinate summands are independent. The summed statistic has variance at mostKs. On F its alternative mean is at most-Kalpha^2/(3s). A threshold at-Kalpha^2/(6s) has error at most

    36s^3/(Kalpha^4).                                (15)

For k=4, take a fixed per-label Poisson mean nu>=max{64,16000s^3/(Dalpha^4)}. Since D=Theta(s^3), nu is a constant depending on epsilon. With probability tending to one, at leastD/2 labels have BOTH counts at leastnu/2, so K>=nu D/4>=4000s^3/alpha^4. Equation (15) is then below0.01. The total row cost is O_epsilon(D)=O_epsilon(s^3).

For k=5, take nu=1000s^(3/2)/(alpha^2sqrt(D)), which is at most one for sufficiently large s. A label has at least one row from each source with probability (1-exp(-nu))^2>=nu^2/4. Independently across labels, Chernoff concentration gives

    K>=Dnu^2/8=125000s^3/alpha^4

with probability tending to one. Again (15) is below0.01. Total cost is O_epsilon(Dnu)=O_epsilon(s^(7/2)). In both cases cap the Poisson COMPLETE-row totals at four times their expectation, adding exponentially small failure probability and giving a worst-case budget. These are matching polynomial ceilings for the specific priors.

For the actual encoded Gibbs family, first measure in the common computational basis and retain only the known ideal event: all reservoir spins plus, constant label blocks, and label weight r. Retention probability is at least1-eta, and conditional rows are exact. Constant oversampling with a fixed cap gives the same upper-bound orders. This rejection step relies on the declared encoding and cannot be imposed on a general unknown Gibbs state.

## 8. Remaining P1 gap and attribution

The count-averaging repair supplies meaningful further exponents for k=4 and5 if accepted. It does not blindly extend26: its heavy probability, small-count regime and distance calculation are explicitly different. The corresponding statistical hard families have the ceilings above, so they do not automatically reach the full upper O(N^k log N). At k=6 the analogous power would be4, already supplied by24 with a better logarithm; for k>6 this mechanism has a smaller power than24. No improvement there is claimed.

The remaining full P1 task still needs a stronger hard family or a genuinely full-class collective upper, with the dependence on accuracy, temperature and locality kept explicit. Conditional-product sampling and its identifiable ideal event do not hold for arbitrary noncommuting Gibbs states. No historical priority, efficient physical preparation, bounded-degree or bounded-total-strength theorem, or full optimal-copy result is asserted.

Primary and accepted sources:

1. Canonne, Diakonikolas, Kane and Stewart, *Testing Bayesian Networks*, COLT2017, Section5.2/Theorem40, PDF indices25-27: https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf . This credits the established heavy/light product-prior idea. The shared-label Hellinger calculation and present physical admission are supplied here.
2. Accepted26, exact preserved proof and coordinating review: https://github.com/Sodelin/Research-Commons/blob/a823c8445e1dd2ce4cb4008a547958fa50bac810/research/2026-10-16-g6-gibbs-certification/conditional-product-label-26/README.md . Its growing-count truncation is not used in the new lower-bound proof.
3. Accepted24, reservoir and shell controls for both parity cases: https://github.com/Sodelin/Research-Commons/blob/0e3e40d07edb9292a2c5a4c64c8f6fe0ae56e98d/research/2026-10-16-g6-gibbs-certification/reservoir-amplified-lock-24/README.md . The even-degree change of variables here explicitly includes data spins.
4. Preserved general collective upper13: https://github.com/Sodelin/Research-Commons/blob/5055e470b32c17bdf93c55e09a891969be9ea23f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md . No new upper for the full original class is proved here.

This draft remains unaccepted until full review. Its source references do not establish historical novelty of the composition.
