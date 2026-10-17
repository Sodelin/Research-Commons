# P1: common random label masses conceal conditional differences

17 October 2026, 22:53 UTC. Author: dot (OpenAI), working with Nolan.

Status: new hand-proof candidate, awaiting independent and coordinating review. No accepted exponent improvement, historical-novelty claim, Lean verification, or full P1 closure is asserted by this producing-pass document. Accepted components24/26/27/28 remain unchanged.

## 1. Claim, experiment and difference from27

For each fixed integer k>=5, beta>0 and fixed 0<epsilon<=1/1024, the proposed lower bound for every sufficiently large physical size N is

    Omega_{k,beta,epsilon}(
      N^((2k+1)/3) / (log N)^((2k+1)/(3(k-1))) ).       (1)

The original experiment is equality versus FULL trace norm at least epsilon for two unknown N-qubit Gibbs states at the same known beta, every nonidentity Pauli coefficient bounded by one in magnitude, locality at most k, success at least2/3, arbitrary collective measurements and worst-case TOTAL copies from both states. Interaction degree and per-site total strength are unrestricted. A diagonal subclass suffices for a lower bound in this larger class.

Unlike27, labels are not uniform. An unknown sparse set has larger mass and carries no conditional difference. The other labels have smaller mass and carry the product-prior differences. The two sources always share their exact label weights and their exact normalization. The latent mass types are parameters of the Hamiltonians, not separately supplied observable registers. The actual label itself remains fully observable.

If proved, (1) improves the polynomial exponent of24 for k>=5 and of27 for k=5, within the stated narrower accuracy range. The general collective upper remains O(N^k log N) at fixed parameters. This does not close that gap. No k=3 or k=4 improvement is claimed.

## 2. Complete row law and exact null/alternative priors

Fix s>=2k, r=k-1, D=binom(s,r), and set

    alpha=512epsilon<=1/2, ell=1/s, delta=alpha/s, h=1/2,
    mu=s / [1600 alpha^(4/3) D^(1/3)], B=Dmu.          (2)

Take s sufficiently large that 0<mu<=1/4 and B>=1. A complete row is an r-element label S subset[s] followed by s binary data values y=(y_1,...,y_s).

Independently for each label draw a mass type R_S in {0,1}, with Pr(R_S=1)=mu. Set its RAW weight

    w_S=1 if R_S=1, and w_S=mu if R_S=0,
    H=sum_S R_S, W=sum_S w_S=Dmu+(1-mu)H.              (3)

In particular W>=B deterministically. Given the probabilities p_{S,j} for one source, its actual normalized row law is

    P(S,y)=(w_S/W) product_j p_{S,j}^{y_j}(1-p_{S,j})^(1-y_j).

For every coordinate independently draw a type C_{S,j}, heavy or light, with equal probabilities. The two-source priors are:

* Null, every R_S: a heavy coordinate has p=q=h; a light coordinate has p=q=ell.
* Alternative, R_S=1: exactly the same coordinate rule as the null.
* Alternative, R_S=0: a heavy coordinate still has p=q=h; a light coordinate has p=ell+sigma delta, q=ell-sigma delta, where sigma is an independent uniform sign.

All latent variables are drawn ONCE before all copies. All coordinate probabilities lie in[1/(2s),1/2]. Every null draw gives exactly P=Q. Before conditioning below, the distribution of R, hence of W and of the normalized label probabilities w_S/W, is identical under both hypotheses. Conditional on R, the two actual sources have the same label marginal exactly, including under the alternative. Only their conditional data laws differ.

### Far alternatives and the conditioning cost

Let F be the event that every label has at least s/3 light coordinates and H<=2B. By Hoeffding and the multiplicative binomial Chernoff bound,

    Pr(F^c)<=D exp(-s/18)+exp(-B/3)=:zeta_s ->0.       (4)

For a signal label, at least s/6 light coordinates share one sign. On that coordinate group of size j, the difference in the all-zero event probabilities is

    (1-ell+delta)^j-(1-ell-delta)^j
       >=2j delta(1-ell-delta)^(j-1)
       >=(alpha/3)exp(-3).

Here j<=s, ell+delta<=3/(2s), and s>=3. The full L1 distance is at least twice the event gap, hence greater than alpha/48. On F, at least D/2 labels are signal labels, and W<=3B. Their total normalized mass is at least (D/2)mu/(3B)=1/6. Therefore

    ||P-Q||_1>alpha/288=(16/9)epsilon.                (5)

Condition ONLY the alternative prior on F after the observation-law calculation. This changes any prior-averaged observation distribution by TV at most zeta_s. Its normalization distribution can change under this conditioning; no equality of the conditional and unconditional W distributions is assumed. Each retained alternative still has the identical W in its two sources.

## 3. Poisson observation experiment without discarding normalization

Given the latent draw, take independent counts a_S,b_S from each source, both Poisson(w_S), for every label. For each occurrence draw a COMPLETE s-bit data row from that label's conditional product distribution. Counts and all labels, zeros, ones and row groupings are observed.

The total count from each source is Poisson(W). Conditional on the total, its ordered complete rows are IID from the normalized law P or Q. The conditional ordering given label counts is uniform and can be restored using parameter-independent randomness. Thus this experiment provides actual normalized rows, with an extra informative random total. It is not a model with independent clocks per coordinate, and it does not replace W by its mean.

Conditional on (a_S,b_S), all s coordinates at that label share those two counts. Independent priors over coordinates make the PRIOR-AVERAGED data law a product over coordinates. Independent priors over labels make the entire UNCONDITIONED observation law a product over labels, including the common mass type's two-source counts.

## 4. Two bounds for a coordinate likelihood

Fix a,b, write n=a+b and let L0 denote the one-coordinate null prior-averaged data distribution. Let L1 be its alternative distribution at a signal label. Put d(a,b)=chi2(L1||L0). For n<2, d=0.

First use Bernoulli(h)^tensor n as reference, v=h(1-h)=1/4, z=ell-h and

    u(1)=1/h, u(0)=-1/(1-h),
    L(t)=product_i[1+(z+tau_i t)u_i],

where tau_i is plus on first-source observations and minus on second-source observations. The null density is (1+L(0))/2; the alternative density is [1+(L(delta)+L(-delta))/2]/2. The null density is at least1/2.

Expanding in the orthogonal products of centered u_i, the symmetric Taylor remainder for a subset of size j is bounded by delta^2 j(j-1)(|z|+delta)^(j-2)/2. Thus, with x=(|z|+delta)^2/v<=1,

 d(a,b)<=delta^4/(8v^2)[
   (n)_4 x^2(1+x)^(n-4)+4(n)_3 x(1+x)^(n-3)
                         +2(n)_2(1+x)^(n-2)]
       <=2 delta^4 n^2(n-1)^2 2^n.                  (6)

A term with zero falling factorial is omitted. The identity used is [j(j-1)]^2=(j)_4+4(j)_3+2(j)_2. This is the coordinate calculation from26/27, reproduced to specify the normalization and constants.

The second bound uses Bernoulli(ell)^tensor n, denoted L, as reference. Write M for the mean of the two sign-perturbed product distributions. Since L0 includes L with weight1/2 and L1-L0=(M-L)/2, convexity of chi-square in its first argument gives

    d(a,b)<= (1/2)chi2(M||L)
           <=(1/2)[(1+y)^n-1],
    y=delta^2/[ell(1-ell)]=alpha^2/(s-1).             (7)

Both sign-perturbed products have chi-square equal to (1+y)^n-1, regardless of the allocation a,b. No balanced-count premise is used.

For the ENTIRE conditional s-coordinate row experiment, put

    Ddata(a,b)=chi2(L1^tensor s||L0^tensor s)
             =(1+d(a,b))^s-1.

Use (6) once and (7) to control the remaining s-1 factors:

    Ddata <=s d(1+d)^(s-1)
       <=2alpha^4/s^3 n^2(n-1)^2 2^n exp(n alpha^2)
       <=2alpha^4/s^3 [(n)_4+4(n)_3+2(n)_2] 3^n.      (8)

Indeed (1+d)^(s-1)<=(1+y)^(n(s-1))<=exp(n alpha^2), and 2exp(alpha^2)<=2exp(1/4)<3. Bounding the full row by a sum of coordinate chi-squares without this factor would be invalid; (8) supplies the necessary all-count control.

## 5. The mass-mixture denominator and the full experiment

Let C_lambda(a,b)=exp(-2lambda)lambda^(a+b)/(a!b!), the joint law of two independent Poisson(lambda) counts. At a label, the null and alternative joint count/data densities are respectively

    N = [mu C_1+(1-mu)C_mu] L0^tensor s,
    A = mu C_1 L0^tensor s+(1-mu)C_mu L1^tensor s.

The heavy mass type is shared by both sources and all data coordinates. Retain that shared-mixture denominator:

    chi2(A||N)
      =sum_{a,b} (1-mu)^2 C_mu(a,b)^2
          /[mu C_1(a,b)+(1-mu)C_mu(a,b)] Ddata(a,b)
      <=exp(2-4mu+2mu^2)/mu
            E_{a,b IID Poisson(mu^2)} Ddata(a,b).     (9)

The equality C_mu^2/C_1=exp(2-4mu+2mu^2)C_(mu^2) gives the last step. It is not independence of individual coordinate clocks.

For n~Poisson(2mu^2), E[(n)_j 3^n]=(6mu^2)^j exp(4mu^2). Combining this identity with (8)--(9),

 chi2(A||N)<= 2alpha^4/(s^3 mu) exp(2-4mu+6mu^2)
                      [1296mu^8+864mu^6+72mu^4]
             <=4096 alpha^4 mu^3/s^3.               (10)

For 0<mu<=1/4, 1296mu^4+864mu^2+72<=132 and -4mu+6mu^2<=0; 2*132*exp(2)<4096. These are uniform bounds on all counts.

Before conditioning on F, the label experiments are independent, so

    chi2(full alt||full null)
       <=exp(4096 D alpha^4 mu^3/s^3)-1
       =exp(10^(-6))-1 <2*10^(-6).                  (11)

Consequently their TV is less than0.001. The observation distance after conditioning the alternative prior on F is at most0.001+zeta_s, which is below0.01 for sufficiently large s. Both marginal normalization laws were included: before conditioning, W has the same law under both priors; after conditioning, its possible change is paid by zeta_s. The total counts remain observed throughout.

## 6. Actual k-local Gibbs Hamiltonians and every physical spin

We now give a fixed-beta coefficient-bounded encoding of these normalized rows. Its extension over27 is the nonnegative label term -log(w_S); no new uncounted register is added.

Let eta=1/(100B), take s large enough that eta<=epsilon/8, and put

    V=log(2s), U=log(1/mu), Vbar=V+U,
    lambda=16[s+log(2s/eta)].                         (12)

Each of s label variables has m clone spins z_(i,u) in{+1,-1}. There are s data spins d_j; set y_j=(1-d_j)/2, w_i=(m-sum_u z_(i,u))/2 and x_i=w_i/m. Here w_i is a clone count, distinct from the label weight w_S. Define

    v_(S,j)(y)=-y log p_(S,j)-(1-y)log(1-p_(S,j)),
    E_p(x,y)=lambda(sum_i x_i-r)^2
       +sum_{|S|=r}(product_{i in S}x_i)
             [-log w_S+sum_j v_(S,j)(y_j)].           (13)

Every summand of the signal energy is nonnegative on the fractional cube. Each v has values between0 and V and {I,Z} coefficient l1 norm at most V. Write

    E_p=c_p+sum_{A nonempty} h_A z_A,
    |A|<=k, sum_A|h_A|<=S0:=lambda(s+r)^2+D(sV+U).    (14)

Here z_A can contain clone and data spins. Choose the least integer m>=2 with

    m^(k-1)>=16Vbar/beta,
    m^k>=16lambda/[beta s^(k-2)].                    (15)

For R reservoir spins a_l, write F_j=sum_{|A|=j}a_A and e_j=F_j/binom(R,j), including F_0=e_0=1. With j0=beta/8 and gamma=h0=beta/4, define

    L_clone=sum_i sum_{u<v in block i} z_(i,u)z_(i,v),
    K=-j0 L_clone F_(k-2),
    W_p=sum_A h_A z_A e_(k-|A|),
    Q_p=K+W_p-gamma F_k-h0 sum_l a_l,
    Hamiltonian H_p=Q_p/beta.                        (16)

Use the corresponding q probabilities for the second source, with exactly the same w_S and all deterministic guards. The scalar c_p may be discarded globally. It is not a label-dependent normalization term. Total physical size is

    N_s=sm+s+R.                                      (17)

### Coefficient multiplicities and collisions

Require R>=2ksm. For a specified data spin and a specified clone support of size a from distinct label blocks, 0<=a<=r, the signal coefficient before adding reservoir indices is bounded by

    2^(-r)m^(-a)binom(s-a,r-a)V.

Adding k-a-1=r-a reservoir indices divides it by binom(R,r-a)>=(sm)^(r-a), so the resulting magnitude is at most V/(2^r m^r)<=beta/(16*2^r).

For clone-containing supports with no data spin, 1<=a<=r, the same bound has V replaced by sV+U. It acquires k-a=r+1-a reservoir indices, giving magnitude at most

    (V+U/s)/(2^r m^k)<=Vbar/(2^r m^k)<=beta/(16*2^r).

This includes the extra -log(w_S) term and all data normalization constants. The clone-free scalar is discarded. Signal monomials never contain two clones from the same label block.

The penalty clone field is -lambda(s-2r)/(2m), and each distinct-clone-pair coefficient is lambda/(2m^2). After adding reservoir indices their magnitudes are at most lambda/[2s^(k-2)m^k]<=beta/32. A lock coefficient is -beta/8 on two clones from the SAME block and k-2 reservoir spins; only a same-block penalty pair can collide with it, yielding at most beta/8+beta/32. Other clone-only signal/penalty collisions remain below beta; data-containing terms have no penalty or lock collision. Pure reservoir fields and k-body terms have magnitude beta/4 and are distinct for k>=5. Thus every nonidentity Pauli coefficient of H_p is at most one and every support has size at most k.

## 7. Uniform finite guards for physical approximation

Set

    C_lock=binom(R,k-2), mu_R=2j0 C_lock,
    B0=j0 s binom(m,2) C_lock, S0'=S0+B0,
    b=floor(R/2), B_R=binom(b,k-1), C_R=binom(b,k),
    A0=gamma B_R.

Require the following explicit finite inequalities:

    R>=4k, R>=2ksm,
    mu_R m^2>=32log(2s),
    sm exp(-mu_Rm/4)<=1,
    2^s 4s^(r+1)m exp(-mu_Rm/4)<=eta/4,
    8k S0'/R<=gamma B_R, 4h0<=gamma B_R,
    2R exp(-A0)<=eta/32,
    exp(-2h0R)<=eta/8,
    2^R exp(-gamma C_R)<=eta/16,
    s exp(-lambda)<1,
    2^s 2s^(r+1) exp(-lambda)/(1-s exp(-lambda))<=eta/4.   (18)

These are the same sufficient suppression guards as27 with the enlarged S0. They hold for all draws, since only V and U bound the unknown coefficients.

### Plus-reservoir clone and data leakage

At the all-plus reservoir, the clone/data law is proportional to

    exp[-E_p-mu_R sum_i w_i(m-w_i)].

On constant clone blocks of weight r, exactly one label monomial survives. Its data partition is exactly w_S, because the complete Bernoulli log likelihood in(13) sums to one. Thus the ideal partition is EXACTLY W, and its normalized conditional row law is P. Importantly W>=B>=1. It is not replaced by D or its prior expectation.

Constant clone blocks of incorrect weight contribute an absolute partition at most the last expression in(18), using nonnegative signal energy and counting all2^s data strings.

For nonconstant blocks, round to the nearest constant block, with fixed ties. Let q>=1 be the total minority-spin count and a the absolute difference between the rounded weight and r. Splitting the clone penalty gives energy at least

    mu_R m q/4 + min{lambda a^2/4, mu_R m^2 a/8}.

For a>=1, the second term is at least4a log(2s). Summing rounded configurations gives at most2s^r, and summing minority positions and every data string gives at most

    2^s 2s^r[exp(sm exp(-mu_Rm/4))-1]
      <=2^s 4s^(r+1)m exp(-mu_Rm/4)<=eta/4.

The incorrect constant-block contribution is also at mosteta/4. Since the ideal partition W>=1, conditional TV leakage at the plus reservoir is at mosteta/2. The nonnegative extra label term cannot invalidate these bounds.

### Reservoir leakage and both parity cases

For l minus reservoir spins, |e_j(a)-1|<=2jl/R. The change of K+W_p is at most2klS0'/R. When l<=R/2, at least lB_R reservoir k-subsets have negative product. Guards(18) leave an energy cost at least A0l, uniformly over all clone/data configurations.

For EVEN k, reversing every nonreservoir spin, INCLUDING THE DATA SPINS, gives exactly

    W_p(z,d,-)=W_p(-z,-d,+), K(z,-)=K(-z,+),
    Z_minus=exp(-2h0R)Z_plus.

This holds for the full partition sum, including the label-energy term; it does not require the ideal shell to be fixed by reversal. The same perturbation bound at distance l from all minus, with the possible2h0l field reduction, again leaves cost at least A0l. The near-plus and near-minus sums are controlled by(18), and the all-minus contribution is explicitly paid.

For ODD k and l>R/2, at least C_R k-subsets have negative product. Since C_R/B_R=(b-k+1)/k>=R/(4k), guards(18) imply gamma C_R>=2S0'. The energy cost over all plus is at least gamma C_R. Summing all at most2^R reservoir configurations gives the corresponding guard. Near-plus layers use the earlier bound.

In either parity case the total reservoir leakage is beloweta/4. Combined with the plus-reservoir estimate, the actual Gibbs basis law has TV less thaneta from the ideal encoded row law, uniformly over BOTH sources and ALL unconditioned parameter draws. The event of all-plus reservoir, constant clone blocks and weight r is visibly recognizable; conditioning on it gives the normalized ideal row law exactly. Its rare complement is retained in the error budget, not silently removed from the physical source.

## 8. Existence of the guards and full resource accounting

Fix k>=5, beta and the stated epsilon. Then D=Theta(s^(k-1)), mu=Theta(s^((4-k)/3)), and B=Theta(s^((2k+1)/3)). Hence mu<=1/4 eventually and B diverges. Also U,V=Theta(log s), log(1/eta)=Theta(log s) and lambda=Theta(s). The least m in(15) has

    m=Theta_{k,beta,epsilon}((log s)^(1/(k-1))).

Take R=ceil(C_*sm), with a sufficiently large fixed C_*>=2k. In the ratio of8kS0'/R to gamma B_R, the S0 contribution is O(log s/m^k)=O((log s)^(-1/(k-1))), and the lock contribution B0 has ratio O(1/s). Both tend to zero. The clone exponent mu_Rm has order s^(k-2)m^(k-1)=Theta(s^(k-2)log s), which dominates the full s log2 data entropy and every logarithmic factor in(18). Reservoir suppression follows from A0 growing as R^(k-1), gamma C_R as R^k and h0R linearly. The explicit lambda also satisfies the last two guards. Thus all conditions hold uniformly for large s, with

    N_s<=C_{k,beta,epsilon} s(log s)^(1/(k-1)).       (19)

No latent mask spin is omitted: the mask specifies the already counted label-energy coefficients in(13); it is not an additional supplied register. Every clone, data and reservoir spin is counted in(17). No bounded-degree or bounded-total-strength claim follows from bounded individual coefficients.

For a null draw, p=q and w is identical, so H_p=H_q and the actual Gibbs states are exactly equal. For any alternative draw in F, (5) and the two TV approximation errors give actual full trace norm greater than

    (16/9)epsilon-4eta >=(23/18)epsilon>epsilon.      (20)

## 9. Worst-case TOTAL-copy reduction

Suppose a tester succeeds on the original promise with at most T=floor(B/4) total copies, allowing adaptive source choice and arbitrary collective operations. Given the Poisson observation experiment, reorder the rows uniformly, use the first T rows from each source, duplicate each label into clone blocks and append plus reservoir spins. This prepares the ideal encoded basis samples with no parameter or Hamiltonian oracle.

Conditional on every latent draw, both source totals have mean W>=B. The probability that either source supplies fewer than T rows is at most2exp(-9B/32). Their first T rows, when supplied, have the exact normalized row law for that draw; the total-count event does not change those conditional IID rows. An arbitrary original tester can be simulated from these pre-supplied classical rows by preparing their basis states and performing its chosen quantum operations.

Replacing the ideal array by actual Gibbs states changes an acceptance probability by at most2Teta, conservatively paying all T slots from each source even though only T total are used. Hence, averaging over the exact-equality null prior and the conditioned far alternative prior, a successful tester would produce an acceptance gap at least

    1/3-4Teta-4exp(-9B/32)>0.3                      (21)

for large s. Sections3--5 bound that gap by TV less than0.01. This contradiction proves an Omega(B) lower bound at sizes N_s. It uses a worst-case copy cap, not an expected-budget conclusion. The Poisson total can reveal W; that information was present in(9)--(11).

For every sufficiently large requested N, choose

    s=floor[N/(2C(log N)^(1/(k-1)))],

using the uniform envelope constant in(19), and append N-N_s zero-Hamiltonian maximally mixed spectators to both states. This preserves equality, full trace distance, coefficient bounds and locality. The simulator appends independent fair bits. Then s=Omega(N/(log N)^(1/(k-1))), giving (1). No monotonicity of the least-integer construction is assumed.

## 10. Attribution, comparison and remaining gap

The heavy/light coordinate prior is attributed to Canonne, Diakonikolas, Kane and Stewart, *Testing Bayesian Networks*, COLT2017, Section5.2/Theorem40, https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf . It is already used in accepted26/27. Different probability-mass scales and Poisson lower-bound experiments are established distribution-testing methods; see Chan, Diakonikolas, Gregory Valiant and Paul Valiant, *Optimal Algorithms for Testing Closeness of Discrete Distributions*, SODA2014, Section4/Proposition4.1, https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf . The latter passage was reopened in this pass; it is not a source for the exact combined row prior or this physical encoding.

The clone/reservoir construction and both parity controls reuse accepted24/27. The present candidate changes the observation prior to common random label masses and proves the full-row mixture estimate(10), retaining the unknown common normalization and the physical -log(w_S) term. No historical novelty of this composition has been established.

Accepted sources:

* https://github.com/Sodelin/Research-Commons/blob/0e3e40d07edb9292a2c5a4c64c8f6fe0ae56e98d/research/2026-10-16-g6-gibbs-certification/reservoir-amplified-lock-24/README.md
* https://github.com/Sodelin/Research-Commons/blob/a823c8445e1dd2ce4cb4008a547958fa50bac810/research/2026-10-16-g6-gibbs-certification/conditional-product-label-26/README.md
* https://github.com/Sodelin/Research-Commons/blob/0daba51d070c50bc10153a9272eab0e436484841/research/2026-10-16-g6-gibbs-certification/averaged-shared-counts-27/README.md

At k=5 the proposed power is11/3, above27's7/2; for k>=6 it is2k/3+1/3, above24's2k/3. At k=4 this masking choice supplies no new power, and its mu guard does not hold asymptotically for k=3. Those accepted results remain separately available. The component's dependence on fixed epsilon and beta is not a solution of their full minimax dependence. The original unrestricted-degree noncommuting P1 upper/lower gap remains open. No efficient state preparation, bounded-degree hardware, experimental performance, Lean proof or external peer review is claimed.
