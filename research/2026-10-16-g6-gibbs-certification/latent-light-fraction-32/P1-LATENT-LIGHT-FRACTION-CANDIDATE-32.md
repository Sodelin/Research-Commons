# P1 candidate: a shared latent light fraction suppresses two-copy information

18 October 2026. Author: dot (OpenAI), working with Nolan.

**Producing-pass hand-proof candidate; not accepted or published.** The proposed improvement requires review of the full statistical and physical argument below. It is not a full P1 solution, an external peer-review claim, a Lean proof or a historical-novelty claim.

## 1. Proposed claim and original experiment

Fix an integer k>=5, beta>0, and fixed 0<epsilon<=1/4096. For all sufficiently large physical sizes N, the proposed lower bound for the original P1 problem is

    Omega_{k,beta,epsilon}(N^a_k / (log N)^(a_k/(k-1))),
    a_k=min{(2k+2)/3,(4k-1)/5}.                    (1)

Thus a_5=19/5, a_6=23/5, and a_k=(2k+2)/3 for k>=7. This would improve component29's power (2k+1)/3 in this stated accuracy range. It does not close the general upper/lower gap or the full dependence on beta and epsilon. No new k=3 or k=4 statement is proposed.

The experiment is equality versus FULL trace norm at least epsilon for two unknown N-qubit Gibbs states at the same known beta. Their Hamiltonians are k-local Hermitian Pauli sums, with every nonidentity Pauli coefficient at most one in magnitude. Degree and per-site total strength are unrestricted. The tester may use arbitrary collective operations and adaptive source choice, but has a worst-case TOTAL copy budget across both sources. The construction below is a diagonal subclass.

The change from component29 is statistical. At each label there is one shared latent Beta(3,3) light-coordinate fraction, and each coordinate has an independent shared random bit flip. The latent fraction is held fixed across every copy at its label. It makes coordinates correlated after it is averaged out. No exact second-moment matching is claimed.

## 2. Full latent prior and normalized row states

Let s be sufficiently large, r=k-1, D=binom(s,r), and set

    alpha=2048 epsilon<=1/2, ell=1/s, delta=alpha/s,
    c0=2^(-20),
    mu=c0 min{[s^4/(alpha^4 D)]^(1/3),
               [s^3/(alpha^4 D)]^(1/5)},
    B=Dmu.                                         (2)

Eventually 0<mu<=1/4 and B diverges. A complete row is a visible size-r subset S of [s] and s binary data values. Independently at each label draw:

1. A mass type R_S~Bernoulli(mu). Its raw weight is w_S=1 if R_S=1, and w_S=mu otherwise. R_S=0 labels are signal labels.
2. A light fraction theta_S with density f(theta)=30 theta^2(1-theta)^2 on [0,1].
3. Conditional on theta_S, independent coordinate types C_(S,j)~Bernoulli(theta_S), with 1 meaning light.
4. Independent signs U_(S,j) and sigma_(S,j), each uniform in {+1,-1}.

Every variable is drawn ONCE before all observations. theta_S is shared by all coordinates at S and by both sources. The signs are likewise fixed for all repetitions of their coordinate.

Before applying U, a heavy coordinate has p=q=1/2 under both hypotheses. A light coordinate has:

- Null, every label: p=q=ell.
- Alternative, R_S=1: p=q=ell.
- Alternative, R_S=0: p=ell+sigma delta and q=ell-sigma delta.

When U=-1, replace both probabilities by their complements. This is one common bit flip; it does not change the conditional pair's L1 distance. The resulting probabilities all lie in [1/(2s),1-1/(2s)].

Put H=sum_S R_S and W=Dmu+(1-mu)H. The actual normalized row law of the first source is

    P(S,y)=(w_S/W) product_j p_(S,j)^y_j
                                  (1-p_(S,j))^(1-y_j),

and Q uses q with exactly the same label weights and W. Every null draw has P=Q exactly. The mass-mask and normalization distributions are the same under both unconditioned hypotheses. No normalization is replaced by its prior expectation.

## 3. A high-probability globally far alternative event

A label is good if R_S=0, theta_S>=1/2, and it contains at least s/3 light coordinates. Since the Beta law is symmetric, Pr(theta>=1/2)=1/2. Conditional on theta>=1/2, Hoeffding gives

    Pr(number of light coordinates<s/3)<=exp(-s/18).

For large s with exp(-s/18)<=1/3 and mu<=1/4, each label is good with probability at least 1/4. Labels are independent before conditioning. Let J be the number of good labels, and define

    F={J>=D/8 and H<=2B}.

Chernoff and a union bound give

    Pr(F^c)<=exp(-D/32)+exp(-B/3)=:zeta_s ->0.        (3)

At a good signal label, at least s/6 light coordinates have the same sigma. Undo the common coordinate bit flips only for the mathematical distance calculation. On that group of j coordinates, j>=s/6, the all-zero event probability difference is at least

    (1-ell+delta)^j-(1-ell-delta)^j
      >=2j delta(1-ell-delta)^(j-1)
      >=(alpha/3)exp(-3).

Full conditional L1 distance is twice at least this event difference, hence strictly greater than alpha/48. On F, W<=3B and good labels have total normalized mass at least

    (D/8)mu/(3B)=1/24.

Orthogonality of labels therefore gives

    ||P-Q||_1>alpha/1152=(16/9)epsilon.              (4)

Only the alternative prior will be conditioned on F, after the complete observation bound. Conditioning changes its observation law by TV at most zeta_s. No coordinate independence after conditioning is assumed.

## 4. Complete observation law and conditional coordinate bounds

Given all latent variables, take independent per-label source counts a_S,b_S~Poisson(w_S) and observe that many COMPLETE s-bit rows from each source. Counts, labels and all row groupings are observed. Conditional on its total, each source supplies IID rows from its normalized law P or Q; its total has mean W. This is the same informative raw-Poisson experiment used by component29. The later reduction retains its random total and unknown common W.

For one label, fix the actual count pair (a,b), n=a+b. Conditional on theta, the coordinate priors are independent. Let N_theta be the one-coordinate null data law and A_theta its signal-alternative law, retaining all n repeated observations and the shared U and sigma. Denote

    d_theta(a,b)=chi2(A_theta||N_theta).

The common bit flip gives the two equally weighted orientations of each light coordinate. Let L be their null light law, and M their perturbed light law after averaging sigma. Then

    N_theta=(1-theta)Unif+theta L,
    A_theta=(1-theta)Unif+theta M.

The null uniform component and the same symmetric Taylor remainder as component29 yield

    d_theta <= 4 theta^2/(1-theta)
                delta^4 n^2(n-1)^2 2^n.            (5)

For completeness, use Bernoulli(1/2)^n as reference, v=1/4 and z=ell-1/2. The coefficient of a degree-j centered product in the symmetric perturbation remainder is at most delta^2 j(j-1)(|z|+delta)^(j-2)/2. Orthogonality and x=(|z|+delta)^2/v<=1 give a squared norm at most

    [delta^4/(4v^2)] sum_j binom(n,j)
                       j^2(j-1)^2 x^(j-2)
      <=4delta^4 n^2(n-1)^2 2^n.

Averaging the common bit flip cannot increase that squared norm. Since N_theta>=(1-theta)Unif and A_theta-N_theta=theta(M-L), (5) follows. Endpoint theta=1 has measure zero; its singular bound will be integrated, not used uniformly.

A second bound controls the remaining coordinate product factors. Revealing the heavy/light flag and the bit-flip orientation only for an upper bound, and using convexity over sigma, gives

    d_theta<=theta[(1+y)^n-1],
    y=delta^2/[ell(1-ell)]=alpha^2/(s-1).            (6)

For fixed theta, the entire s-coordinate row experiment has chi-square (1+d_theta)^s-1. From (5), (6), and 2exp(alpha^2)<3,

    chi2(A_theta^tensor s||N_theta^tensor s)
      <=4 theta^2/(1-theta) alpha^4/s^3
                         n^2(n-1)^2 3^n.           (7)

The true row laws integrate one SHARED theta, not independent thetas for the coordinates. Data processing from the experiment that additionally reveals theta gives

    Ddata(a,b):=chi2(integral f A_theta^tensor s
                         ||integral f N_theta^tensor s)
      <=4alpha^4/s^3 n^2(n-1)^2 3^n,               (8)

because E[theta^2/(1-theta)]=30 integral_0^1 theta^4(1-theta)dtheta=1. Bounds (7)–(8) hold for every count pair. Counts n=0,1 give identical laws. The new sharper estimate for n=2 is next.

## 5. Every two-copy allocation has a smaller full-row bound

Write r0=1-2/s and z0=r0^2. Encode a data bit by x in {+1,-1}. For n=2, conditional on theta, each coordinate's null pair density is

    (1+theta z0 x_1 x_2)/4.

After averaging the fixed sigma, the alternative replaces z0 by

    z0+4delta^2 for allocations (2,0) and (0,2),
    z0-4delta^2 for allocation (1,1).

These statements include the common fixed U sign. Define the entire pair-row law

    g_z(x)=integral_0^1 f(theta) Q_(theta z)(x)dtheta,
    Q_v(x)=product_(j=1)^s (1+v x_(1,j)x_(2,j))/4.

Thus Ddata is chi2(g_z||g_z0) for the indicated z. The integration boundary terms vanish since theta f(theta) is zero at both endpoints. Differentiating the finite polynomial kernel and integrating by parts gives

    g'_z=-(1/z) integral (theta f(theta))' Q_(theta z)dtheta.

Let h(theta)=(theta f)'/f=(3-5theta)/(1-theta). Its exact second moment is

    E h^2=30 integral_0^1 theta^2(3-5theta)^2 dtheta=15.

Weighted Cauchy–Schwarz, followed by summing the normalized kernel over x, proves

    sum_x (g'_z(x))^2/g_z(x) <=15/z^2.              (9)

For s>=8 and alpha<=1/2, all z between z0-4delta^2 and z0+4delta^2 obey z>=1/2 and 1-z>=3/s. Pointwise likelihood ratios satisfy

    Q_(theta z)/Q_(theta z0)
      <=[1+s|z-z0|/3]^s
      <=exp(4alpha^2/3)<2.

The same bound holds for g_z/g_z0. Therefore (9) implies

    sum_x (g'_z(x))^2/g_z0(x)<=120.

Integrating this derivative in the fixed weighted L2 norm yields the full-row estimate

    Ddata(a,b)<=120(4delta^2)^2
               =1920alpha^4/s^4,    n=2.            (10)

No exact matching is asserted: the three allocations have different signs of their small correlation shift. The common latent fraction provides a continuous nuisance distribution with a finite score bound. Coordinates are correlated after theta is integrated, which is precisely why independent-coordinate chi-square multiplication is not used in (10).

## 6. Shared mass denominator and all counts

Put C_lambda(a,b)=exp(-2lambda)lambda^(a+b)/(a!b!). Let Ndata and Adata be the full theta-integrated row data laws from Section 4. At each label the complete null and alternative count/data densities are

    N=[mu C_1+(1-mu)C_mu] Ndata,
    A=mu C_1 Ndata+(1-mu)C_mu Adata.

The same latent mass type is shared by both sources and all data coordinates. Retaining the exact denominator gives

    chi2(A||N)
      =sum_(a,b) [(1-mu)^2 C_mu^2
                    /(mu C_1+(1-mu)C_mu)] Ddata(a,b)
      <= exp(2-4mu+2mu^2)/mu
                    E_(a,b IID Poisson(mu^2)) Ddata(a,b).  (11)

Let n=a+b~Poisson(2mu^2). The n=2 contribution, using (10), is at most

    3840 exp(2-4mu) alpha^4 mu^3/s^4
      <=30720 alpha^4 mu^3/s^4.                    (12)

For n>=3 use (8). The falling-factorial identity is

    n^2(n-1)^2=(n)_4+4(n)_3+2(n)_2.

The exact full expectation of this polynomial times 3^n is

    exp(4mu^2)[1296mu^8+864mu^6+72mu^4].

The n=2 term is 72mu^4 exp(-2mu^2). Thus, since 1-exp(-6mu^2)<=6mu^2,

    E[n^2(n-1)^2 3^n 1_(n>=3)]
      <=exp(4mu^2)[1296mu^8+1296mu^6]
      <=1377mu^6 exp(4mu^2),     mu<=1/4.

Its contribution in (11) is at most

    44064 alpha^4 mu^5/s^3.

Together,

    chi2(A||N)<=65536 alpha^4
                         (mu^3/s^4+mu^5/s^3).      (13)

This is a complete count/data bound. It does not replace common row counts with coordinate clocks, truncate an uncontrolled tail, or discard normalization information.

The unconditioned experiments are independent across labels. By (2),

    D chi2(A||N)<=2^16(c0^3+c0^5)<2^(-43).

Consequently full unconditioned chi-square is below 2^(-42), and TV is below 2^(-21). Conditioning the alternative on F costs at most zeta_s from (3). These bounds preserve both actual random total counts and the common unknown W.

## 7. Fixed-beta physical admission and all spin costs

Use the accepted [admission30](https://github.com/Sodelin/Research-Commons/blob/75077b740d7a6c44aee69cbd776aea5e26a43014/research/2026-10-16-g6-gibbs-certification/conditional-qubit-admission-30/README.md) for this diagonal special case. Choose one prescribed leakage eta=1/(100B), eventually eta<=epsilon/8. To satisfy its maximum-one convention use w'_S=w_S/max_T w_T. This leaves normalized label probabilities unchanged. If H=0 all w'_S=1; otherwise w'_S=w_S. Since mu is inverse polynomial for fixed parameters, one fixed class exponent C gives w'_S>=s^(-C) eventually.

The conditional qubits have eigenvalues p,1-p in [1/(2s),1-1/(2s)]. Common guards use U*=C log s, V*=2log(2s), and the same eta for both sources and every latent draw. All clone and reservoir sizes are source independent. The isometry appends the known label/clone and plus-reservoir registers; it does not need theta, the types, the signs, or the Hamiltonian coefficients.

The resulting Hamiltonians have locality at most k, every nonidentity Pauli coefficient bounded by one, and the common fixed beta. They are diagonal in this subclass. Total size, including every clone, data and reservoir spin, satisfies

    N_s=sm+s+R<=C_* s(log s)^(1/(k-1)).             (14)

The physical Gibbs state is within full trace norm 2eta of the common ideal encoding, uniformly in every unconditioned draw. The same parameters under the null produce exactly the same Hamiltonian. On F, the physical full trace separation is greater than

    (16/9)epsilon-4eta >=(23/18)epsilon>epsilon.     (15)

The new theta and U draws are parameters used to sample the already counted Hamiltonian coefficients, not additional free or omitted physical registers. No bounded-degree, bounded-total-strength, efficient-preparation, or hardware claim is made.

## 8. Worst-case total-copy reduction

Suppose a tester for the original physical promise succeeds with at most T=floor(B/4) TOTAL copies, allowing adaptive source choices and arbitrary collective operations. Given the complete Poisson experiment of Section 4, uniformly restore within-source ordering and supply the first T rows from each source, when present. Each source total is Poisson(W), with W>=B. The probability of either supply failure is at most 2exp(-9B/32).

Conditional on any fixed latent draw and on a source total, its ordered rows are IID from its actual normalized row law. Thus the first T rows, when available, have the required ideal normalized law; no knowledge of W is used by the simulator. Preparing the classical rows as computational-basis states and applying the common encoding implements ideal inputs. Adaptive source allocation is supported by the two arrays. The original tester still consumes at most T total copies; provisioning T slots for each source is only a conservative comparison device.

Replacing both ideal arrays by actual physical Gibbs arrays changes any acceptance probability by at most 2Teta. Comparing the null and conditioned alternative and paying both supply failures, the tester would therefore yield an acceptance gap at least

    1/3-4Teta-4exp(-9B/32)>0.3

eventually. But (13) bounds the complete prior observation TV by 2^(-21)+zeta_s<0.01 eventually. This contradiction proves an Omega(B) lower bound at sizes N_s. It is a worst-case-copy result, not an expected-budget result. All informative counts and both normalization distributions were included before the reduction.

## 9. Exponents, every sufficiently large size, and comparison

For fixed k>=5, beta, epsilon,

    B=Theta(min{s^(4/3)D^(2/3),s^(3/5)D^(4/5)})
      =Theta(s^a_k).

The second term is limiting for k=5,6; the first for k>=7. Both are needed: the first controls total count two, the second the complete higher-count contribution. The latter cannot be dropped just because typical counts are small.

Using the uniform constant in (14), for any sufficiently large requested N choose

    s=floor[N/(2C_*(log N)^(1/(k-1)))].

Then N_s<=N and s=Omega(N/(log N)^(1/(k-1))). Add N-N_s zero-Hamiltonian maximally mixed spectators to both states. Equality, full trace norm, beta, locality and coefficient bounds are preserved; the simulator generates the independent fair spectator bits. This establishes (1) for every sufficiently large N without assuming monotonicity of the least-integer guards.

At k=5, the proposed order is N^(19/5)/(log N)^(19/20), compared with29's N^(11/3)/(log N)^(11/12). At k=6 it is N^(23/5)/(log N)^(23/25), compared with N^(13/3)/(log N)^(13/15). For k>=7, the proposed power improves by 1/3. These comparisons hold in the present fixed-parameter accuracy range; they do not resolve the full P1 minimax dependence or its gap to the general collective upper.

## 10. Attribution and verification limits

The heavy/light rare-coordinate prior, symmetric sign perturbation, and product-distribution likelihood method descend from Canonne, Diakonikolas, Kane and Stewart, *Testing Bayesian Networks*, COLT 2017, Section 5.2/Theorem40: https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf . They were already used in components26–29. The shared random masses and their exact denominator are from [component29](https://github.com/Sodelin/Research-Commons/blob/603e52474aa12a2b7f0131a02e6508249d9dc616/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/P1-RANDOM-LABEL-MASS-CANDIDATE-29.md). Its notes also credit the distribution-testing mass constructions of Chan, Diakonikolas, Gregory Valiant and Paul Valiant, SODA2014.

The new proposed composition adds one shared Beta light fraction and random coordinate flips, uses its finite integration-by-parts score to improve the full two-copy row bound, and retains a separate rigorous all-count remainder. Integration by parts, score-information bounds, data processing, Poissonization and tensor chi-square identities are classical tools. No historical novelty of this composition has been established.

Physical admission is reused from30 and its source ancestry, with all common guards and registers counted. It is not a new physical encoding claim. Prior ceilings29A–C apply to their specified fixed conditional alphabets and resource relations; this prior changes the conditional-law structure and has correlated coordinates after latent averaging. Exclusion31 concerns a different angular prior and is unchanged.

This document remains a candidate until the full argument is reviewed. A finite symbolic check can verify the displayed scalar identities but cannot replace the parameterized proof or the physical reduction. No external peer review, Lean verification or full P1 closure is claimed.
