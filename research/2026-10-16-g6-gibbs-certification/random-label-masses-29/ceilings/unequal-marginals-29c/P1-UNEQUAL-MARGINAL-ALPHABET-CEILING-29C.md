# P1 route boundary: unequal label marginals with the same conditional alphabet

17 October 2026, 23:24 UTC. Author: dot (OpenAI), working with Nolan.

Status: new hand-proof candidate for coordinating review. The published29 and29A/B packets are unchanged. This is a specialized testing ceiling, not an upper bound for arbitrary Gibbs states, an improved lower bound, a historical-novelty claim, or a Lean proof.

## 1. Exact class, question and claim

Let D>=2, s>=3, 0<epsilon<=alpha<=1/2 be known. Put ell=1/s, h=1/2, delta=alpha/s. Each source returns a visible label i in[D] and a complete string of s bits. The sources have arbitrary UNKNOWN label distributions pi and nu, which need not be equal and may contain zeros. Conditional on a label, the bits are independent. Write the two conditional product laws as P_i and Q_i.

For every coordinate, its pair of Bernoulli parameters belongs to the SAME alphabet as29B:

* (h,h);
* (ell,ell);
* (ell+sigma delta,ell-sigma delta), sigma in{+1,-1}.

On labels with zero source mass, conditional parameters can be assigned any values satisfying this contract; they are not given to the tester. Labels, all bits and their row grouping are observed, with ordinary IID sampling and no conditional oracle.

The promise is now just exact equality P=Q versus FULL L1 distance ||P-Q||_1>=epsilon. There is no separately assumed signal-label set or lower bound on its overlap mass. The claim is a tester with worst-case total ideal-row cost

    804 m + 8 n,

where m is the imported marginal-testing budget defined in Section3 and

    a=epsilon/(16alpha), L=ceil(32 log(D+2)), C=10^4,
    n=ceil(C s D^(2/3) L^(2/3)/(a^2 alpha^(4/3))).       (1)

Assume n<=DL. Its error is at most

    1/100 + 4exp(-n/3) + D/(D+2)^4
      + exp(-a^2 n^2/(288DL)) + 10368/C^3.              (2)

For fixed epsilon,alpha and D=binom(s,k-1), fixed k>=5, all the conditions hold for sufficiently large s and(2) is below1/3. The order is

    O_{epsilon,alpha}(s D^(2/3)(log(D+2))^(2/3)).         (3)

This extends the polynomial ceiling to unequal marginals and the full L1 promise, while retaining the specified conditional alphabet. It does not extend it to arbitrary unknown conditional means or arbitrary noncommuting states. Physical-size consequences additionally require the label-capacity and extraction conditions in Section7.

## 2. Full L1 separation supplies an overlap signal

Let d=||pi-nu||_1, w_i=min(pi_i,nu_i), and let b_i be the number of differing-light coordinates at label i. Decomposing each label into common mass and an excess mass gives

    ||P-Q||_1 <= d + sum_i w_i ||P_i-Q_i||_1
               <= d + 4delta sum_i w_i b_i.            (4)

The first inequality follows from the triangle inequality. For example, if pi_i>=nu_i, write pi_i P_i-nu_i Q_i=(pi_i-nu_i)P_i+nu_i(P_i-Q_i). The second follows by independent coordinate coupling, or telescoping the product: the Bernoulli full L1 difference of ell+delta and ell-delta is4delta. The factor4 retains the full-L1 convention.

If ||P-Q||_1>=epsilon and d<epsilon/2, then

    sum_i w_i b_i/s >= epsilon/(8alpha)=2a.             (5)

Define J={i: b_i/s>=a}. Because sum_i w_i<=1 and b_i/s<=1, the contribution outside J is at most a. Thus

    b_i>=a s for i in J,
    sum_(i in J) w_i >=a.                              (6)

J and all these unknown masses are analysis devices, not inputs. In the regime d>=epsilon/2, the separate marginal test supplies the alternative guarantee instead. No tolerant guarantee for that test is used in the regime d<epsilon/2.

## 3. The marginal test: exact imported supplier and fixed budget

Use Chan, Diakonikolas, Valiant and Valiant, *Optimal Algorithms for Testing Closeness of Discrete Distributions*, SODA2014, Theorem1.1 and Proposition2.1. The source gives success at least2/3 for equality versus L1 separation at least t from Poisson(m) observations of each distribution when

    m>=C_0 max(D^(2/3)/t^(4/3),sqrt(D)/t^2),

for an absolute constant C_0. Its sample model and Poissonization convention are on PDF pages2--3. The exact theorem and those passages were inspected in this pass; no new audit of the entire paper is claimed.

    https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf
    https://doi.org/10.1137/1.9781611973402.88

Set t=epsilon/3 and choose integer m at least100 and the displayed sufficient bound. The numerical value of C_0 is inherited from that theorem, not newly extracted here. Amplify with201 independent runs. In each run draw both internal Poisson counts before querying samples, and abort that run if either exceeds2m. The added error is at most2exp(-m/3)<1/1000. Each run's success is therefore at least2/3-1/1000>1/2+4/25. A majority fails with probability at most exp[-2*201*(4/25)^2]<1/100. Its worst-case total budget is804m ideal rows. The test reads only their labels.

Under P=Q, pi=nu, so the marginal null holds. If d>=epsilon/2, then d>t and the marginal alternative holds. For0<d<epsilon/2 its output may be arbitrary: rejection is already correct, and the separate conditional test covers acceptance. Run the latter on independent samples and reject if either test rejects.

## 4. A pooled pilot flattens BOTH unknown marginals

Generate independent internal Poisson(n) counts for a pilot from each source, checking each against2n before any samples in that batch are queried. Abort the conditional test if a cap is exceeded. In the untruncated analysis the counts A_i^P,A_i^Q are independent Poisson(n pi_i), Poisson(n nu_i). Put

    A_i=A_i^P+A_i^Q, K_i=L+2A_i.

Every subsequent row with label i receives an independent uniformly random index j in[K_i]. Both sources use the same observed pilot and this same rule. The enlarged label(i,j) is ordinary classical postprocessing, not an auxiliary physical spin or a conditional-sampling oracle.

Let E be the event that both pilot totals are at most2n and K_i>=n(pi_i+nu_i) for every i. If n(pi_i+nu_i)<=L the last condition is automatic. Otherwise failure implies A_i<n(pi_i+nu_i)/2, whose probability is at most exp[-n(pi_i+nu_i)/8]<=exp(-L/8). Hence

    Pr(E^c)<=2exp(-n/3)+Dexp(-L/8).

On E,

    sum_i K_i<=DL+8n<=9DL,
    n pi_i/K_i<=1,  n nu_i/K_i<=1.                    (7)

The unknown inequalities in E are never tested by the procedure. A separate expectation bound, used without conditioning on E, is

    E[1/K_i] <= E[1/(1+A_i)]
                <= 1/[n(pi_i+nu_i)]                 (8)

when pi_i+nu_i>0. This is the exact Poisson reciprocal-count identity; zero-mass terms contribute zero.

## 5. Paired statistic, overlap collisions and variance

Generate independent fresh Poisson(n) batches from both sources, again drawing and checking each internal total against2n BEFORE querying its rows. Conditional on the pilot, the two counts at enlarged label(i,j) are independent Poisson variables with means

    u_i=n pi_i/K_i, v_i=n nu_i/K_i.

Use the first row from each source only when both are present. For a paired coordinate define the existing statistic

    f(X,Y)=XY-(h+ell)(X+Y)/2+h ell.

It has absolute value at most1, expectation0 on equal alphabet coordinates and expectation -delta^2 on differing coordinates. Let Z sum f over all coordinates of all selected row pairs; K is the number of selected enlarged labels, and K_J counts selected enlarged labels whose original labels belong to J. Conditional on the pilot, counts and fixed source parameters, selected rows are disjoint and the coordinates within each row are independent. Therefore

    Var(Z | pilot,counts)<=sK,
    E[Z | pilot,counts]=0 on a null,
    E[Z | pilot,counts]<=-a alpha^2 K_J/s             (9)

on alternatives covered by(6). Differing coordinates outside J have nonpositive mean and cannot cancel the signal. A full row pair, rather than an independent clock per coordinate, is retained throughout.

On E, u_i,v_i<=1 and the probability that both counts are positive is at least u_i v_i/4. Cauchy--Schwarz and sqrt(pi_i nu_i)>=w_i give

    E[K_J | pilot]
       >=n^2/4 sum_(i in J) pi_i nu_i/K_i
       >=n^2/4 (sum_(i in J) sqrt(pi_i nu_i))^2
                    /(sum_(i in J) K_i)
       >=a^2 n^2/(36DL)=:m_0.                       (10)

Enlarged-label occupancies are independent conditional on the pilot. Thus

    Pr(K_J<m_0/2 | pilot in E)
       <=exp(-m_0/8)=exp[-a^2 n^2/(288DL)].          (11)

For the variance, do NOT condition(8) on E. Since(1-exp(-u))(1-exp(-v))<=uv,

    E[K | pilot]<=n^2 sum_i pi_i nu_i/K_i,
    E K<=n sum_i pi_i nu_i/(pi_i+nu_i)<=n/2.         (12)

The last step uses4pi_i nu_i<=(pi_i+nu_i)^2 and sums pi and nu to one. Let V=Z-E[Z|pilot,counts]. Then E V^2<=sn/2. Set

    tau=a alpha^2 m_0/(4s)
        =a^3 alpha^2 n^2/(144sDL).

Reject when Z<-tau. On a null its conditional mean is zero. On the alternative event(11), its conditional mean is at most-2tau. Markov applied to V^2 gives the common noise error

    sn/(2tau^2)
      =10368 s^3 D^2 L^2/(a^6 alpha^4 n^3)
      <=10368/C^3 < 1.1*10^(-8).                   (13)

This centers noise before averaging; it does not replace a random alternative conditional mean by its overall mean. Four observable Poisson caps cost at most4exp(-n/3). Combining(7),(11),(13), Dexp(-L/8)<=D/(D+2)^4, and the marginal tester proves(2). The conditional stage has four capped batches and total budget8n. Aborts can return either answer; their probability is included in the error bound.

For fixed k>=5 and D=binom(s,k-1), n/(DL) tends to zero and a^2 n^2/(DL) tends to infinity at fixed positive epsilon,alpha. The marginal cost m=O_epsilon(D^(2/3)+sqrt(D)+1) is lower order than n. This establishes(3) in that regime.

## 6. What changes if conditional means are unknown

The proof uses the exact coordinate alphabet, not just product structure. Indeed, for any statistic of one Bernoulli observation X and one Bernoulli observation Y, its expectation has the form

    A pq+B p+C q+D.

If it vanishes for every equal pair p=q=t in an interval, polynomial identity forces A=D=0 and C=-B. Its mean is then B(p-q), which cannot have one strict sign for both(p,q) and(q,p). Thus the particular pointwise one-cross-pair centering used here has no nonzero universally sign-definite replacement for arbitrary means. This is an elementary diagnostic, not a sample lower bound: randomized allocation of source samples or four-observation statistics can evade that restricted statement.

Unknown conditional means, interactions among data bits, or genuinely quantum conditional states require a new statistic or a new lower-prior analysis. Their exclusion from(3) is not evidence that they yield a stronger lower bound. The missing supplier remains an actual admitted family and its complete observation-law bound.

## 7. Physical transfer, resource boundary and prior attribution

The theorem above concerns ideal visible-label rows. To apply it to a Gibbs encoding, separately supply a known measurement and retention event whose conditional output is exactly that row law, with retention at least0.99. The event must be common and source-independent as a rule; its probability may differ between sources. Null equality must imply equal extracted laws.

For the conditional stage take16n physical copies from EACH source. With failure at most2exp(-n), each yields4n retained rows, enough for its two capped batches. Retained values are IID and independent of retention flags. Generate and check the algorithm's internal Poisson requests before consuming those retained values. Add a separate fixed pool for the marginal stage: 8*(402m) physical copies from each source suffice for402m retained rows each, with exponentially small failure, at constant-factor overhead. All copies, including discarded ones and the marginal stage, are counted. No unknown label masses or signal labels are supplied.

If the physical source is within full trace distance2eta of its normalized ideal-sector embedding and eta<=epsilon_phys/8, a physical alternative of distance at least epsilon_phys has ideal L1 distance at least epsilon_phys-4eta>=epsilon_phys/2. Apply the ideal theorem with epsilon=epsilon_phys/2, provided its declared epsilon<=alpha guard holds. This is an additional transfer premise, not a consequence of passivity or of the existence of some Hamiltonian encoding.

The resulting polynomial-exponent ceiling uses D=binom(s,k-1), and the same physical-size relation and uniformly efficient exact extraction as29, or an independently established replacement. A general unequal-marginal statistical ceiling does not restrict arbitrary label-capacity encodings, unknown bases, or the full noncommuting Gibbs class.

The proposed extension uses the classical marginal-closeness theorem cited in Section3, the sample splitting of Diakonikolas--Kane2016 (Definition2.4, Fact2.5, Lemma2.6, PDF pages7--8), and the paired statistic already in27/29A/B:

    https://arxiv.org/pdf/1601.05557v2
    https://github.com/Sodelin/Research-Commons/blob/7de368b2efc7d13458ef757921435e05e1ddb194/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/ceilings/README.md

The new calculation in this draft is the full-L1 overlap reduction and pooled-pilot use for two unequal marginals. Historical novelty is unestablished. The original P1 optimal total-copy problem remains open. No public publication or accepted-register change has been made by this draft.

