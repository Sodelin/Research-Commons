# Fixed-beta shell encoding at every fixed interaction order

16 October 2026. Attributed hand-proof candidate by dot (OpenAI) for Nolan. Status: awaiting independent review. This extends the reviewed two-local shell construction18 and all-size padding19, using a higher-order reservoir. It imports classical closeness-testing hardness; no novelty, implementation, experiment, Lean verification or P1 closure is claimed.

## 1. Original experiment and proposed conclusion

Fix an integer k>=2 and known beta>0. The original source class consists of two unknown N-qubit Gibbs states at that same beta, with locality at most k and every nonidentity Pauli coefficient individually bounded by one. There is no inherited bounded-degree or per-site interaction-sum condition. The promise is equality versus full trace-norm separation at least epsilon; the budget is worst-case TOTAL copies, including adaptive allocation and arbitrary collective measurements.

For logical s>=2k, let D=binom(s,k), 0<epsilon<=1/4,

    L=max{D^(2/3)/epsilon^(4/3), sqrt(D)/epsilon^2},
    eta=1/(100L).

The construction below uses N_s=sm+R qubits and imports an Omega(L) lower bound. Its explicit parameter inequalities are feasible with

    m=O_{beta,k}(log(s/eta)),
    R=O_{beta,k}(s log(s/eta)^(1/k)+log(s/eta)),
    N_s=O_{beta,k}(s log(s/eta)).

Consequently, at any fixed admitted accuracy epsilon and fixed beta,k, every sufficiently large physical N has lower bound

    Omega_{beta,k,epsilon}(N^(2k/3)/(log N)^(2k/3)).

The epsilon dependence in the last display is not uniform: the preceding construction is the explicit accuracy-dependent statement. This improves the previously recorded dense n^(k/2) exponent at fixed k>=3 and constant accuracy if accepted. It leaves a gap to the general collective upper. Growing degree and per-site energy are essential permissions of the source class, not a bounded-strength thermodynamic limit.

## 2. Positive shell energy and clone leakage

For an arbitrary distribution p on k-subsets S of [s], put pbar=(3/4)p+(1/4)U_D, v_S=-log pbar_S, V=log(4D). Thus 0<=v_S<=V. Each logical site has m physical bits; w_i is its number of ones and x_i=w_i/m. Choose

    lambda=16(k+1)log(2s/eta), mu=beta/4,
    E_p(x)=lambda(sum_i x_i-k)^2 + sum_{|S|=k}v_S product_{i in S}x_i,
    J_p=E_p+mu sum_i w_i(m-w_i).

All displayed summands are nonnegative. On constant blocks of logical weight k, exactly one signal monomial survives, so the shell partition equals sum_S exp(-v_S)=1, with conditional distribution pbar.

Choose an integer m satisfying

    m>=2, m>=8lambda/beta, m>=8V/beta,
    mu m^2>=32log(2s),
    sm exp(-mu m/4)<=1,
    4s^(k+1)m exp(-mu m/4)<=eta/4.

Such a choice has the stated logarithmic bound. Constant-block states of weight w!=k have total partition at most

    2s^k sum_{a>=1}s^a exp(-lambda a)
      =2s^(k+1)exp(-lambda)/(1-s exp(-lambda))<=eta/4.

For a nonconstant configuration, round each block to its nearer constant value with a fixed tie rule. Let w be the rounded weight and q=sum_i min(w_i,m-w_i)>=1. The number with fixed rounded string and q is at most binom(sm,q). Moreover |sum x_i-w|<=q/m and the lock energy is at least mu m q/2. Splitting that bound in half, with a=|w-k|, yields

    J_p>=mu m q/4+g(a),
    g(a)=min{lambda a^2/4,mu m^2 a/8}.

Indeed if q<ma/2 the square supplies the first alternative, while otherwise the second half of the lock supplies the second. For a>=1, g(a)>=4a log(2s). Therefore

    sum_w binom(s,w) exp(-g(|w-k|))<=2s^k.

The total nonconstant partition is at most

    2s^k[exp(sm exp(-mu m/4))-1]
      <=4s^(k+1)m exp(-mu m/4)<=eta/4.

Thus the distribution proportional to exp(-J_p) is within TV eta/2 of the ideal constant-block shell distribution. These estimates retain logical-weight suppression and hold uniformly in p.

## 3. Pauli expansion and reservoir distribution of coefficients

Write physical spins z_j=1-2y_j. Expand

    J_p=c_p+K_lock(z)+sum_{1<=|A|<=k}h_A z_A,

where K_lock consists of within-block pair coefficients -mu/2; h_A are the nonconstant Pauli coefficients of E_p. In particular K_lock(-z)=K_lock(z). Let

    S0=lambda(s+k)^2+D V.

The triangle inequality for coefficient l1 norms gives sum_A|h_A|<=S0: each block average x_i has coefficient l1 norm one, and sum_i x_i-k has coefficient l1 norm at most s+k.

For an A of size a in distinct logical blocks, the signal part satisfies

    |h_A^signal|<=2^(-k)m^(-a)binom(s-a,k-a)V.

It vanishes if A repeats a logical block. The penalty contributes only fields -lambda(s-2k)/(2m) and pair coefficients lambda/(2m^2).

Introduce R distinct reservoir spins a_l. Define e_r(a) as the average of products over all r-subsets of these spins, with e_0=1. Replace the E_p polynomial by

    W_p(z,a)=sum_A h_A z_A e_{k-|A|}(a).

At the all-plus reservoir, W_p=sum_A h_A z_A exactly. Each summand is a k-body Pauli interaction on distinct sites; the coefficient for a fixed logical A and reservoir subset is h_A/binom(R,k-|A|). No different A contributes to that same physical Pauli support.

Take R>=2ks and R>=4k. For r=k-a>0, binom(R,r)>=(R/r)^r>=s^r; for r=0 its value is one. Consequently every distributed signal coefficient is at most V/(2^k m^a)<=beta/8. Since s>=2k, the distributed penalty field is at most lambda/(m s^(k-2))<=beta/8, and its pair coefficient is at most lambda/(2m^2)<=beta/16. Combined h_A coefficients are at most beta/4. For k=2 only, a penalty pair can also coincide with a lock pair; their combined magnitude is at most beta/4+mu/2=3beta/8. For k>2 the lock pair has different degree. This verifies coefficients rather than inferring admission from a formal energy expression.

## 4. Finite higher-order reservoir estimate

Set gamma=h0=beta/4 and define the full dimensionless energy

    Q_p(z,a)=K_lock(z)+W_p(z,a)
               -gamma sum_{|S|=k}a_S-h0 sum_l a_l.

All remaining reservoir coefficients are gamma or h0; supports are distinct from those in Section3. Thus H_p=Q_p/beta, after dropping an identity term, is admitted with locality at most k and every nonidentity coefficient bounded by one.

Let b=floor(R/2), B=binom(b,k-1), C=binom(b,k), and A0=gamma B. In addition to the preceding size bounds, choose R to satisfy

    8k S0/R<=gamma B, 4h0<=gamma B,
    R exp(-A0)<=1, 2R exp(-A0)<=eta/32,
    exp(-2h0R)<=eta/8,
    2^R exp(-gamma C)<=eta/16.

All are finite explicit inequalities depending only on s,k,beta,epsilon. Since B is bounded below by a positive k-dependent constant times R^(k-1), and C by such a constant times R^k, they permit the stated R bound. In particular S0=O_k(s^k log(s/eta)); a sufficiently large constant multiple of s log(s/eta)^(1/k)+log(s/eta) meets every inequality. The last inequality is needed only for odd k, but imposing it in both cases is harmless.

For a reservoir with l minus spins, let O_k(l) count its k-subsets with an odd number of minus spins. Relative to all plus, the reservoir interaction cost is exactly 2gamma O_k(l). If 1<=l<=R/2, counting subsets with exactly one minus gives

    O_k(l)>=l binom(R-l,k-1)>=l B.

Also |e_r(a)-1|<=2rl/R, since the product differs from one only if a uniformly chosen r-subset meets the minus set. Hence

    |W_p(z,a)-W_p(z,+)|<=2k l S0/R.

The same-z full energy difference from all plus is at least A0 l, using the inequalities above and the favorable field cost 2h0l. This is pointwise in z and uniform in p.

### Even k: exact two-phase identity

For even k, O_k(l)=O_k(R-l). Near all minus, put q=R-l. The corresponding W change is bounded by 2k q S0/R, while the field can lower energy by 2h0q. Thus the energy above all minus is at least

    2gamma qB-2k qS0/R-2h0q>=A0q.

At all minus, e_{k-|A|}=(-1)^|A|, so W_p(z,-)=W_p(-z,+). Together with K_lock(-z)=K_lock(z), global logical spin flip proves the exact partition identity Z_-=exp(-2h0R)Z_+. This does not assume a sign for the h_A.

Summing near either phase over subsets gives mixed partition at most

    (Z_++Z_-)[exp(R exp(-A0))-1]
       <=(Z_++Z_-)2R exp(-A0).

Double counting the middle layer is harmless. Total non-plus partition divided by Z_+ is at most eta/8+(1+eta/8)eta/32<eta/4.

### Odd k: direct suppression of the far phase

For l>R/2, the all-minus k-subsets alone give O_k(l)>=binom(l,k)>=C. The W change is at most 2S0 and the field cost is nonnegative. As R>=4k,

    C/B=(b-k+1)/k>=R/(4k),

and the imposed strength bound gives gamma C>=2S0. Therefore the same-z energy difference from all plus is at least 2gamma C-2S0>=gamma C. Summing all such reservoir strings gives relative partition at most 2^R exp(-gamma C)<=eta/16. The near-plus strings contribute at most 2R exp(-A0)<=eta/32. Total non-plus relative partition is therefore less than eta/4.

In either parity, conditioning on the plus reservoir gives exactly exp(-J_p)/Z_J, because Q_p(z,+)=J_p(z)-c_p plus a z-independent reservoir constant. The full Gibbs state is within TV eta/4 of that conditional state with pinned reservoir. Section2 then gives TV less than eta from the ideal encoded pbar with all reservoir spins plus.

## 5. Prior lower bound and sample-only transfer

The supplier is Chan, Diakonikolas, Gregory Valiant and Paul Valiant, SODA2014, Theorem1.1: two-unknown D-symbol equality versus L1 distance at least 2epsilon needs Omega(L) samples at constant error. The primary theorem was reread on16October2026: https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf (PDF page2), also https://arxiv.org/abs/1308.3946 . This is established classical testing hardness, not a new testing theorem.

If p=q, the constructed actual Gibbs states are identical. If ||p-q||_1>=2epsilon, their ideal encodings have L1 separation at least3epsilon/2, and the actual states have separation at least3epsilon/2-4eta>=epsilon. Explicitly L>=sqrt(D)/epsilon^2>=1/epsilon^2 implies 4eta<=epsilon^2/25<=epsilon/2. All clone and reservoir parameters depend only on the declared s,k,beta,epsilon, never on p.

The ideal encoding uses samples alone: with probability3/4 take a p sample, otherwise a known uniform k-subset, clone its incidence bits, and append plus reservoir spins. It does not request probability values, H_p or a partition-function oracle. The existence of H_p proves admission; the simulator need not evaluate it.

Every state is diagonal in the same known computational basis. Given its basis strings, any collective quantum measurement or adaptive quantum processing is a stochastic postprocessing. Pre-sampling T strings per unknown source simulates every adaptive total-budget-T experiment with at most2T original samples. A sequential hybrid coupling replaces ideal encodings by the admitted Gibbs states with transcript TV at most T eta. For T<=L this is at most1/100; fixed repetition restores a standard constant success probability. The classical lower bound therefore gives T=Omega(L). If T>L the lower bound is automatic. This preserves worst-case total-copy and full-trace-norm conventions.

## 6. All sufficiently large physical sizes and limits

At fixed beta,k,epsilon, the construction supplies N_s<=C_{beta,k,epsilon}s log s for every sufficiently large s, with C>=1. For a requested N take s=floor(N/(2C log N)). For large N, s>=N/(4C log N), s is in the construction range, and N_s<=N/2. Append N-N_s independent zero-Hamiltonian spins. Tensoring with their common maximally mixed state preserves trace norm, equality, admission and the sample-only reduction. Thus the all-N lower bound in Section1 holds without a monotonic-size assumption. This reuses the reviewed padding19 argument.

At fixed accuracy and k>=3 the exponent2k/3 exceeds the dense bound's k/2, while logarithmic overhead remains. This does not give the optimal exponent, an efficient tester, a physical preparation procedure or a bounded-degree result. The general upper and lower still differ. The construction and all calculations here are hand work, unreviewed at publication of this local candidate; no source code was run. Historical priority of the higher-order encoding needs a separate focused prior audit.

## Provenance

- Reviewed shell18: https://github.com/Sodelin/Research-Commons/blob/d459d65df3eeebb6edf5036ff930b1c607a9acf5/research/2026-10-16-g6-gibbs-certification/FIXED-BETA-SHELL-18-INDEPENDENT-REVIEW.md . Original candidate local title FIXED-BETA-CLASSICAL-SHELL-CANDIDATE-18.md; its original bytes and review remain preserved.
- Reviewed padding19: https://github.com/Sodelin/Research-Commons/blob/773ac17b56350f2154bddd191cb74117a52e15c5/research/2026-10-16-g6-gibbs-certification/FIXED-BETA-ALL-SIZES-19-INDEPENDENT-REVIEW.md .
- Full current scope and original P1 experiment: https://github.com/Sodelin/Research-Commons/blob/7a5a5282de68aaa356dec6a8d2591fc12e0c8821/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md .

Separate evidence: hand proof supplied; independent review pending; Lean source/check not performed; Rust implementation and execution not performed; novelty unresolved; General P1 remains OPEN. General P5's fixed-support infinite-Redfield obligation is unchanged.

## Version2 source and convention clarification

The original candidate21, SHA25612636dd2eecab2edab1c0d30be5dfc08e759dc6e7240d4f4e3c3a7087dc233ea, remains unchanged. This successor adds the explicit far-promise margin and this source clarification only.

The classical supplier's Section4, Definition4.1, Theorem4.1 and Proposition4.1, uses balanced sample access from both unknown distributions; Theorem4.1 explicitly states Poisson(k) samples from each. The combined optimal statement used here is Theorem1.1. A worst-case-total-budget T adaptive Gibbs tester can be simulated from T independent samples from each classical source, hence at most2T combined. If its budget were o(L), this would contradict a balanced per-source Omega(L) lower bound just as it contradicts a total Omega(L) convention; the factor two is absorbed. No expected-budget or Hamiltonian-oracle assumption is added.

Overlap with18 is deliberate: smoothing, positive shell energy, two-body clone locking, logical-weight/defect counting, sample-only reduction and the even-phase flip principle are reused. The added construction distributes every nonconstant logical Pauli coefficient over distinct reservoir supports to degree k and uses a k-body reservoir, including the direct odd-parity far-phase estimate. It is this combination that avoids the two-body reservoir's polynomial overhead at k>2. Padding is exactly the accepted19 method.

A bounded prior check also inspected De las Cuevas and Cubitt, Simple universal models capture all classical spin physics (https://discovery.ucl.ac.uk/1477525/1/UH-combined.pdf), Definition1 and Theorem15/its displayed overhead. Hamiltonian simulation, auxiliary spins and partition-function approximation are established techniques. The inspected statement permits real coupling strengths and polynomial overhead in the number of target interactions; it is not itself the near-linear-spin, fixed-beta, unit-coefficient, sample-only reduction proved here. This difference is an applicability check, not a priority claim. Bezáková et al., JMLR21(2020), Theorem1 and its model definition (https://www.jmlr.org/papers/volume21/19-580/19-580.pdf), concerns conditional computational hardness with a specified reference model; it cannot be substituted for this unconditional two-unknown copy lower bound. Historical novelty remains unresolved.
