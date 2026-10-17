# P1: a weight-two label selecting a product distribution

17 October 2026, 20:51 UTC. Author: dot (OpenAI), working with Nolan.

Status: new hand-proof candidate, awaiting review. No execution or Lean verification is claimed. Historical novelty is unresolved. This is a proposed stronger LOWER-BOUND COMPONENT for the original problem, not a solution of optimal-copy P1.

## 1. Claim and unchanged original experiment

The original experiment supplies independent copies of two unknown N-qubit Gibbs states at a common known fixed inverse temperature beta>0. Hamiltonians are at most k-local in the Pauli basis and every nonidentity Pauli coefficient has absolute value at most one. There is no bounded-degree or bounded-total-strength-per-site assumption. The promise is equality versus FULL trace norm at least epsilon, success probability at least 2/3. The budget is the worst-case TOTAL copies from the two sources, and arbitrary collective measurements are allowed.

For k=3, every fixed beta>0 and fixed 0<epsilon<=1/256, this candidate claims, for every sufficiently large N,

    Omega_{beta,epsilon}( N^(9/4)/(log N)^(9/8) ).       (1)

The accepted note24 gives Omega(N^2/(log N)^(2/3)) for k=3. Thus (1), if correct, improves an exponent rather than only auxiliary-spin overhead. The recorded general collective upper remains O(N^3 log N) at fixed parameters. The same hard family belongs to classes k>=3, but this note does not claim it improves the stronger k-specific bounds when k>=4. There is no uniform-in-epsilon overhead claim.

The statistical construction adapts the heavy/light Bernoulli prior in Canonne, Diakonikolas, Kane and Stewart (2017), Section 5.2. It is placed independently behind many observed labels. Because all coordinates of a row share its label, this note proves the needed conditional-count likelihood bound directly. It does not replace the experiment by independent Poisson clocks for individual coordinates. The physical encoding adapts the positive fractional-shell and shared-reservoir construction of accepted notes21 and24, with all data spins and their entropy included.

## 2. Exact row experiment and priors

Let s be an integer, D=binom(s,2), and let the observed label S range over the two-element subsets of [s]. One sample is the COMPLETE row

    (S,Y_1,...,Y_s),

where S is uniform on D labels and, conditional on S, the data bits are independent Bernoulli variables. The two unknown row laws are

    P_p(S,y)=D^(-1) product_j p_{S,j}^{y_j}(1-p_{S,j})^{1-y_j},
    P_q(S,y)=D^(-1) product_j q_{S,j}^{y_j}(1-q_{S,j})^{1-y_j}.

All parameters are drawn ONCE before sampling and stay fixed for every copy.

Set

    alpha=128 epsilon in (0,1/2],
    C0=2000 exp(8), c=(1/(100 C0))^(1/4),
    mu=c (s^3/D)^(1/4)/alpha,
    h=1/mu, ell=1/s, delta=alpha/s.

Take s sufficiently large that 2<=mu<=s and s>=4. For every pair (S,j), independently, use these priors:

* Null prior Y: with probability 1/2 set p=q=h; otherwise set p=q=ell.
* Alternative prior Z: with probability 1/2 set p=q=h; otherwise draw sigma uniformly from {-1,+1} and set p=ell+sigma delta, q=ell-sigma delta.

Every null draw gives EXACTLY equal row laws, not equality only after prior averaging. All probabilities lie in [1/(2s),1/2]. The heavy/light random choices, and the signs on the light choices, are independent across all (S,j). They are shared between the two sources as stated, not redrawn for each sample.

### Separation of alternative draws

For each label the number of light coordinates is Bin(s,1/2). Hoeffding's inequality and a union bound show that the event F on which every label has at least s/3 light coordinates satisfies

    Pr_Z(F^c)<=D exp(-s/18).                              (2)

On F, at each label one of the two signs occurs on at least m0>=s/6 light coordinates. Restrict to those coordinates and consider the event that all are zero. The difference between the two probabilities of that event has magnitude

    (1-ell+delta)^m0-(1-ell-delta)^m0
      >= 2 delta m0 (1-ell-delta)^(m0-1)
      >= (alpha/3) exp(-3).

For the last inequality, m0<=s, alpha<=1/2, s>=3 and

    log(1-3/(2s)) >= -(3/(2s))/(1-3/(2s))

give (1-3/(2s))^(s-1)>=exp(-3). This bound concerns one marginal event, so the conditional FULL L1 distance is at least 2alpha/(3exp(3))>alpha/48. Uniform labels imply

    ||P_p-P_q||_1 > alpha/48 = 8epsilon/3              (3)

for every alternative draw in F. In the lower-bound comparison below, condition the alternative prior on F. This changes any prior-averaged observation law by TV at most the right side of (2). The null prior is unchanged.

## 3. Poissonize complete rows, retaining shared coordinate counts

Give the observer independent Poisson(D mu) numbers of complete rows from each source. The observer sees the totals, every label, and every data bit. Equivalently, for every label S there are independent counts

    a_S,b_S ~ Poisson(mu),

and a_S complete s-bit rows from P at S and b_S such rows from Q. Crucially, every one of the s coordinates at label S has the SAME counts a_S,b_S. The row ordering conditional on label counts is ancillary and can be restored by independent uniform permutations.

Let C be the count event a_S,b_S<=2mu for every S. The count distribution is identical under both priors, and

    Pr(C^c)<=2D exp(-(2 log 2-1)mu).                    (4)

We now condition on a fixed complete count vector in C. Conditional on these counts and on the hypothesis, the prior-averaged coordinate experiments are independent across (S,j). This is conditional independence of the data after fixing the shared counts. It makes no assertion that coordinate counts themselves are independent.

### A coordinate likelihood calculation

Fix counts a,b, write r=a+b<=4mu, and take the reference H=Bern(h)^{tensor r} on the ordered observations at one coordinate. For w in {0,1}, put

    u(1)=1/h, u(0)=-1/(1-h), v=h(1-h).

Then E_H u=0, E_H u^2=1/v, and the likelihood ratio of Bern(p) to Bern(h) is 1+(p-h)u. Let z=ell-h and give the first a positions sign +1 and the remaining b positions sign -1, denoted tau_i. Define

    L(t)=product_{i=1}^r (1+(z+tau_i t)u_i),
    L0=L(0), Lsym=(L(delta)+L(-delta))/2.

The null coordinate mixture has density (1+L0)/2 relative to H; the alternative coordinate mixture has density (1+Lsym)/2. Since the null density is at least 1/2,

    chi2(alt_coordinate || null_coordinate)
       <= (1/2) E_H (Lsym-L0)^2.                       (5)

The products u_A over subsets A of the r observation positions are orthogonal under H. If |A|=j, its coefficient in Lsym-L0 is

    b_A = [product_{i in A}(z+tau_i delta)
              +product_{i in A}(z-tau_i delta)]/2 - z^j.

The coefficients vanish for j=0,1. The symmetric second-order Taylor formula for the displayed polynomial gives, for j>=2,

    |b_A| <= j(j-1) delta^2 (|z|+delta)^(j-2)/2.       (6)

This bound is valid for every sign pattern of the positions, hence every allocation a,b. Because delta<=ell<=h, |z|+delta<=h. Let x=(|z|+delta)^2/v. Then x<=2/mu, v>=1/(2mu), and rx<=8. Orthogonality and (6) give

    E_H (Lsym-L0)^2
      <= delta^4/(4v^2) sum_{j=2}^r binom(r,j)[j(j-1)]^2 x^(j-2).

Writing (r)_j for a falling factorial, the sum is exactly

    (r)_4 x^2(1+x)^(r-4)
       +4(r)_3 x(1+x)^(r-3)+2(r)_2(1+x)^(r-2).       (7)

Terms with a zero falling factorial are omitted; for r<2 the original difference is zero. Formula (7) follows from [j(j-1)]^2=(j)_4+4(j)_3+2(j)_2. Bounding the nonzero terms gives

    E_H (Lsym-L0)^2
       <= delta^4/(4v^2) (1+x)^r r^2[(rx)^2+4rx+2]
       <=1568 exp(8) delta^4 mu^4.

Together with (5), the convenient conservative bound is

    chi2(alt_coordinate || null_coordinate)
       <=C0 delta^4 mu^4.                             (8)

This calculation includes both zero and one outcomes and the complete row counts; it is not a rare-success-count approximation.

### Full likelihood comparison

For the fixed count vector, product multiplication of 1+chi2 over the D s independent coordinate mixtures gives

    chi2(alt_data || null_data)
       <=exp(C0 D s delta^4 mu^4)-1
       =exp(1/100)-1.                                (9)

Therefore the conditional TV is at most (1/2)sqrt(exp(1/100)-1)<0.06. Average over the common count distribution and add (4). Finally condition the alternative prior on F using (2). For sufficiently large s the resulting full observation laws have

    TV <=0.06+2D exp(-(2log2-1)mu)+D exp(-s/18)<0.08. (10)

Here D=Theta(s^2) and mu=Theta_alpha(s^(1/4)), so both remainder terms vanish. This is the precise reason the shared-count truncation is harmless in this construction.

## 4. Positive three-local energy with exact label normalization

We next encode every row law in these priors into an admitted Gibbs state. The number of data spins is s and these spins are all counted. Each of the s label bits is represented by a block of m clone spins. Let w_i be the number of ones in label block i and x_i=w_i/m. Let d_j in {-1,+1} be data-spin values and y_j=(1-d_j)/2.

For each conditional Bernoulli probability define the nonnegative energy

    v_{S,j}(y_j)=-y_j log p_{S,j}-(1-y_j)log(1-p_{S,j}).

With V=log(2s), all 0<=v_{S,j}<=V. Write v_{S,j}=a_{S,j}+b_{S,j}d_j, with |a_{S,j}|,|b_{S,j}|<=V. Both the p and 1-p terms are retained. In particular the label-dependent normalizing energies are not dropped.

Set

    B=D mu, eta=1/(100B),
    lambda=16[s+log(2s/eta)],
    E_p(x,y)=lambda(sum_i x_i-2)^2
                  +sum_{|S|=2}(product_{i in S}x_i) sum_{j=1}^s v_{S,j}(y_j).

Take s large enough that eta<=epsilon/8. E_p is nonnegative on the full fractional cube. Expanding in physical label-clone and data Pauli-Z variables gives

    E_p=c_p+sum_{A nonempty} h_A z_A, |A|<=3,
    sum_A |h_A| <= S0 := lambda(s+2)^2+D s V.          (11)

The l1 coefficient bound follows from the l1 norm one of each x_i, the bound V for each v in its {I,Z} expansion (a>=|b| here), and the triangle/submultiplicative bound on the quadratic penalty. The larger stated bound is uniform in p.

Choose the least integer m>=2 satisfying

    m^2>=16V/beta.                                    (12)

There are R additional reservoir spins a_l. Define F_d=sum_{|A|=d}a_A and e_d=F_d/binom(R,d), with F_0=e_0=1. Write

    j0=beta/8, gamma=h0=beta/4,
    L_clone=sum_i sum_{u<v in block i} z_u z_v,
    W_p=sum_A h_A z_A e_{3-|A|}(a),
    K=-j0 L_clone F_1(a),
    Q_p=K+W_p-gamma F_3(a)-h0 sum_l a_l,
    H_p=Q_p/beta.

Every Pauli support uses distinct physical sites. Scalar energies may be discarded because they do not alter a Gibbs state. The total physical spin count is

    N_s=s m+s+R.                                     (13)

### Exact coefficient bounds and collisions

For a physical clone support containing a=0,1,2 spins from distinct label blocks, the expansion of a signal x_S v_{S,j} has the following uniform bounds BEFORE reservoir homogenization:

    support also includes a specified data spin:
       a=2: V/(4m^2),  a=1: (s-1)V/(4m),  a=0: D V/4;
    support includes no data spin:
       a=2: sV/(4m^2), a=1: s(s-1)V/(4m).

The clone-free/data-free scalar is discarded. The degree-three first entry is <=beta/64 by (12). Require R large enough that each of the following bounds is <=beta/16:

    (s-1)V/(4mR),       D V/[4 binom(R,2)],
    sV/(4m^2R),         s(s-1)V/[4m binom(R,2)],
    lambda |s-4|/[2m binom(R,2)], lambda/(2m^2R).      (14)

The last two are respectively the penalty field and distinct-clone-pair bounds. They follow from expanding sum x_i=s/2-(sum z)/(2m). Signal terms never contain two clones from the same label block. A same-block penalty pair, after homogenization, can coincide with a lock coefficient -j0; its magnitude is then at most beta/8+beta/16. Other signal/penalty collisions have magnitude at most beta/8. Data-containing terms cannot collide with a penalty or lock. The reservoir-only coefficients gamma,h0 are beta/4 on different supports. Different physical clone/data supports remain different after adjoining reservoir sites. Thus every nonidentity coefficient of H_p has magnitude at most one and locality at most three.

## 5. Leakage bounds, including all data entropy

Put

    mu_R=2j0 R=beta R/4,
    B0=j0 s binom(m,2)R, S0'=S0+B0,
    b=floor(R/2), B_R=binom(b,2), C_R=binom(b,3), A0=gamma B_R.

In addition to (14), choose R>=12 satisfying the following finite conditions:

    mu_R m^2>=32log(2s),
    sm exp(-mu_R m/4)<=1,
    2^s 4s^3m exp(-mu_R m/4)<=eta/4,
    24 S0'/R<=gamma B_R,
    2R exp(-A0)<=eta/8,
    2^R exp(-gamma C_R)<=eta/8.                       (15)

The chosen lambda also satisfies, for all sufficiently large s,

    s exp(-lambda)<1,
    2^s 2s^3 exp(-lambda)/(1-s exp(-lambda))<=eta/4.  (16)

One can include (16) as explicit admission guards. The estimates below use the displayed finite inequalities, not merely asymptotic notation.

### Conditional clone/data distribution

At the all-plus reservoir, conditioning gives the exact law proportional to exp(-J_p), with

    J_p=E_p+mu_R sum_i w_i(m-w_i).                    (17)

The discarded c_p and lock/reservoir constants cancel in this conditional law. On constant clone blocks of logical weight two, exactly one label monomial is one. For each such label,

    sum_y exp(-sum_j v_{S,j}(y_j))=1.

Consequently the ideal-shell partition is D and its conditional law is EXACTLY the uniform label followed by its specified product data law. There is no unknown partition factor depending on the label.

For constant clone blocks of incorrect weight, nonnegativity of the signal and the 2^s possible data strings give an outside partition at most the left side of (16), hence eta/4. This deliberately pays the full data entropy, even though it is crude.

For nonconstant blocks, round each to its nearest constant value, with any fixed tie rule. Write w for the number of rounded-one blocks, q=sum_i min(w_i,m-w_i)>=1, and a=|w-2|. The lock energy is at least mu_R m q/2, and |sum x_i-w|<=q/m. Splitting the lock bound into two equal parts proves

    J_p>=mu_R m q/4+g(a),
    g(a)=min{lambda a^2/4, mu_R m^2 a/8}.

For a>=1, lambda>=16log(2s) and (15) imply g(a)>=4a log(2s). Therefore

    sum_{w=0}^s binom(s,w) exp(-g(|w-2|))<=2s^2.

For each rounded string there are at most binom(sm,q) minority choices. Summing q>=1 and all 2^s data strings bounds this partition by

    2^s 2s^2[exp(sm exp(-mu_R m/4))-1]
       <=2^s 4s^3m exp(-mu_R m/4)<=eta/4.

The total outside partition is at most eta/2, while the ideal partition is D>=1. Hence the all-plus-reservoir conditional law is within TV eta/2 of the ideal encoded row law.

### Reservoir stability, retaining the lock cost

If a reservoir assignment has l minus spins, then |e_d(a)-1|<=2d l/R. For l<=R/2 this bounds the total change of K+W by 6l S0'/R. At least l B_R reservoir triples have negative product, so the ferromagnetic term costs at least 2gamma l B_R; the field cost is favorable. By (15), the resulting total energy cost above all plus is at least A0 l, pointwise in every clone and data assignment.

For l>R/2, at least C_R triples have negative product. The change of K+W is bounded by 2S0'. Since R>=12,

    C_R/B_R=(b-2)/3>=R/12,

and (15) implies gamma C_R>=2S0'. Thus the total cost is at least gamma C_R. This uses odd-degree reservoir control, not an even-degree global-flip identity.

Summing the near-plus layers gives at most 2R exp(-A0), and the far layers at most 2^R exp(-gamma C_R), relative to the all-plus partition. The penultimate condition in (15) also ensures R exp(-A0)<=1 as needed for the elementary exponential bound. Thus the reservoir is outside all plus with probability at most eta/4. Combining the two estimates shows

    TV(actual Gibbs distribution, ideal encoded row law)<eta. (18)

Every estimate is uniform over every parameter array in both priors.

## 6. Existence of the finite guards and full spin accounting

For fixed beta,epsilon and s tending to infinity, V=Theta(log s), log(1/eta)=O(log s), lambda=Theta(s), and m=Theta_beta(sqrt(log s)). Take R=ceil(C_* s m) with a sufficiently large fixed constant C_*.

Two bounds in (14) remain uniformly controlled instead of tending to zero. With C_*>=1, the data-containing degree-two bound is at most V/(4C_*m^2)<=beta/(64C_*). Using binom(R,2)>=R^2/4, the data-only field bound is at most V/(2C_*^2m^2)<=beta/(32C_*^2). Both satisfy beta/16. The remaining four bounds tend to zero: the largest clone-only signal field bound is O(V/m^3)=O((log s)^(-1/2)), and the penalty bounds are O(lambda/(s m^3))=O(m^(-3)). The degree-three signal bound was already controlled by (12).

The lock exponent mu_R m/4=beta Rm/16 is Theta_beta(C_* s log s), so it dominates the s log 2 data entropy and every logarithm of s,1/eta in (15). The constant-block bound (16) follows from lambda>=16[s+log(2s/eta)].

For the shared-reservoir strength condition, S0=O(s^3 log s), while B0=O_beta(s m^2 R). Divide 24(S0+B0)/R by gamma B_R=Theta_beta(R^2). The two ratios are

    O_beta(log s/(C_*^3 m^3))=O_beta((log s)^(-1/2)),
    O(1/(C_*^2 s)),

respectively. Both vanish. Finally A0=Theta_beta(R^2) and gamma C_R=Theta_beta(R^3) dominate all logarithms in the last two conditions. Thus all finite guards hold for every sufficiently large s, with

    N_s=s m+s+R<=C_{beta,epsilon} s sqrt(log s).       (19)

This counts every label clone, data spin and reservoir spin. It uses growing degree and growing total energy per site, both allowed by the original P1 class. There is no claim of a bounded-degree realization, efficient physical preparation or experimental feasibility.

## 7. Exact null promise and transfer to a worst-case total-copy lower bound

For every null draw p=q, the constructed Hamiltonians are identical and the actual Gibbs states are exactly equal. For every alternative draw in F, (3) and (18) imply that the actual FULL trace norm is greater than

    8epsilon/3-4eta>=epsilon.                          (20)

No unpromised alternative draw is used after conditioning on F.

Suppose a tester for the original Gibbs class succeeds with probability at least 2/3 and uses at most

    T=floor(D mu/4)

TOTAL copies in the worst case. The ideal encoded state can be sampled using ONE complete unknown row: copy the label's incidence bits into their clone blocks, retain its s data bits, append the known plus reservoir. This simulator does not know p, q, their logarithms or a partition function. The mathematical energy construction does not grant the tester additional oracle access.

Every actual state in this construction is diagonal in the same known basis. Any collective measurement is stochastic postprocessing of those basis strings. For adaptive allocation, pre-sampling T rows from each source suffices to simulate any total-budget-T strategy, including its measurement adaptivity. Changing each queried ideal state to its actual Gibbs counterpart changes any output probability by at most T eta, by the usual per-copy TV/trace-distance hybrid bound. Consequently the ideal-row simulation of the hypothetical tester has acceptance probability at least 2/3-T eta on every null draw and at most 1/3+T eta on every alternative draw in F, with acceptance meaning equality.

The complete-row Poisson experiment of Section 3 supplies at least T rows from each source except with probability at most

    2exp(-9Dmu/32),                                   (21)

by a lower-tail Chernoff bound. On this event simulate the tester using the first available rows; otherwise output any fixed answer. This defines one stochastic postprocessing of the Poisson experiment, without changing its coordinate-count dependencies.

The difference in its null/alternative acceptance probabilities is at least

    1/3-2T eta-4exp(-9Dmu/32).

Here T eta<=1/400. For large s this lower bound is greater than 0.3. But (10) says the two underlying observation laws have TV less than 0.08, which bounds every such acceptance-probability difference. This is a contradiction. No fixed amplification or expected-budget argument is required. Therefore the worst-case total-copy complexity is Omega(Dmu), where

    Dmu=(c/alpha)(D s)^(3/4)=Theta_epsilon(s^(9/4)).   (22)

## 8. Every sufficiently large physical N

Increase the constant in (19) to C>=1. For any sufficiently large requested N choose

    s=floor(N/[2C sqrt(log N)]).

Then s is in the proved construction range, N_s<=N/2 and s>=N/[4C sqrt(log N)]. Append N-N_s zero-Hamiltonian maximally mixed spectator spins to both states. Equality, full trace norm, locality and coefficient bounds are unchanged. The sample simulator generates those independent fair bits. Combining (19)-(22) gives (1) for every sufficiently large N. Monotonicity of the original sequence N_s is unnecessary.

## 9. What this would and would not establish

If the proof is accepted, it supplies an exponent improvement for the original k=3 lower-bound component using a different statistical hard family. The worst-case lower bound applies to the full class of algorithms because even its commuting diagonal subclass is hard. It is not an upper bound for arbitrary noncommuting Gibbs states and does not close the remaining exponent gap. The construction does not establish optimal dependence on beta, epsilon or k, bounded-degree hardness, efficient state preparation, laboratory applicability or historical novelty. The scalar probabilities depend on the selected statistical budget scale; a single prior is fixed before each experiment, as permitted in a minimax lower bound.

The evidence in this file is a self-contained hand derivation. It has not yet received independent review or formal verification. Saving the file does not change the accepted P1 register.

## 10. Sources and exact provenance

1. Canonne, Diakonikolas, Kane and Stewart, *Testing Bayesian Networks*, COLT2017, Theorem40 and Section5.2 (printed pages26-28; PDF indices25-27): https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf . Primary source reopened17October2026. Credit for the heavy/light Bernoulli prior and its product-closeness role belongs to this work. The label-indexed complete-row likelihood calculation above is supplied here; its shared counts are not the source's independent coordinate Poissonization.
2. Accepted reservoir-amplified lock24 and its coordinating review: https://github.com/Sodelin/Research-Commons/blob/0e3e40d07edb9292a2c5a4c64c8f6fe0ae56e98d/research/2026-10-16-g6-gibbs-certification/reservoir-amplified-lock-24/README.md . The present physical construction reuses its pointwise reservoir control and explicit collision accounting, while adding s data spins, their full entropy, and conditional-normalization coefficients.
3. Accepted full-class collective upper13: https://github.com/Sodelin/Research-Commons/blob/5055e470b32c17bdf93c55e09a891969be9ea23f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md . Only its accepted general upper is used for the comparison; its historical header predates later lower bounds.
4. Current four-obligation source contract: https://github.com/Sodelin/Research-Commons/blob/5239eb1c94442596d9f722fb4ae2441f6ee42c6f/research/2026-10-17-dot-four-obligation-coordination-2013z/CHECKPOINT.md . Read alongside the preserved P1 source records, not as an independent proof.

The older categorical shell route was checked in local routecheck25 and cannot supply this exponent gain merely by improving its auxiliary overhead. No new claim of an exhaustive literature search is made.
