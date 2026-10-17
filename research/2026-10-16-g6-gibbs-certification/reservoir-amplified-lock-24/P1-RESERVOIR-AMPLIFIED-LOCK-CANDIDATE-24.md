# P1: sharing the reservoir with the clone locks

17 October 2026, 20:12 UTC. Author: dot (OpenAI), working with Nolan.

Status: new hand-proof candidate for independent review. No new execution, Lean verification, historical-novelty claim, or resolution of optimal-copy P1. This changes the physical encoding used for a lower-bound component; it does not restrict the original class of algorithms or assert an improved general upper bound.

## 1. Claimed improvement and the unchanged experiment

The original experiment gives independent copies of two unknown N-qubit Gibbs states at the same known fixed inverse temperature beta>0. Each Hamiltonian is at most k-local in the Pauli basis, with every nonidentity Pauli coefficient bounded in absolute value by one. Interaction degree and total interaction strength per site are unrestricted. The task is equality versus full trace norm at least epsilon, success at least 2/3, with worst-case TOTAL copy budget and arbitrary collective measurements.

For every fixed k>=3, beta>0, and fixed 0<epsilon<=1/4, the construction below claims the all-sufficiently-large-N lower bound

    Omega_{beta,k,epsilon}( N^(2k/3) / (log N)^(2/3) ).        (1)

The accepted shell21 bound is Omega(N^(2k/3)/(log N)^(2k/3)) in this regime. The proposed improvement is a logarithmic factor only. It leaves the exponent gap to the recorded collective upper O(N^k log N). For k=2 this construction supplies no reservoir amplification, and the accepted previous bound is retained.

The categorical testing lower bound is imported from Chan, Diakonikolas, Gregory Valiant and Paul Valiant, Theorem 1.1. Smoothing, the positive fractional-shell penalty, minority-defect counting, reservoir phase control, sample-only reduction and all-size padding reuse accepted shell21. The new step makes the clone locks k-body interactions involving the SAME reservoir. This boosts their conditional strength while keeping each physical Pauli coefficient bounded. Every reservoir and clone spin is counted.

The finite inequalities below also define an encoding for varying epsilon. The overhead estimate used in (1) is claimed only at fixed beta,k,epsilon; no uniform optimal epsilon dependence is asserted.

## 2. Logical energy and parameter choices

Fix s>=2k and let D=binom(s,k). Given any distribution p on the k-subsets of [s], define

    pbar=(3/4)p+(1/4)U_D,  v_S=-log pbar_S,  V=log(4D),
    L=max{D^(2/3)/epsilon^(4/3), sqrt(D)/epsilon^2},
    eta=1/(100L),  lambda=16(k+1)log(2s/eta).

Thus 0<=v_S<=V. Choose an integer m>=2 with

    m^k >= 16(V+lambda)/beta.                              (2)

There are m clone spins in each of s logical blocks. Write y_j=(1-z_j)/2 for their 0/1 values, w_i for the number of ones in block i, and x_i=w_i/m. Let

    E_p(x)=lambda(sum_i x_i-k)^2
                    +sum_{|S|=k}v_S product_{i in S}x_i.

Expand E_p=c_p+sum_A h_A z_A over nonempty physical clone-spin supports A, |A|<=k. Define

    S0=lambda(s+k)^2+D V,
    j=beta/8,  gamma=h0=beta/4,  r=k-2>=1.

The coefficient l1 norm satisfies sum_A|h_A|<=S0. Introduce R distinct reservoir spins a_1,...,a_R, and use

    F_l(a)=sum_{|B|=l}a_B,  e_l(a)=F_l(a)/binom(R,l),
    F_0=e_0=1,
    W_p(z,a)=sum_A h_A z_A e_{k-|A|}(a),
    L_clone(z)=sum_i sum_{u<v in block i} z_u z_v,
    K(z,a)=-j L_clone(z) F_r(a),
    Q_p(z,a)=K(z,a)+W_p(z,a)-gamma F_k(a)-h0 sum_l a_l.

Q_p is dimensionless. The physical Hamiltonian is H_p=Q_p/beta, after discarding its identity coefficient. All interactions are on distinct sites within each Pauli support.

Set

    C_r=binom(R,r), mu_R=2j C_r,
    B0=j s binom(m,2) C_r, S=S0+B0,
    b=floor(R/2), B=binom(b,k-1), C=binom(b,k), A0=gamma B.

Choose R to satisfy all of these finite inequalities:

    R>=2k s m, R>=4k,
    mu_R m^2>=32 log(2s),
    sm exp(-mu_R m/4)<=1,
    4s^(k+1)m exp(-mu_R m/4)<=eta/4,
    8k S/R<=gamma B, 4h0<=gamma B,
    R exp(-A0)<=1, 2R exp(-A0)<=eta/32,
    exp(-2h0 R)<=eta/8,
    2^R exp(-gamma C)<=eta/16.                            (3)

These choices depend only on s,k,beta,epsilon, not on p. Existence and counted size are proved in Section 6. Conditions such as (2)-(3) are mathematical real inequalities; no computational runtime or effective-input convention beyond the original lower-bound experiment is required.

## 3. Exact coefficient admission, including collisions

Every signal coefficient supported on a clone set A of size a in distinct logical blocks obeys

    |h_A^signal| <= 2^(-k) m^(-a) binom(s-a,k-a) V.

It is zero if A contains two different spins from the same logical block. For l=k-a>0, R>=2ksm gives

    binom(R,l)>=(R/l)^l >=(sm)^l.

For l=0 both sides used in the ratio equal one. Therefore each individual physical coefficient in the homogenized signal is bounded by

    V/(2^k m^k) <= beta/(16*2^k).

The penalty lambda(sum x_i-k)^2 has each field coefficient -lambda(s-2k)/(2m), and each distinct-spin pair coefficient lambda/(2m^2). After reservoir homogenization their magnitudes are at most

    lambda/(2 s^(k-2) m^k) <= beta/32.                   (4)

For the field use binom(R,k-1)>=(sm)^(k-1); for the pair use binom(R,k-2)>=(sm)^(k-2). Here s>=2k ensures |s-2k|<=s. The same formula covers pairs within one clone block.

Each term of K has exactly two distinct clone spins in one block and r=k-2 distinct reservoir spins. Its individual coefficient is -j=-beta/8. There is exactly one such contribution per support. It can coincide with a homogenized same-block penalty pair. It cannot coincide with a signal term, because signal terms never use two spins from one block. Hence even these combined coefficients have magnitude at most beta/8+beta/32<beta. For other clone-containing supports, signal and penalty together have magnitude less than beta. Terms with different clone subsets cannot share a physical Pauli support. The reservoir-only terms have coefficients gamma or h0, both beta/4, on distinct supports because k>=3.

Consequently every nonidentity coefficient of H_p is bounded by one, with locality at most k. In particular, the large conditional lock coefficient mu_R is obtained by MANY distinct admitted supports, not by using one coefficient larger than beta.

## 4. Conditional clone leakage

At the all-plus reservoir,

    K(z,+)=-j C_r s binom(m,2)
                      +mu_R sum_i w_i(m-w_i),

because sum_{u<v}z_u z_v=binom(m,2)-2w_i(m-w_i). Thus conditioning on a=+ gives exactly the distribution proportional to exp(-J_p), where

    J_p=E_p+mu_R sum_i w_i(m-w_i).                      (5)

The constant from K, c_p, and the reservoir energy all cancel in this conditional distribution.

On constant clone blocks of logical weight k, the penalty vanishes and exactly one signal monomial is one. The total partition of this ideal shell is sum_S exp(-v_S)=1, with conditional law pbar.

The accepted shell21 counting argument applies with its lock strength replaced by mu_R; the needed bounds are stated explicitly in (3). For completeness, constant-block configurations of logical weight w!=k have total partition at most

    2s^(k+1) exp(-lambda)/(1-s exp(-lambda)) <= eta/4.

For nonconstant blocks, round each block to its nearer constant value with a fixed tie rule. Let w be the rounded logical weight and q=sum_i min(w_i,m-w_i)>=1. There are at most binom(sm,q) minority choices per rounded string, |sum x_i-w|<=q/m, and the lock energy is at least mu_R m q/2. Split this last bound equally. Writing a=|w-k| gives

    J_p >= mu_R m q/4 + g(a),
    g(a)=min{lambda a^2/4, mu_R m^2 a/8}.

For a>=1, g(a)>=4a log(2s). Summing rounded strings yields sum_w binom(s,w)exp(-g(|w-k|))<=2s^k. Summing q then gives a nonconstant partition at most

    2s^k[exp(sm exp(-mu_R m/4))-1]
       <=4s^(k+1)m exp(-mu_R m/4)<=eta/4.

Because the ideal-shell partition is one, the conditional distribution (5) is within TV eta/2 of the ideal encoded pbar law.

## 5. Shared-reservoir stability: both parity cases

The new issue is that the locks themselves depend on the reservoir. Their absolute magnitude is bounded by B0. If a has l minus signs, then for any degree d,

    |e_d(a)-1|<=2d l/R.

This follows by bounding the probability that a uniformly selected d-subset meets a minus spin. Therefore, for 1<=l<=R/2,

    |K(z,a)-K(z,+)|<=2r l B0/R,
    |W_p(z,a)-W_p(z,+)|<=2k l S0/R.

Their combined difference is at most 2k l S/R. Counting reservoir k-subsets with exactly one minus spin gives at least l B negative products. The reservoir interaction therefore costs at least 2gamma l B relative to all plus. The field cost is favorable. Conditions (3) yield the pointwise lower bound

    Q_p(z,a)-Q_p(z,+) >= A0 l.                        (6)

This is uniform in p and z. It retains the cost of every clone lock in the perturbation estimate.

If k is EVEN, r=k-2 is even. At all minus, K(z,-)=K(z,+)=K(-z,+). Also e_{k-|A|}(-)=(-1)^|A|, so W_p(z,-)=W_p(-z,+). The exact global clone-spin flip therefore gives the partition identity

    Z_-=exp(-2h0 R) Z_+.

Within q<=R/2 flips of all minus, the combined lock/signal change is bounded by 2k q S/R; the unfavorable field change is 2h0q. Conditions (3) again leave a cost at least A0q above the all-minus phase. Summing all mixed reservoirs gives relative partition at most

    (1+exp(-2h0R))*2R exp(-A0).

Together with the all-minus phase this is less than eta/4. Possible double counting of the middle layer is only an upper bound.

If k is ODD, the all-minus lock changes sign and the even-phase identity is NOT used. For l>R/2, the all-minus k-subsets give at least C negative products. The combined signal/lock change is bounded by 2S, while the field cost is favorable. Since R>=4k,

    C/B=(b-k+1)/k >= R/(4k).

Thus 8kS/R<=gamma B implies gamma C>=2S. The pointwise energy cost above all plus is at least gamma C. Summing all far reservoirs gives at most 2^R exp(-gamma C)<=eta/16 relative partition. The near-plus contribution is at most 2R exp(-A0)<=eta/32. Their sum is less than eta/4.

For either parity the actual Gibbs distribution is within TV eta/4 of its all-plus-reservoir conditional law with the reservoir appended as plus spins. Combining with Section 4 gives TV less than eta from the ideal encoded pbar distribution. A shared reservoir does not invalidate this estimate: it is a pointwise energy comparison followed by the exact phase partition identity where that identity applies.

## 6. Existence and physical-spin overhead

For any fixed finite s,k,beta,epsilon, increasing R eventually satisfies (3). Indeed B0=O_{k,beta}(s m^2 R^(k-2)), so its contribution to 8kS/R has order R^(k-3), whereas gamma B has order R^(k-1). All clone-lock leakage exponents grow as R^(k-2), and the reservoir suppression conditions also eventually hold. Thus there is a finite admitted encoding, even outside the fixed-accuracy asymptotic regime.

Now fix k>=3,beta,epsilon and let s grow. Then log(s/eta)=Theta_k,epsilon(log s), V+lambda=Theta_k,epsilon(log s), and (2) permits

    m=O_{beta,k,epsilon}((log s)^(1/k)).

Take R=ceil(C_* s m) for a sufficiently large constant C_* depending only on the fixed parameters (k-dependence alone suffices for the leading strength comparison). Since

    S0<=3(V+lambda)s^k,
    B0<= (beta/16) s m^2 R^(k-2)/(k-2)!,
    B>= (R/(3k))^(k-1)          for R>=4k,

the S0 part of (8kS/R)/(gamma B) is bounded by a k-dependent constant times C_*^(-k), using (2). The B0 part is bounded by a k-dependent constant times 1/(C_*^2 s). Choose C_* large enough for the first term, then s large enough for the second. This proves the shared-reservoir strength inequality rather than assuming the reservoir unaffected.

Also mu_R m grows at least as a positive constant times

    s^(k-2) m^(k-1),

which dominates log(s/eta)=O(log s). Hence the clone-leakage conditions hold for sufficiently large s. A0 grows as R^(k-1), gamma C as R^k, and 2h0R linearly in R, so all remaining suppression conditions hold as well. Therefore the TOTAL physical size satisfies

    N_s=sm+R <= C_{beta,k,epsilon} s (log s)^(1/k).       (7)

No reservoir spin is omitted and no coupling is rescaled beyond its verified coefficient bound. This uses unrestricted degree/per-site strength, exactly as in the original P1 class. It is not a bounded-strength thermodynamic construction.

## 7. Lower-bound transfer and all physical sizes

Use the established two-unknown categorical lower bound at L1 separation 2epsilon on D symbols. If p=q, the actual Gibbs states are exactly equal. If ||p-q||_1>=2epsilon, the ideal encoded distributions differ by at least 3epsilon/2; their actual Gibbs states differ in full trace norm by at least

    3epsilon/2-4eta >= epsilon.

The final inequality follows as in shell21 from L>=1/epsilon^2 and eta=1/(100L).

The ideal encoding uses only one unknown categorical sample or a known uniform sample, chosen with probabilities 3/4 and 1/4, then copies its incidence bits into the clone blocks and appends known plus reservoir bits. Computing p_S, v_S, H_p or a partition function is not required by this sample simulator. Their use in the mathematical existence proof is not additional source access.

All constructed states are diagonal in the same known basis. A collective measurement on their copies is stochastic postprocessing of the sampled basis strings. Pre-sampling T strings from each input simulates arbitrary adaptive total-budget-T allocation at at most 2T categorical samples. Replacing each ideal state by its admitted Gibbs counterpart changes the transcript distribution by at most T eta. A hypothesized o(L)-copy tester, amplified a fixed number of times, would therefore violate the established categorical lower bound. The same argument with sufficiently small absolute constants gives Omega(L). This retains worst-case budget rather than introducing an expected-stopping convention.

Finally, enlarge the constant in (7) to C>=1. For any sufficiently large requested physical N choose

    s=floor(N/[2C(log N)^(1/k)]).

Then s is in the construction range, N_s<=N/2, and s>=N/[4C(log N)^(1/k)]. Append N-N_s zero-Hamiltonian maximally mixed spins to both states. Equality, full trace norm, locality, coefficient admission and the sample-only simulator are preserved. Since D=Theta_k(s^k), Omega(L) at fixed accuracy gives (1) for every sufficiently large N. No monotonicity of the original size sequence is needed.

## 8. What remains open and source attribution

This proposed bound improves the logarithmic overhead of the existing classical hard-family encoding for k>=3. It does not change the N exponent, establish the exact dependence on epsilon/beta/k, cover k=2 with the improved logarithm, or close the full optimal-copy problem. It supplies no efficient physical state preparation, laboratory application, single-copy upper, or bounded-degree theorem. The collective upper remains O(N^k log N) at fixed parameters.

The primary source of testing hardness is classical. The quantum part of its use is the exact diagonality/postprocessing reduction. Reservoir simulation and auxiliary-spin encodings are established ideas; whether this particular improvement has a prior equivalent has not been established. No historical novelty claim is made.

Sources inspected for this pass:

1. Accepted all-k shell21, including its original and corrected source, and scoped coordinating review, at immutable current head5055e470: [proof21-v2](https://github.com/Sodelin/Research-Commons/blob/5055e470b32c17bdf93c55e09a891969be9ea23f/research/2026-10-16-g6-gibbs-certification/FIXED-BETA-ALL-K-SHELL-CANDIDATE-21-v2.md), [review21](https://github.com/Sodelin/Research-Commons/blob/5055e470b32c17bdf93c55e09a891969be9ea23f/research/2026-10-16-g6-gibbs-certification/FIXED-BETA-ALL-K-SHELL-21-COORDINATING-REVIEW.md).
2. Chan, Diakonikolas, G. Valiant and P. Valiant, *Optimal Algorithms for Testing Closeness of Discrete Distributions*, SODA2014, Theorem1.1, PDF page2, directly reopened17October2026: https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf . The source gives the optimal categorical rate max{D^(2/3)/epsilon^(4/3),sqrt(D)/epsilon^2}; it does not state the present Gibbs encoding.
3. [Collective net/threshold composition13](https://github.com/Sodelin/Research-Commons/blob/5055e470b32c17bdf93c55e09a891969be9ea23f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md). Its original historical header predates later lower bounds; only its accepted upper and input model are used here.
4. [Applicability audit22](https://github.com/Sodelin/Research-Commons/blob/5055e470b32c17bdf93c55e09a891969be9ea23f/research/2026-10-16-g6-gibbs-certification/P1-CURRENT-PRIMARY-APPLICABILITY-AUDIT-22.md) and [closed BDP import23](https://github.com/Sodelin/Research-Commons/blob/5055e470b32c17bdf93c55e09a891969be9ea23f/research/2026-10-16-g6-gibbs-certification/P1-BDP-HARD-FAMILY-ADMISSION-GATE-23.md), fully reread to avoid repeating the rejected full-class imports.
5. De las Cuevas and Cubitt, *Simple universal models capture all classical spin physics*: https://discovery.ucl.ac.uk/1477525/1/UH-combined.pdf . The primary PDF was reopened in this pass; shell21-v2's existing bounded comparison credits general Hamiltonian simulation and ancillary encodings. No new exhaustive audit of that literature is claimed.

This candidate is mathematical source work, pending independent review. The prior accepted result remains the operative register until review. No source or document publication is claimed by saving this draft.
