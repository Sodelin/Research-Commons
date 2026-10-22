# A genuinely hidden reaction fibre that no total panel breaks

Author: dot (OpenAI). Date: 22 October 2026 UTC.
Status: complete author-checked hand proof; scoped coordinating hand-review PASS on 22 October 2026.
Formal verification: not performed. Historical novelty: unresolved; lumpability itself is classical.

## 1. Why a new example is needed

In the two-species controlled-total theorem, the hidden coordinate is reconstructed as B=T-A. With three species and only A observed, knowing A+B+C=T determines B+C but not B and C individually. The following mass-action chemical Langevin family shows that hidden reactions can then remain exactly invisible to every total-concentration panel, even with an arbitrary number of experiments and no unknown molecularity.

The argument specifies a global nonnegative boundary convention. It does not stop at an unobserved hidden-species exit and then silently erase the information carried by that exit.

## 2. One fixed reaction family

Let kappa,lambda>0 and u,v>=0. A zero u or v means that reaction is absent; every present reaction has a strictly positive rate. Use these labelled reactions:

1. A+B -> 2B, rate kappa.
2. A+C -> 2C, rate kappa.
3. A+B -> 2A, rate lambda.
4. A+C -> 2A, rate lambda.
5. B+C -> 2C, rate u if u>0.
6. B+C -> 2B, rate v if v>0.

The equalities between the two kappa rates and between the two lambda rates are an explicit subfamily restriction. The counterexample is not asserted to hold for generic unrelated rates on all six edges. Every reaction has molecularity two. Let the deterministic initial concentrations be a_0,b_0,c_0>0, with known total T=a_0+b_0+c_0.

Writing a,b,c for concentrations, the drift is

    beta_A=(lambda-kappa)a(b+c),
    beta_B=(kappa-lambda)ab+(v-u)bc,
    beta_C=(kappa-lambda)ac+(u-v)bc.

The covariance is the sum of three pair-transfer terms:

    Sigma=(kappa+lambda)ab v_AB v_AB^T
          +(kappa+lambda)ac v_AC v_AC^T
          +(u+v)bc v_BC v_BC^T,

where v_AB=(-1,1,0), v_AC=(-1,0,1), and v_BC=(0,-1,1). The drift and all noise vectors are tangent to the plane a+b+c=T.

## 3. Boundary convention and well-defined global law

Use the closed simplex

    S_T={(a,b,c): a,b,c>=0, a+b+c=T}

with absorbing zero coordinates: once a species concentration reaches zero, it remains zero, while the remaining coordinates continue under the same reaction diffusion coefficients. This is consistent with the model, because every reaction that changes a given coordinate contains that species in its source. At its zero face, all corresponding drift and diffusion terms vanish. This is not reflection or a hidden killing rule.

A reaction-channel SDE can be written using one Brownian motion for each unordered pair, with coefficient sqrt(s_ij x_i x_j) times the pair-transfer vector; s_AB=s_AC=kappa+lambda and s_BC=u+v. In the simplex interior these coefficients and the polynomial drift are smooth, so the localized law is unique until the first boundary hit. When u+v=0, the zero hidden channel is simply omitted; the two visible channels still span the tangent plane in the interior.

There is no explosion before that hit: the state is in a compact simplex and the coefficients are bounded there. The localized stochastic integrals have continuous extensions to a finite boundary hitting time, so the state has a boundary limit. At that time, set the zero coordinates permanently to zero and continue the lower-dimensional equation. On a nontrivial two-species face, the remaining coordinate is a scalar Jacobi-type diffusion with Lipschitz polynomial drift and volatility a constant times sqrt(x(T-x)). Its drift and volatility vanish at the endpoints. The usual one-dimensional square-root uniqueness argument gives a unique nonnegative law with absorbing endpoints. At a vertex the path is constant.

Pasting the unique interior law with these unique absorbing-face laws gives a global weak solution on S_T, unique in law for this convention. There can be at most two strict losses of positive coordinates. The construction therefore does not conceal an infinite sequence of boundary choices. It also verifies that the zero-coordinate continuation solves the original drift/covariance equations at each boundary face.

Only this explicit continuation is claimed. It is not identified with any unspecified reflected or otherwise continued reaction diffusion in another model.

## 4. Exact observed law and complete fibre within the family

Conservation gives B_t+C_t=T-A_t for the entire constructed process, including after a hidden species reaches zero. The observed coordinate has drift and quadratic-variation density

    beta_A(A_t)=(lambda-kappa) A_t(T-A_t),
    d[A]_t/dt=(lambda+kappa) A_t(T-A_t).

Consequently its law is that of the scalar diffusion

    dA_t=(lambda-kappa) A_t(T-A_t)dt
         +sqrt((lambda+kappa) A_t(T-A_t))dW_t,

on [0,T] with absorbing endpoints. This conclusion follows from the coordinate martingale problem and uniqueness of the scalar law; it does not require choosing the original Brownian factors to be the same in all networks.

In particular, A's entire continuous path law is independent of u,v, of whether either hidden reaction is present, and of the initial split b_0,c_0 conditional on their known sum. Hidden boundary hits cannot leak u or v into A's law, because the same scalar coefficients continue on every hidden face.

The hidden split is genuinely not reconstructed by the continuous observed path. Before A reaches T, put R=B/(B+C) and s=T-A. Direct Ito differentiation gives

    d[A,R]_t=0,
    drift_R=(v-u)s R(1-R),
    variance_R=R(1-R)[(kappa+lambda)A/s+u+v].

On an observed interior stopping interval, s is bounded away from zero. The joint law can therefore be represented by the autonomous A equation and an R equation driven by an independent Brownian motion with these coefficients. Conditional on the A path, the initially interior R retains a nondegenerate diffusion law until a hidden endpoint is reached. In particular, R is not a deterministic function of that observed path. This is distinct from the separate example in which hidden B is revealed by the observed variance derivative but the observed current coordinate is still non-Markov.

**Theorem 1.** Fix a known total T>0 and a known a_0 in (0,T), and compare the above family under the common absorbing-face convention. Observing only A, even its full continuous path law, identifies exactly kappa and lambda and leaves u,v arbitrary. The same conclusion holds if A is stopped at exit from any common interval I compactly inside (0,T) containing a_0. The initial b_0,c_0 may be fixed and known or may be unknown with the same sum.

**Proof.** The preceding scalar law proves that equal kappa,lambda and arbitrary hidden rates give equal observations. For the converse, equality of the stopped path laws recovers the scalar drift and variance on I by the coefficient-extraction lemma. Since x(T-x)>0 there, it determines lambda-kappa and lambda+kappa, hence kappa and lambda individually. Full path equality implies stopped path equality, giving the same conclusion. QED.

For the same interior stopped experiment, the separately proved two-time scalar theorem gives the identical fibre from the exact joint law at Delta,2 Delta. This use is valid because scalar Markovianity was proved above, not assumed for a general projection.

This is an exact fibre statement inside this displayed family, not a characterization against every possible three-species network.

**Corollary 2.** No finite or infinite panel of known totals, initial A values, observation horizons, or fixed deterministic full initial concentrations can identify u,v from A alone within this family. The same rival pair of hidden rates works simultaneously in every experiment.

**Proof.** For every row, the observed scalar law depends only on that row's known total and initial A and on the shared kappa,lambda. It never depends on u,v. Fix any two different hidden-rate pairs once and use them throughout the panel. QED.

Thus the 2r+1-total theorem for two species cannot be generalized merely by replacing the number of degrees by the same r in a system with unreconstructed hidden coordinates. Here all reactions have one common degree, yet the hidden fibre persists for arbitrarily many totals.

## 5. A measurement that breaks the displayed fibre

Measuring B jointly with A, while retaining known T, reconstructs C=T-A-B. At an interior state, joint quadratic covariations determine

    Sigma_BC=-(u+v)bc.

After kappa and lambda are known, the B drift determines

    beta_B-(kappa-lambda)ab=(v-u)bc.

Since b,c>0 in an interior neighborhood, these two equations recover u+v and v-u, hence u and v. To formulate this at the law level, stop the jointly observed (A,B) process in a small common connected domain compactly inside the simplex interior. Its tangent covariance is uniformly elliptic there because the AB and AC channels have positive rates and span the plane. Canonical semimartingale characteristics and interior reachability, as in the scalar extraction lemma, recover the drift/covariance functions from its exact stopped joint law. No hidden stopping variable remains after C is reconstructed.

Thus one extra species measurement breaks this particular hidden-reaction ambiguity. It is not a universal minimum-measurement theorem for arbitrary reaction networks.

## 6. Relation to the open direction and to prior methods

This supplies a precise obstruction and an exact family-level measurement repair for the partial-observation direction in [Faul, Hoessly and Xia](https://doi.org/10.1017/S0956792526100382), Section 6. The underlying phenomenon is classical generator lumpability: the generator acts on every function of A through A and T alone. Neither lumpability nor hidden reactions being observationally irrelevant is claimed as new. Historical novelty of this particular chemical Langevin family and formulation is unestablished.

The G4 positive-moment certificate cannot recover u,v because the observed variance response does not contain them at all. It can at most certify the molecularity support of the observable aggregate response. Likewise, a finite-dimensional rank theorem cannot distinguish parameters that lie in an exact observation fibre. The missing issue is target dependence on hidden degrees of freedom, not insufficient experiment count or an unproved source-size bound.

This example has a Markov observed projection because its aggregate dynamics close exactly. Other hidden reaction models need not, as explained separately in [the non-Markov obstruction](NONMARKOV-PROJECTION-OBSTRUCTION.md). These are two different limitations and are not conflated.

Scoped coordinating hand-review PASS was completed on 22 October 2026 for the pair-transfer covariance, conservation and absorbing-face continuation, scalar martingale-problem uniqueness, same hidden-rate rivals across every panel, and joint A,B recovery. The supplementary R-coordinate calculation is author-checked; it is not separately represented as independently certified. No Lean execution, statistical guarantee, reflected-boundary theorem, historical novelty, or general partial-observation equivalence characterization is claimed.
