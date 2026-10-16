# P5: rejected global mixed-gradient gate and exact product-noise countercheck

16 October 2026. Contributor: dot (OpenAI). Source-level hand analysis with scoped coordinating acceptance of the explicit MR counterexample only. FINAL ROUTE STATUS: the proposed global maximal-regularity estimate (MR) is FALSE, by the explicit Hermitian counterexample in the 16:51 successor section below. The earlier attempt is retained as history, not a live candidate. P5 remains open; no novelty claim.

## Preserved target and sources

The 10:05 reconciliation at 7a5a5282de68aaa356dec6a8d2591fc12e0c8821, supplier04/corrected obstruction05 at 44ace19b8deed339e992c4ca6a6e07ca8c152bbe, checkpoint10 and volume-tail12 at 4a391a06b9c18d6496c7d3c7b3f763d55d185441 were reread. The target is the actual infinite-filter Redfield response on fixed-support observables, uniform in elapsed time and volume. The Hamiltonian remains bounded-body/incidence, the bath retains its positive-type thermal assumptions, exponential envelope and noise floor. A lattice-only filter estimate does not cover arbitrary admitted interaction geometries. No Lindblad substitution or positivity assumption about Redfield is made.

The previously established exact reduction needs integral_0^infinity I(exp(t L_R^*)O_X)dt <= C_X ||O_X||/gamma. Exponential support-cardinality admission of the full filter is unavailable. The following tests whether positive *reference* smoothing can avoid that admission, while keeping the full residual in the equation.

## Exact second-gradient bookkeeping

Index all on-site Pauli channels by p. Write D_p O=[A_p,O],

    I(O)=sum_p ||D_p O||,
    I2(O)=sum_(p,j) ||D_p D_j O||.

Put Q_p=K_p-k0_p A_p. The existing full-filter bound gives q=sup_p||Q_p|| <= 2 gamma h tauB. Let

    V_p O=(D_p O)Q_p-Q_p^dagger(D_p O),
    V=sum_p V_p,
    kappa=sup_p sum_j ||[A_j,Q_p]||.

In a finite volume these quantities are defined; a volume-uniform small kappa is an additional estimate to establish, not an assumed consequence of q. Jacobi and the product rule give exactly

    D_j V_p O = V_p D_j O
      + [[A_j,A_p],O]Q_p-Q_p^dagger[[A_j,A_p],O]
      + (D_p O)[A_j,Q_p]-[A_j,Q_p^dagger](D_p O).

Summing norms yields

    I(V O) <= 2q I2(O)+(8q+2 kappa)I(O).                 (1)

For the middle term, only the two different axes at the same site contribute; each commutator is plus or minus 2i times the remaining axis. Each resulting axis occurs twice in the ordered (j,p) sum. The two products with Q account for 8q I. The last two products give 2 kappa I. Also

    I2(O) >= 2 I(O),                                   (2)

because the diagonal p=j terms obey ||[A_p,[A_p,O]]||=2||[A_p,O]||. These are finite-volume operator-norm statements, without commutativity assumptions about H or Q.

Equation (1) explains why a small instantaneous bound ||V O||<=2q I(O) alone does not close the response. Its next derivative contains I2, rather than merely I.

## What positive product-noise smoothing would have to prove

For diagnostic clarity consider an isotropic product depolarizing reference B with single-Pauli decay rate lambda>0; S_t=exp(tB). This is a reference model, not a change to the full physical generator. A potential sufficient estimate is

    integral_0^infinity I2(S_t O)dt <= (C/lambda) I(O),   (MR)

with C independent of volume and O. The usual componentwise contraction gives only integral I(S_t O)<=I(O)/lambda; it does not prove (MR), whose sum has a second derivative. Exchanging the two inequalities would be an unjustified dimension-free maximal-regularity assumption.

There is a precise conditional reason (MR) would matter. For B+V in a fixed finite volume, Duhamel with S_t on the outside, Tonelli on nonnegative norms, and (MR) give on every finite time horizon T

    Y_T := integral_0^T I2(exp(t(B+V))O)dt
      <= (C/lambda)I(O)
         +(C/lambda) integral_0^T I(V exp(u(B+V))O)du
      <= (C/lambda)I(O)+(C/lambda)(6q+kappa)Y_T.

The last step uses (1) and (2). Thus C(6q+kappa)<lambda would close this particular residual bootstrap, if (MR) were actually proved. No contractivity of exp(t(B+V)) was used. However, B+V omits the Hamiltonian superoperator; a complete application must also admit that actual term in the same bound and handle the actual channel-dependent product reference. Neither omission can be silently ignored. This is a diagnostic reduction, not a proved physical estimate.

## Exact sanity check: neither the instantaneous failure nor a word calculation decides MR

For a Pauli word P supported on m sites and normalized to operator norm one,

    I(P)=4m,  I2(P)=16m^2,  S_t P=exp(-lambda m t)P.

Hence I2/I=4m is unbounded, excluding a dimension-free *instantaneous* replacement of I2 by I. But

    integral_0^infinity I2(S_t P)dt = (4/lambda)I(P).

The reference damping exactly cancels the extra word-weight factor after integration. Therefore this word example does not disprove (MR). Conversely, checking words does not establish (MR) for arbitrary operator sums: operator norm is not the sum of Pauli coefficient magnitudes, and choosing such a norm incurs precisely the uncontrolled support costs already excluded by earlier notes. No claim about (MR)'s truth is made here.

## Exact stopping point

This attempt provides the explicit mixed-gradient residual estimate (1), the finite-horizon conditional closure calculation, and the opposite instantaneous/integrated word checks. It does not provide a new volume-uniform response bound. Before continuing this route, one must prove or disprove (MR) in operator norm with its exact sums, then check the full Hamiltonian and the actual product-reference rates and establish the necessary uniform filter influence kappa under the original geometry. A theorem only for individual Pauli words or an arbitrary newly imposed coefficient norm is insufficient.

Alternatively, a direct fixed-support evolution estimate may bypass this global reference condition. Its failure, if found, would only reject this sufficient route; it would not produce a physical fixed-support P5 counterexample. The accepted large-support nonpositive witness and scalar-majorant limitation remain separate and are not recycled as such a counterexample.

No execution, formal verification, independent acceptance, physical counterexample or full P5 closure is claimed. This note is preserved locally for review rather than promoted as an accepted supplier.

## 16:51 UTC successor: the proposed global MR estimate is false

The preceding attempt is preserved as chronology. Its original SHA256 is 66028799ea80ac8d0a783648d18cd9d4801c23b3c7c6cdffca8e69f62728c0f4. The open MR question above is now resolved negatively by this elementary countercheck. This is a failure of that proposed sufficient estimate, not of P5.

Let N>=2 be even, let 0<theta<pi/2, and set c=cos(theta), s=sin(theta). Use the isotropic product depolarizing reference with single-site Pauli decay lambda. Set

    O_N=cos(theta sum_(i=1)^N Z_i),  ||O_N||<=1.

This is Hermitian. Since the Z_i commute, O_N=Re product_i(c I+i s Z_i). The product channel acts exactly as

    S_t O_N=Re product_i(c I+i r s Z_i),
    r=exp(-lambda t),  a=(c²+r²s²)^(1/2).

Initially, commuting either X_i or Y_i through O_N gives norm at most 2s, while the Z_i commutator vanishes. Thus

    I(O_N)<=4Ns.                                      (3)

For distinct sites i,j and axes p at i and q at j chosen independently from X,Y, the double commutator of S_t O_N has norm exactly

    ||D_p D_q S_t O_N||=4r²s² a^(N-2).                (4)

To check (4), apply the two sign flips to the corresponding factors. Their product contributes (2i r s)² Z_i Z_j, multiplied on the left by the two norm-one Pauli operators. The remaining factor is Re product_(l!=i,j)(c I+i r s Z_l). Its norm is at most a^(N-2). Equality is attained by choosing half of the remaining N-2 Z eigenvalues positive and half negative; their paired factors multiply to c²+r²s². This also covers N=2 with an empty remaining product.

There are 4N(N-1) ordered distinct-site/axis pairs. Ignoring the nonnegative same-site contributions gives

    integral_0^infinity I2(S_t O_N)dt
      >=16N(N-1)s² integral_0^infinity r²(c²+r²s²)^((N-2)/2)dt
      =16(N-1)(1-c^N)/lambda.                        (5)

For the equality substitute u=r², dt=-du/(2lambda u), and integrate the resulting power between zero and one. No inequality involving the actual Redfield semigroup, numerical approximation or large-N limit is used in (3)-(5).

If (MR) held for every Hermitian O with one volume-independent C, (3)-(5) would require

    C >= 4(1-1/N)(1-cos(theta)^N)/sin(theta).

Take theta=N^(-1/2). The elementary inequalities sin(theta)<=theta and cos(theta)<=exp(-theta²/2) give the explicit lower bound

    C >=4(1-1/N)(1-exp(-1/2)) sqrt(N).

Therefore no such C exists. This obstruction already occurs for a positive product-noise semigroup; the difficulty cannot be removed simply by choosing a contractive reference. H=0 with identical admitted baths realizes this frozen reference (lambda=8b), so there is no issue realizing the reference itself. But the witness support is N and the failed statement is a global second-gradient estimate. The actual fixed-support P5 comparison is exact when H=0. In particular, this is not an admitted counterexample to the original P5 conclusion.

### Consequence for the active proof route

The direct all-operator maximal-regularity bootstrap proposed above is unavailable. A possible replacement would have to control mixed gradients only on the restricted operators actually generated from O_X by the Hamiltonian and the full anchored filters, with constants tied to fixed X rather than ambient volume. None of the preceding estimates proves that restricted closure. Merely applying (MR) after a filter insertion is now explicitly ruled out.

The original alternatives remain: establish a genuinely fixed-support actual-Redfield response estimate using additional structure already present in the model, or construct a fixed-support interacting counterexample under the complete original bath/Hamiltonian assumptions. The full generator must remain in the evolution. The global obstruction just proved supplies neither alternative. No new literature/theorem attribution is asserted for this elementary countercheck; historical novelty is unassessed, and review is pending.

## Coordinating hand review, 16 October 2026, 16:52 UTC

The coordinating dot contributor read the complete successor and hand-checked the explicit MR counterexample: equations (3)-(5), all four ordered X/Y choices for each distinct-site pair, balancing the even number N-2 of remaining eigenvalues, the substitution u=exp(-2lambda t), the constant 16(N-1)(1-c^N)/lambda, the initial I upper bound, and the resulting square-root-N lower bound on C. This scoped review accepts that global sufficient-route obstruction. It does not constitute blanket acceptance of the earlier residual bookkeeping, the conditional closure, or bath-realization assertions, and does not close fixed-support P5. No execution, Lean verification, external peer review or historical novelty conclusion is claimed.

The prereview successor is preserved locally with SHA256 71fc7b99475388c78c732ca45d998bcdc83fe67cac45d6d4160d4b71b3dd2ec4. This successor changes the status and appends the precise review receipt; the counterexample and original historical calculations are unchanged.
