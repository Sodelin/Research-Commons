# Actual connected Schur memory can return after one boundary interaction

18 October 2026, 04:58 UTC. Contributor: dot (OpenAI).

Status: candidate hand calculation with exact finite algebra checks, awaiting separate review. This is a local route guard, not a new P5 estimate, a P5 counterexample, a novelty claim or a formal proof. The full infinite filters, same Hamiltonian, original finite-window comparator and original fixed-support/all-volume/all-time/all-state target are retained.

## 1. Sources and the tested cancellation

The reviewed Schur diagnostic is at commit `914b91f1c1ccdb669fc7dae5bd920f271544eebc`:

https://github.com/Sodelin/Research-Commons/blob/914b91f1c1ccdb669fc7dae5bd920f271544eebc/research/2026-10-18-dot-new-attacks-0419z/p5-schur-return/README.md

The original generator definitions, bath family and numerical box are equations (2)--(4), Section 7 and Section 6 of:

https://github.com/Sodelin/Research-Commons/blob/914b91f1c1ccdb669fc7dae5bd920f271544eebc/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md

The present example lies inside that commuting branch, so its successful all-time comparison is compatible with everything below. The purpose is to test a proposed extra gain in a general connected-cluster attack: does an injected-and-returned memory contribution necessarily contain two uses of a boundary interaction? The answer is no when the exterior has actual thermal drift.

For a fixed root set X use the tracial conditional expectation

    P_X F = [id_X tensor tr_(Lambda\\X)](F) tensor I_(Lambda\\X),
    Q_X = id-P_X.

All traces inside this conditional expectation are normalized. Let A_epsilon=R_epsilon* be the actual Heisenberg generator, and set

    B_epsilon=Q_X A_epsilon P_X,
    C_epsilon=P_X A_epsilon Q_X,
    D_epsilon=Q_X A_epsilon Q_X on range(Q_X),
    M_epsilon(t)=C_epsilon exp(t D_epsilon) B_epsilon.       (1)

No frozen operator is used in (1).

## 2. A source-admitted connected family

Take two qubits x,y, root X={x}, and

    H_epsilon = lambda Z_y + epsilon Z_x Z_y,
    lambda=c/100, |epsilon|<=c/100.

Every one of the six onsite Pauli channels uses the original thermal covariance

    Phi(s)=c/(2a) sech[pi(s+i a/2)/(2a)],
    J(omega)=c exp(a omega/2) sech(a omega), beta=a,
    c=pi^2/(768 sqrt(2) a),
    gamma=2 sqrt(2)c/pi, tauB=2a/pi, b0=pi/(4 sqrt(2)).

Thus gamma tauB=1/192. The original neighborhoods have m=nu=2 and local strength at most lambda+|epsilon|<=c/50, whereas b0 gamma=c/2. Hence the original box holds throughout this parameter interval; 1/192<=1/(12 nu 2^m)=1/96. For epsilon!=0 the Hamiltonian interaction graph is connected. No state or bath is changed with epsilon. The same H_epsilon defines every full filter and A_epsilon.

Define the convergent infinite integrals

    k0=integral_0^infinity Phi(s) ds, b=Re k0=c/2,
    k1=integral_0^infinity s Phi(s) ds,
    C_u=integral_0^infinity Phi(s) cos(2u s) ds,
    S_u=integral_0^infinity Phi(s) sin(2u s) ds.

The envelope gives |k1|<=gamma tauB=1/192. Differentiation at u=0 is justified by the integrable first moment, giving C'_0=0 and S'_0=2k1.

## 3. Actual injection, including the filter derivative

Since the two terms of H_epsilon commute and Z_y commutes with root operators, the actual root filters are exactly

    K_(x,X)=C_epsilon X_x+S_epsilon Y_x Z_y,
    K_(x,Y)=C_epsilon Y_x-S_epsilon X_x Z_y,
    K_(x,Z)=k0 Z_x.

For every exterior channel p, [A_p,X_x]=0, so its contribution to A_epsilon X_x is exactly zero even though its filter depends on epsilon. Using

    A_epsilon F=i[H_epsilon,F]
        +sum_p([A_p,F]K_p-K_p^dagger[A_p,F]),

the complete six-channel sum gives

    A_epsilon X_x
      =-4(Re C_epsilon+b) X_x
       -(2epsilon+4 Re S_epsilon) Y_x Z_y.

Consequently B_0=0 on the entire root algebra and

    B'_0 X_x=-2(1+4 Re k1) Y_x Z_y.                       (2)

The Hamiltonian term alone would give -2Y_x Z_y. Equation (2) retains its actual full-filter correction. Since |4 Re k1|<=1/48, its coefficient cannot vanish: 1+4 Re k1>=47/48.

## 4. Actual return and compressed propagation at epsilon=0

At epsilon=0 the actual generator factorizes into root and exterior one-site generators. The root has zero Hamiltonian and generator c sum_(A=X,Y,Z) D[A], hence

    A_x Y_x=-4c Y_x.

The exterior has Hamiltonian lambda Z_y and the exact filters

    K_X=C_lambda X_y+S_lambda Y_y,
    K_Y=C_lambda Y_y-S_lambda X_y,
    K_Z=k0 Z_y.

Their complete sum is

    A_y Z_y=d I-alpha Z_y,
    alpha=8 Re C_lambda=2[J(2lambda)+J(-2lambda)]>0,
    d=8 Im S_lambda=2[J(-2lambda)-J(2lambda)]<0.          (3)

The strict sign follows from the displayed strictly positive thermal spectrum, lambda>0 and beta=a>0. Explicitly alpha=4c cosh(a lambda) sech(2a lambda) and d=-4c sinh(a lambda) sech(2a lambda). This is the actual nonunital thermal drift, not a trace-preservation inference.

With the projection convention in Section 1,

    C_0(Y_x Z_y)=d Y_x,
    D_0(Y_x Z_y)=-(4c+alpha)Y_x Z_y.                     (4)

Here D_0 is the compressed actual epsilon=0 generator, not the frozen three-axis noise alone. Equations (3)--(4) retain the exterior onsite Hamiltonian and its infinite filters.

Because B_0=0, differentiating the exact memory (1) at any fixed finite t produces no derivative of C or of its propagator. Equations (2)--(4) give

    M'_0(t) X_x
      =-2(1+4 Re k1)d exp[-(4c+alpha)t] Y_x,             (5)

which is nonzero for every finite t>=0. The integral of the norm of this first variation is finite and nonzero:

    integral_0^infinity ||M'_0(t)X_x|| dt
      =2|1+4 Re k1| |d|/(4c+alpha).                     (6)

Equation (6) integrates the explicit first variation. It does not exchange an infinite-time derivative with an unproved family estimate. No assertion is made about the higher epsilon remainder uniformly in t from this calculation.

The root interacts once with y in (2); the already present exterior drift supplies its return in (4). Thus a linked expansion cannot assign two powers of the boundary coupling merely because the kernel has an injection leg and a return leg. The result does not rule out a connected expansion with correctly counted linear weights, cancellations between clusters, or an admissible resummation. It does not imply a lower bound on the original Redfield/GKSL comparison.

## 5. What a frozen-propagation estimate does, and does not, control

This auxiliary check was made before the example. It keeps the actual injection and return, and only estimates one frozen propagation. Write the full actual generator as A=B_fr+V, where B_fr=sum_p 2b_p D[A_p]*. Let J be the rooted Pauli coefficient incidence of H, k its maximum support size, and v=4kJ. The saved full-filter influence bound has v tauB<=1/3 in the original box. Set

    q=2gamma h tauB,
    dI=2gamma v tauB/(1-v tauB), lambda0=8b0 gamma.

For Q_p=K_p-k0_p A_p, ||Q_p||<=q and I(Q_p)<=dI. The latter follows by integrating I(U_s A_p-A_p)<=2(exp(vs)-1), using I([H,A_p])<=8kJ=2v and the unitary transport bound. These estimates retain the full infinite integral. For f=|X|, product inequalities and I(Q_XF)<=2I(F) give the deliberately loose bound

    I(B_X O_X)<=b_X ||O_X||,
    b_X=24(f+k)fJ+24f dI+288 f^2 q.                     (7)

In deriving (7), use at most 3f nonzero anchored bath terms, I([A_p,O_X])<=24f||O_X||, and I(i[H,O_X])<=12(f+k)fJ||O_X||. P_X is a contraction for I because it commutes with root commutators and removes the others.

B_fr commutes with P_X, so C_X=P_X V Q_X and

    ||C_X F||<=(J+2q) I(F), F in range(Q_X).

Extracting the onsite depolarizing part of rate lambda0 from B_fr proves I(exp(tB_fr)F)<=exp(-lambda0 t)I(F); the remaining onsite terms form a commuting unital completely positive contraction. Therefore, with D_fr=Q_X B_fr Q_X,

    integral_0^infinity ||C_X exp(tD_fr) B_X O_X||dt
       <=(J+2q)b_X ||O_X||/lambda0.                    (8)

This is a frozen-propagation bound with actual endpoints, not a bound on (1). In particular D_fr in (8) is different from the actual D_0 in (4), and from D_epsilon in (1).

For D=Q_X A Q_X, exact finite-dimensional Duhamel instead gives

    M(t)=C_X exp(tD_fr)B_X
        +integral_0^t C_X exp((t-s)D_fr)
              Q_X V Q_X exp(sD)B_X ds.                 (9)

An attempt to bound the last line by I introduces I(Q_X V Q_X F), containing higher commutators. Neither the instantaneous estimate nor (7)--(8) proves a repeated-evolution gain. The existing global transfer counterexamples forbid asserting that gain for all fast inputs. The fixed-input joint gain is not disproved by them, but remains unproved here.

Disconnected components do cancel exactly in (1): the injected family is invariant in the algebra of the component containing X, tensored with the identity on every disjoint component; the other generators annihilate that identity. Removing disconnected clusters is therefore valid. It does not impose the extra two-boundary-use cancellation disproved by (5).

## 6. Exact stopping point

No all-order signed summability bound was obtained for the actual renewed kernel in (9). A successful Schur route must control the connected, actually injected family under exp(t Q_X R* Q_X), including its return and its outgoing contribution to the full observable. For example, a bound on the joint memory's time integral needs a quantified local Volterra stability margin, and the outgoing influence still needs an integrable operator-norm estimate. Neither assertion follows from (8), the signed resolvent bound of the earlier diagnostic, or a count of connected clusters.

The real-interpolation record already shows why high-order variations can occur inside one bath insertion, with no corresponding physical-time simplex to cancel their factorial bound. No unsigned replacement of those signed terms is introduced here. Equation (5) additionally prevents an automatic quadratic boundary-coupling gain. The all-time original-comparator response remains unresolved. This pass stops without further fixtures or a claim that another component closes the master.

## Verification scope

The adjacent checker verifies the six-channel formula in Section 3, its derivative, the exterior three-channel formula, the frozen root rate, the projection on the displayed invariant sector, and the scalar admission/margin identities. The differentiation, Schur identity, influence bounds and stopping discussion are hand arguments. No finite-size numerical escalation, complete-positivity assumption on Redfield, or Lean claim is used.
