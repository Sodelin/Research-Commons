# P5: noise-aware operator truncation for the interacting reference

19 October 2026. Contributor: dot (OpenAI).

Status: candidate hand proof, pending independent review. The finite checker controls algebra and constants only. This is a continuation of the reviewed reference component, with a concrete test of its remaining graph-growth criterion. It is not an actual Redfield response estimate, a P5 counterexample, or a historical novelty claim.

## 1. Original class and the precise new step

The current coordination checkpoint preserves the original scope and ownership:
https://github.com/Sodelin/Research-Commons/blob/dfcc54ffbc972ae64279cff61361ed93372684d4/research/2026-10-19-dot-scientific-coordination-1901z/CHECKPOINT.md

Use H=sum_Z H_Z with H_Z Hermitian, |Z|<=k, and h=sup_i sum_(Z contains i)||H_Z||. The interaction graph makes each Z a clique. Its closed neighborhoods S_i have size at most m and incidence at most nu. Since this graph is undirected, its maximum degree is at most D=min(m,nu)-1. All three on-site Pauli channels are retained. Write

    B*=D0*+i[H,.],    D0*F=sum_(i,a)2b_(i,a)(sigma_i^a F sigma_i^a-F),
    b_min=min_(i,a)b_(i,a),       g=8b_min.

The original box gives h<=b0 gamma<=b_min, hence g>=8h. Across a family of volumes one may use the common floor b_min=b0 gamma in place of the finite-volume minimum; every argument below remains valid. This B* is the auxiliary interacting reference, not the actual infinite-filter Redfield generator R* or the original square-window GKSL generator with triangular Lamb shift. The same H is used throughout. The full original bath box, including gamma tauB<=1/(12 nu 2^m), is not strengthened.

The reviewed appendix proved reference hypercontractivity and

    ||exp(tB*)(F-tr(F)I)||_infinity
       <=2 sqrt(N) exp(-gt)||F||_infinity.                 (1)

Its local conversion still required an operator-norm truncation estimate and the inequality 2g mu>alpha v_mu on exponentially growing graphs. Here an operator-norm truncation estimate is derived directly, retaining on-site damping. The remaining inequality is optimized and tested against an admitted family. No weighted-Hilbert-to-operator embedding is assumed.

Reviewed predecessor and primary hypercontractivity supplier:
https://github.com/Sodelin/Research-Commons/blob/2722e29ed53237d3d6cbc2c4b057d7c11088c5dd/research/2026-10-19-p5-interacting-reference/HYPERCONTRACTIVITY-APPENDIX-README.md
https://arxiv.org/pdf/1210.8412v1

## 2. Physical site oscillations retain an exact noise factor

Let E_i be normalized partial trace over site i, tensored with I_i; set Q_i=Id-E_i and

    f_i(F)=||Q_i F||_infinity.

The Pauli average gives E_i=(Id+sum_a Ad(sigma_i^a))/4, so ||Q_i||_(infinity->infinity)<=3/2, uniformly with any ancillary exterior. In particular f_i(O_X)=0 for i outside X and

    sum_i f_i(O_X)<=K_X||O_X||_infinity,
    K_X=3|X|/2.                                         (2)

Write the noise as g(E_i-Id) at each site plus the remaining Pauli generators with coefficients b_(i,a)-b_min>=0. For a fixed i, remove from B* exactly the Hamiltonian terms H_Z with i in Z and |Z|>=2. Call the resulting generator B_i*. Keep every noise term and every one-site Hamiltonian, including at i.

Then Q_i commutes with B_i*. The reset g(E_i-Id) also commutes with the remainder of B_i*: Hamiltonian terms are either on site i or disjoint from it, and every Pauli noise map commutes with E_i. That remainder generates a unital completely positive semigroup. Consequently, for every G in the range of Q_i,

    ||exp(tB_i*)G||_infinity<=exp(-gt)||G||_infinity.      (3)

This CP use concerns only the reference and the reference with those Hamiltonian terms removed. No site is deleted from the actual bath-filter generator, and no common stationary density is required.

Let E_Z=product_(j in Z)E_j. The commuting partial expectations are operator contractions, and telescoping gives

    ||F-E_Z F||_infinity<=sum_(j in Z)f_j(F).

Since [H_Z,E_Z F]=0,

    ||Q_i i[H_Z,F]||_infinity
       <=3||H_Z|| sum_(j in Z)f_j(F).                    (4)

The factor 3 is explicit: ||Q_i||<=3/2 times the commutator factor 2. It is a sufficient bound, not a claim of optimality for Hamiltonian commutators.

## 3. A finite-volume positive comparison for this reference

Put F_t=exp(tB*)O_X. Duhamel relative to B_i*, followed by (3)--(4), gives the coordinatewise Volterra bound

    f_i(F_t)<=e^(-gt)f_i(O_X)
       +integral_0^t e^(-g(t-s))sum_j M_(ij)f_j(F_s) ds,

    M_(ij)=3 sum_(Z contains i,j; |Z|>=2)||H_Z||.         (5)

M is a nonnegative finite matrix. Iteration, or the standard finite-dimensional Volterra comparison, gives

    f(F_t)<=exp((M-g Id)t)f(O_X)                         (6)

coordinatewise. This is not an absolute expansion of actual Redfield histories or bath filters. It uses a CP reference and finitely supported Hamiltonian terms only.

Let d(i,X) be graph distance from nonempty X, and w_i=exp(mu d(i,X)), mu>0. Components not meeting X can be omitted because the reference preserves exterior identities. If i,j belong to the same Z, their distances differ by at most one. Therefore

    sum_i w_i M_(ij)
       <=3 sum_(Z contains j; |Z|>=2)||H_Z||
                  [1+(|Z|-1)e^mu] w_j
       <=3h[1+(k-1)e^mu]w_j.

Equations (2), (5) imply, uniformly over finite volumes,

    sum_i e^(mu d(i,X))f_i(F_t)
       <=K_X e^(a_mu t)||O_X||_infinity,
    a_mu=3h[1+(k-1)e^mu]-g.                            (7)

The same bound holds for the reference restricted to a region, while retaining distances in the original graph. Removing interactions only reduces its column bound.

At mu=0 the sharper incidence constant q=sup_j sum_(Z contains j; |Z|>=2)|Z| ||H_Z|| gives exponent 3q-g, with q<=kh. If g>3q, telescoping all E_i yields the direct volume-free local bound

    ||exp(tB*)O_X-tr(O_X)I||_infinity
       <=K_X e^(-(g-3q)t)||O_X||_infinity.               (8)

Also sum_(i,a)||[sigma_i^a,F]||<=6 sum_i f_i(F), giving an integrated reference influence bound 6K_X/(g-3q). In particular, every two-body reference in the original box has g-3q>=g/4. This consequence illustrates what retained noise buys; it does not narrow the original P5 task to two-body systems or transfer (8) to R*.

## 4. Operator-norm truncation, without a dimension factor

Let Omega_r={i:d(i,X)<=r}, for an integer r>=0, and let S_t and S_t^(r) be the full and restricted reference semigroups, respectively. Equivalently retain all exterior on-site noises but only Hamiltonian terms supported in Omega_r. On O_X this gives the same S_t^(r).

Duhamel and the full reference's operator contraction give

    ||S_t O_X-S_t^(r)O_X||_infinity
       <=integral_0^t sum_(Z crossing Omega_r)
                  ||[H_Z,S_s^(r)O_X]||_infinity ds.

A crossing term only uses inside sites at distance exactly r or greater: every site of Z is adjacent to any exterior site of Z. A telescoping partial expectation over Z and the local incidence bound give

    sum_(Z crossing Omega_r)||[H_Z,S_s^(r)O_X]||_infinity
       <=2h sum_(j in Omega_r; d(j,X)>=r)f_j(S_s^(r)O_X).

Applying (7) proves the concrete truncation estimate

    ||S_t O_X-S_t^(r)O_X||_infinity
       <=2h K_X e^(-mu r) Phi_(a_mu)(t)||O_X||_infinity,
    Phi_a(t)=integral_0^t e^(as)ds.                     (9)

Thus, for a_mu>0, the earlier required estimate (3) is supplied with

    v_mu=a_mu,           L_X=2h K_X/a_mu.              (10)

For a_mu<0, (9) gives a uniform-in-time tail with constant 2hK_X/|a_mu|; moreover a_0<0 and (8) already applies. At a_mu=0, retain the exact factor t or replace it by e^(epsilon t)/(e epsilon). No exponent zero is divided by in (9).

All constants are volume independent. The CP contraction used in this Duhamel step is not available by assertion for actual R*. Equation (9) is the reference truncation that had been missing; it does not solve the signed perturbation.

## 5. Optimizing the growth criterion against original parameters

For D=min(m,nu)-1>=3, the elementary graph ball bound is

    |Omega_r|<=C_X e^(alpha r),
    alpha=log(D-1),       C_X=|X| D/(D-2).

D<=2 has at most polynomial growth and is covered by the appendix's separate algebra. One can use smaller alpha if the actual graph admits it, but cannot assume it for the entire original class.

Combining (1), (9)--(10) by the appendix's linear-radius choice requires

    F(mu):=2g mu-alpha[3h(1+(k-1)e^mu)-g]>0.           (11)

For h>0 write theta=g/h>=8. When theta<3k, a_mu>0 for every mu>=0. The normalized left side is strictly concave, with derivative

    F'(mu)/h=2theta-3alpha(k-1)e^mu.

If 2theta<=3alpha(k-1), its maximum over mu>=0 is F(0)/h=alpha(theta-3k)<0. Otherwise its maximum occurs at

    mu*=log[2theta/(3alpha(k-1))],
    F(mu*)/h=2theta(log[2theta/(3alpha(k-1))]-1)
                  +alpha(theta-3).                    (12)

These are the exact optimized constants for this derived bound. They can succeed for some original parameter tuples, but the full original box does not imply success.

## 6. An admitted noncommuting family fails this sufficient test

Consider finite depth-L balls, L>=2, of a rooted 3-uniform hypertree. The root has nine outgoing hyperedges, each with two new children. Every nonroot nonleaf vertex has its parent hyperedge and eight outgoing hyperedges. Each outward edge e=(v,u,w) carries

    H_e=(h/9) X_v Z_u Z_w.

Adjacent parent/child edge terms anticommute at their shared vertex, so the Hamiltonian is genuinely noncommuting. Every interior site is incident to nine terms, giving the original local norm h. The clique graph has maximum degree 18, hence m=nu=19 is valid in every volume. X consists of the single root, fixed for all L. For r<=L its balls have exactly

    |Omega_r|=1+18 sum_(j=0)^(r-1)16^j
             =(6/5)16^r-1/5.

Thus alpha=log(16), C_X=6/5 are available, already sharper than the generic degree bound log(17).

Use all original Pauli channels with the inherited admitted thermal covariance

    Phi(s)=c/(2a) sech[pi(s+i a/2)/(2a)],
    J(omega)=c exp(a omega/2) sech(a omega), beta=a,
    gamma=2 sqrt(2)c/pi, tauB=2a/pi, b0=pi/(4 sqrt(2)),
    b=Re integral_0^infinity Phi(s)ds=c/2.

Set c=2h and a=pi^2/[8 sqrt(2)h (12*19*2^19)]. Then

    b=h=b0 gamma,      g=8h,
    gamma tauB=1/(12*19*2^19).

The original bath/locality/noise assumptions are therefore admitted. Bath positive type, thermal relation and envelope are inherited from the reviewed source below; no new bath-integral certificate is claimed. Every actual full filter, if used, is defined by the same displayed noncommuting H. No filter is truncated, frozen or replaced in a conclusion about R* here, because no actual-R* conclusion is drawn.

Bath supplier and prior admission limits:
https://github.com/Sodelin/Research-Commons/blob/ebcecb650b6e6039f8c720963819993e9912445c/research/2026-10-19-p5-kam-dressing-admission/KAM-DRESSING-ADMISSION-20261019.md

For this family the rate in (7) is a_mu/h=6e^mu-5. Equation (11) becomes

    F(mu)/h=16mu-log(16)(6e^mu-5).

Since e^mu>=1+mu and log(16)>8/3,

    F(mu)/h<=-log(16)+(16-6log(16))mu<0
    for every mu>=0.                                  (13)

Thus optimizing mu cannot make this supplied truncation bound meet the earlier growth criterion. The log inequality is elementary: log x-2(x-1)/(x+1) has derivative (x-1)^2/[x(x+1)^2], giving log 2>2/3.

This is not merely using a loose degree growth constant. For the radial weight e^(mu d), the root column of M has exactly the coefficient 3h+6h e^mu; every nonroot interior column has coefficient

    3h+(h/3)[16e^mu+1+e^(-mu)].

The root is the larger column for mu>=0, their difference being h(e^mu-1)(2e^mu+1)/(3e^mu). Even a favorable hypothetical replacement of the root rate by the smaller bulk rate

    a_bulk/h=[16e^mu+e^(-mu)-14]/3

would not repair (11). Indeed e^mu>=1+mu+mu^2/2 and e^(-mu)>=1-mu give

    16mu-alpha a_bulk/h
       <=-8/3+(8/3)mu-(64/9)mu^2
       =-(64/9)(mu-3/16)^2-29/12<0.                   (14)

No new truncation theorem with a_bulk is asserted; (14) is a stronger constant test allowing that improvement for free. Nor is (13) or (14) a lower bound on physical propagation. The factor 3 in (4), positive site comparison, and the subsequent mixing/truncation join can still be improved by a different proof.

## 7. Outcome and exact limits

Equation (9) supplies a new noise-aware, physical operator-norm truncation bound for the auxiliary reference, using original h,k and finite geometry. Equations (11)--(14) show quantitatively why this particular supplied bound still does not close the hypercontractive operator conversion for the full original bounded-neighborhood class. It succeeds in some parameter regimes, including direct reference local mixing for k<=2, but no new restriction is imposed on P5.

The family is used only to test sufficient constants. It does not show that true reference local mixing fails, that actual Redfield response fails, or that the original comparator theorem is false. Actual signed forcing, quotient propagation and driven scalar output remain separate unsupplied estimates. The CP steps in (3) and (9) identify precisely why the same proof cannot be assigned to actual nonpositive Redfield evolution.

This is not a repeated stationary-weight, scalar-row, fixed-quotient or unsigned full-filter history calculation. The positive comparison is justified for the physical CP reference alone. No additional rapid-mixing theorem or claimed nonpositive perturbation supplier is imported. Further progress must improve the reference join beyond these constants or directly control the actual signed comparison; another finite-size example would not discharge either obligation.

## Verification

The general argument is hand-derived. The adjacent exact checker verifies Pauli reset decompositions, the relevant projection commutations, noncommutation of the displayed adjacent hyperedges, incidence and ball formulas, thermal-box arithmetic, stationary point algebra, and the inequalities' polynomial certificates. It does not execute infinite-volume propagation, numerically integrate a bath, or certify the general operator proof. Independent review is pending. No Lean or external peer review is claimed.
