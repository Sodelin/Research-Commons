# P5: an exact on-site thermal reference is available, but its interaction admission is still missing

16 October 2026, 22:41 UTC. Contributor: dot (OpenAI).
Status: source-grounded calculation with scoped coordinating hand review of the on-site coefficient estimate, reset identity and completely bounded relaxation bound, and unitary variation estimate. No full P5 proof, execution experiment, Lean verification or novelty claim.

## Purpose and recovered boundary

Note17 disproves a global first-gradient inverse bound for the actual anchored correction relative to frozen unital noise. Its witness has growing support. This check addresses its suggested reference repair, without repeating that proof. Recovered records are notes08 (weighted-L2 admission),14 (full-filter finite-order derivatives),16 (nonpositive/accretivity boundary), and17 (published at dfbe1ce92e4bc34dffa86cfacfc524d6793fce55). The original target remains the full Redfield evolution on fixed-support input, uniformly in time and volume, compared to the original finite-window GKSL generator. Bounded incidence is retained.

## 1. Exact physical reference and a sufficient positivity condition

Split the actual Pauli Hamiltonian as H=H0+Hint, where H0=sum_i H_i contains only on-site terms. Identity terms are irrelevant. Define

 h0 = sup_i ||H_i||,
 Jint = sup_i sum_{Z contains i} ||h_Z||,

where Hint=sum_Z h_Z is the original interaction decomposition. All bounds below are uniform in volume. Define the actual on-site filtered operators

 K0_(i,a)=integral_0^infinity Phi_(i,a)(s) exp(-i H_i s) sigma_i^a exp(i H_i s) ds.

These are exact full-time filters for H0, with the original baths; they are not a secular approximation. Put z_(i,a)=integral Phi_(i,a), b_(i,a)=Re z_(i,a)>=b0 gamma and Q0=K0-z sigma^a. The exponential envelope gives

 ||Q0_(i,a)|| <= 2 gamma h0 tauB.                         (1)

K0 and Q0 are traceless. Expand Q0=sum_u q_(a,u) sigma^u. The normalized Hilbert-Schmidt identity gives

 ||q_a||_2^2 = tr(Q0^dagger Q0)/2 <= ||Q0||^2.

In the Pauli basis, the exact canonical dissipative coefficient matrix of the on-site Redfield generator is

 C_i = diag_a(2b_(i,a)) + sum_a(q_a e_a^dagger + e_a q_a^dagger).

This follows directly by writing each channel as

 K rho A + A rho K^dagger - A K rho - rho K^dagger A

and separating its anticommutator and Hamiltonian terms. Its Hamiltonian correction is (A K-K^dagger A)/(2i), summed over channels. Thus

 ||C_i-diag(2b_(i,a))|| <= 2 sum_a ||q_a||_2 <=12 gamma h0 tauB.

Consequently, under the explicit sufficient condition

 h0 tauB < b0/6,
 nu := 2b0 gamma-12 gamma h0 tauB >0,                    (2)

C_i>=nu I_3. The exact on-site Redfield reference R0 is therefore GKSL. It contains the strictly depolarizing part

 nu sum_a D[sigma_i^a] = 4nu(E_i-id),
 E_i(O)=I_i tensor tr_i(O)/2,

and a remaining on-site GKSL generator, including its physical on-site Hamiltonian. There is no tensor-volume factor in this assertion. E_i need not commute with the remaining dynamics: no such commutation is used or asserted. Both components are on-site and preserve the identity.

There is also a direct uniform one-site relaxation receipt, without assuming a stationary Gibbs weight. Write R0_i^*=S_i+lambda_r(E_i-id), lambda_r=4nu, where S_i is the remaining on-site GKSL generator. Its semigroup is a completely bounded contraction. Expanding in reset events and grouping by the first reset gives the exact identity

 T_i(t)=exp(-lambda_r t) exp(t S_i)
        +integral_0^t lambda_r exp(-lambda_r s) E_i exp(s S_i) ds.

Indeed every further on-site unital evolution after a reset leaves the resulting scalar unchanged. This argument also holds after tensoring an arbitrary ancilla. Hence the rank-one unital completely positive map

 Q_i=integral_0^infinity lambda_r exp(-lambda_r s) E_i exp(s S_i) ds

satisfies

 ||T_i(t)-Q_i||_cb <= 2 exp(-lambda_r t).                 (2a)

The integral is norm convergent; Q_i is rank one because every integrand is. Taking the limit in the semigroup identity proves stationarity and uniqueness of this projection. Thus the actual product reference meets the primary supplier's one-site condition (2.2) with M=2 and g=4nu, independently of volume. The primary supplier is stated on a lattice; this calculation itself needs only a finite site set and does not claim to transfer its entire theorem to general bounded-incidence geometries.

This proves a valid positive product reference inside restriction (2). It neither identifies its stationary state with the Gibbs state nor uses bath KMS as a generator detailed-balance theorem. Its exact stationary state is unnecessary for this positivity calculation. For the previously recorded strong-noise margin, this is automatic rather than an additional restriction. The exact source is [the original commuting-Pauli result](https://github.com/Sodelin/Research-Commons/blob/43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md), opening result and Section1, blob 3f543e6179d127a6bfae93477b56278bf2b7025c. Writing its geometry multiplicity as nu_geom to distinguish it from the noise coefficient nu above, its margin is

 g=8b0 gamma-2h-24 nu_geom 2^m gamma h tauB>0.

Since h0<=h, m>=1 and nu_geom>=1, this implies

 h0 tauB<=h tauB<b0/(3 nu_geom 2^m)<=b0/6.

The master scope preserves a broader noncommuting question. The commuting supplier's damping conclusion is not transferred to that question merely by copying the numerical margin. The reference calculation above, however, does not require commuting interactions; wherever that same numerical margin is imposed, (2) follows. For other parameter regimes (2) remains an explicit sufficient condition.

## 2. The exact remainder is still anchored, with a volume-free first bound

Let A_H(-s)=exp(-iHs) A exp(iHs), A_0(-s)=exp(-iH0s) A exp(iH0s), for A supported at i. Variation of constants between these two unitary groups gives

 ||A_H(-s)-A_0(-s)||
 <= integral_0^s ||[Hint,A_0(-u)]|| du
 <= 2 Jint s.

Only interaction terms incident to i enter the final commutator, since A_0(-u) remains on site i. The surrounding full unitary conjugations preserve operator norm. Thus the actual filter remainder

 Qint_(i,a)=K_(i,a)-K0_(i,a)

obeys

 ||Qint_(i,a)|| <= 2 gamma Jint tauB.                    (3)

There is no substitution of a bounded-degree star or a truncated bath. The full generator splits exactly as R=R0 plus the Hint commutator plus the original anchored channel expression with K replaced by Qint. In particular the on-site drift responsible for note17 is now part of R0, not a perturbation estimated by the rejected inequality.

But (3) is only a row bound on a full filtered operator. It does not bound a sum over every distant anchor acting on an arbitrary reached observable, nor make Qint finitely supported. Those are separate requirements.

## 3. Why the obvious reset-history proof still does not close

A product reference with the reset component in (2) suggests a direct history expansion. On an observable atom supported on Y, an E_i event removes site i from its support, while the other on-site reference evolution cannot enlarge support. A local interaction map supported on Z can enlarge a nonzero atom to Y union Z. Scalar atoms are killed by any generator perturbation annihilating I.

In an absolute-value atom expansion with exponential support weight a^|Y|, a>1, the reset contribution decreases that weight by

 4nu |Y| (1-1/a) a^|Y|.

A perturbation supported on Z incurs a factor at most a^|Z| and can meet every current site. Thus the familiar sufficient admission condition involves a small rooted sum of the form

 sup_i sum_{Z contains i} a^|Z| ||V_Z||_cb.

This recovers, rather than bypasses, the exponential-support-cardinality requirement already identified in the Crawford–De Roeck–Schuetz prior (arXiv1506.00530v2, Eq.2.7 and Remark3.3). No assertion is made that this particular absolute expansion is necessary for P5. Polynomial support weights do not automatically repair this elementary estimate: a total perturbation rate proportional to |Y| multiplies the whole polynomial weight, whereas independent reset decreases it only by a constant proportion per unit time at large |Y|. Cancellation or additional structure would be needed.

The available full-filter bounds14 control only finitely many commutator sums. They do not supply the displayed rooted exponential-cardinality decomposition for Qint, and equation (3) does not supply it either. Therefore the thermal reference removes one exact obstruction, but the attempted reset-history route returns to the previously recorded physical admission gap. There is no established invariant history domain here.

## Outcome

Equations (1)-(3), including the completely bounded relaxation estimate (2a), are the substantive self-check: the exact on-site thermal reference can be made CP with a quantified volume-independent noise floor, and the actual interacting remainder has the stated anchored norm bound. No Gibbs-weight assumption is needed. The next missing argument is a cancellation-preserving or otherwise controlled repeated full-filter history estimate for fixed-support inputs, or actual verification of the existing nonpositive stability theorem's rooted interaction norm. Neither the global inverse estimate17 nor the reset-history majorant supplies it. The original finite-window comparator join and full fixed-support P5 remain open.

Primary-source readback for this pass: Crawford–De Roeck–Schuetz, https://arxiv.org/html/1506.00530v2 , definitions (2.2), (2.7), and the explicit lattice domain. The support-norm and reference checks above are distinct; only the latter is supplied here.

## Coordinating hand review and attribution — 16 October 2026, 22:42 UTC

The coordinating dot contributor read the full candidate and hand-checked the Kossakowski perturbation estimate, reset identity and completely bounded 2 exp(-4nu t) bound, and the unitary variation estimate. The review prompted explicit comparison with the original recorded damping margin; the exact source and elementary implication are now supplied above. Acceptance is scoped to these reference and remainder estimates, not full interacting history admission, the entire external stability theorem, P5 closure or novelty. The reset expansion and product-mixing method are established mathematics; this note checks their applicability to the exact on-site physical reference.

The initial unreviewed bytes are preserved locally with SHA256 f361e416787d66d894e6f00e5bec05a0e92aa28684779e972d9d7f683a0c677e. This successor adds the source-backed margin implication, clarifies status and records the limited review; equations (1)-(3) and the remaining history gap are unchanged.
