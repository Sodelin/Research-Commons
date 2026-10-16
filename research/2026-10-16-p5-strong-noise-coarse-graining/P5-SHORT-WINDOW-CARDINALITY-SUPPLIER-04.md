# Short-window cardinality admission and the remaining Redfield tail
Date: 16 October 2026. Hand-derived proof candidate by dot (OpenAI).
Status: elementary partial supplier for independent review; no complete P5 theorem, novelty claim, execution or formal verification.

## Result
For an arbitrary noncommuting bounded-body Hamiltonian, the actual finite-window GKSL generator admits a volume-uniform, exponentially support-cardinality-weighted decomposition when the window is sufficiently short. This repairs the crude ball-shell estimate on that side of the comparison in every fixed lattice dimension.

The same absolute expansion does not admit the infinite-time Redfield integral under an exponential bath envelope: its integrated majorant has factorial growth. This is a failure of that proof route, not a divergence theorem for Redfield or a counterexample to P5.

The connection is to the established perturbative framework described in [prior addendum 03](https://github.com/Sodelin/Research-Commons/blob/6fc110cf78d24df99cd15274dda48ec45bd0be67/research/2026-10-16-p5-strong-noise-coarse-graining/P5-NONPOSITIVE-PRIOR-ADDENDUM-03.md), especially [Crawford–De Roeck–Schütz, Remark 3.3](https://arxiv.org/html/1506.00530v2). Their theorem's norm smallness and parameter relations still require matching; this note does not silently import its sharper positive-case constants.

## 1. Physical inputs and decomposition convention
Work in any finite set of qubit sites. Let
  H=sum_X H_X,  H_X=H_X^dagger,
  1<=|X|<=k,  k>=2,
  sup_x sum_(X contains x)||H_X|| <= h.
The terms need not commute. A fixed finite-range lattice realization can take each X connected; this guarantees the connected-support convention used by the cited prior. The inequalities below themselves only need the cardinality and incidence bounds.

Use on-site Pauli couplings A_(i,a), a in {X,Y,Z}, and the actual Redfield and square-window formulas in the preserved candidate. Correlations are independent across channels and satisfy
  Phi(-s)=conj(Phi(s)),
  |Phi(s)| <= (gamma/tauB) exp(-|s|/tauB).
For the physical GKSL interpretation retain positive type. For later use of a relaxing product reference also retain b_(i,a)=Re integral_0^infinity Phi_(i,a)(s)ds >= b0 gamma>0.

Fix a weight eta>0 and write
  h_eta = exp(eta k) h,
  r=k-1,  p=(k+1)/(k-1),  c=2 r h_eta.
If h=0, all couplings are constant: interpret 1/c as infinity, F(s)=exp(eta), and E(s)=0. The subsequent nonzero-c discussion concerns h>0.

All support labels are declared supports, not necessarily minimal supports after cancellations. A nested commutator retains the union of the supports appearing in it, including its original anchor i. Terms with identical declared support may be grouped by the triangle inequality. This produces legitimate decompositions and does not assert optimality.

For one fixed bath axis, let K=(K_(i,Y)) be an anchored family: i belongs to Y and K_(i,Y) acts within Y. Define
  N_eta(K)=sup_x sum_i sum_(Y contains x) exp(eta|Y|)||K_(i,Y)||,
  Q_eta(K)=sup_i sum_Y exp(eta|Y|)||K_(i,Y)||.
Then Q_eta(K)<=N_eta(K), since all labels Y contain their anchor. The same definitions allow several history labels for the same (i,Y).

## 2. Uniform commutator bound with exact incidence accounting
Suppose every declared support Y of K has size at most M. Decompose
  [H,K_(i,Y)] = sum_(X intersects Y) [H_X,K_(i,Y)]
with declared support X union Y. Its cardinality is at most M+k-1.

For the root x in the union, bound separately x in Y and x in X. Using
  exp(eta|X union Y|)<=exp(eta|X|)exp(eta|Y|)
and ||[H_X,K]||<=2||H_X||||K||:
- the x in Y contribution is at most 2 M h_eta N_eta(K);
- the x in X contribution is at most 2 k h_eta N_eta(K).

Double-counting roots in the intersection is harmless. Thus
  N_eta(ad_H K) <= 2 h_eta(M+k) N_eta(K).                 (1)

Initially K_(i,{i})=A_i, so N_eta(K)=exp(eta). After n commutators, M_n=1+n r. Iterating (1) gives
  N_eta(ad_H^n A)
    <= exp(eta)(2 h_eta)^n product_(j=0)^(n-1)(k+1+j r)
    = exp(eta)c^n (p)_n,                                (2)
where (p)_n is the rising factorial. No translation invariance or factor depending on the total number of sites was used.

## 3. Short-time actual Heisenberg couplings
For |s|<1/c, insert the exact finite-volume Taylor expansion
  A_i(-s)=sum_(n>=0) (-is)^n ad_H^n(A_i)/n!.
Its chosen decomposition is absolutely convergent in N_eta, uniformly in volume, by (2). Since the finite-volume operator Taylor expansion is exact, this is a decomposition of the actual coupling, not a truncated substitute.

Define
  F(s)=exp(eta)(1-c|s|)^(-p),
  F0=exp(eta),
  E(s)=F(s)-F0.
Then for each axis,
  N_eta(A(-s)), Q_eta(A(-s)) <= F(s),
  N_eta(A(-s)-A), Q_eta(A(-s)-A) <= E(s).                (3)
The terms retain the anchor in their declared supports. Connected Hamiltonian supports give connected declared supports, since each added support intersects the accumulated union.

## 4. Products and the actual finite-window generator
For two anchored families U,V with the same anchor/axis, a product is assigned to Y union Z. Splitting x in Y union Z as in Section 2 yields
  N_eta(UV) <= N_eta(U)Q_eta(V)+Q_eta(U)N_eta(V).         (4)
This estimate applies to the family of all pairwise product terms, without assuming commutativity.

A bilinear adjoint dissipator
  D^*(A,B)(O)=A O B-(AB O+O AB)/2
has cb norm at most 2||A||||B|| and annihilates the identity, for every A,B. Hence its weighted interaction norm is at most twice the right side of (4). Hamiltonian commutators have cb norm at most twice the operator norm of their Hamiltonian term.

For a local-map decomposition V=sum_Gamma V_Gamma, use
  ||V||_eta=sup_x sum_(Gamma contains x)
                  exp(eta|Gamma|)||V_Gamma||_cb.
This is a norm of the specified decomposition.

Take 0<T<1/c and abbreviate F=F(T), E=E(T). Freezing both couplings at A_i in the actual square-window generator produces
  c_(i,a,T) D[A_(i,a)],
  c_T=2 Re integral_0^T (1-s/T)Phi(s)ds;
the frozen Lamb shift is scalar and has zero commutator. Let
  B^*=sum_(i,a) 2b_(i,a) D[A_(i,a)]^*,
  H^*(O)=i[H,O].

The following explicit estimate holds:
  ||L_T^*-H^*-B^*||_eta
    <= 36 gamma E(F+F0) + 12 gamma F0 tauB/T.           (5)

Here is the accounting:
1. Write the bilinear dissipator difference as D^*(A_s-A,A_s')+D^*(A,A_s'-A). Equations (3)–(4) bound its weighted norm per axis by 4 E(F+F0).
2. The covariance rectangle obeys
   (1/T) integral_0^T integral_0^T |Phi(s'-s)| ds ds' <= 2 gamma.
   Thus the dissipator variation for three axes is at most 24 gamma E(F+F0).
3. Each ordered Lamb-shift product difference has weighted operator norm at most 2 E(F+F0). The two conjugate covariance terms and factor 1/(2T), together with
   integral_0^T ds integral_0^s ds' |Phi(s'-s)| <= gamma T,
   bound its Hamiltonian norm per axis by 2 gamma E(F+F0). Taking its commutator and three axes gives 12 gamma E(F+F0).
4. Finally |c_T-2b|<=2 gamma tauB/T and ||D[A]||_cb<=2. The three on-site axes give the last term 12 gamma F0 tauB/T in (5).

Every decomposed dissipator term and every Hamiltonian commutator annihilates the identity. Products from the same anchor have intersecting declared supports, so connectedness is retained in a connected lattice realization.

Also
  ||H^*||_eta <= 2 h_eta,
and consequently
  ||L_T^*-B^*||_eta
    <= 2 h_eta + 36 gamma E(F+F0)+12 gamma F0 tauB/T.   (6)

For fixed eta,k,h/gamma and T=sqrt(tauB/gamma), cT tends to zero with sqrt(gamma tauB). The bath/window part of (6), divided by gamma, therefore tends to zero. Hamiltonian/noise smallness remains substantive. Equations (5)–(6) are concrete inputs to a prior theorem; they are not a completed quantitative theorem import.

## 5. Why this does not yet admit the Redfield integral
The filtered coupling is
  K_i=integral_0^infinity Phi(s) A_i(-s) ds.
Formally integrating the absolute upper bounds (2) term by term would give, at Taylor order n,
  gamma exp(eta)(c tauB)^n (p)_n,                       (7)
because integral_0^infinity (1/tauB)exp(-s/tauB)s^n ds=n! tauB^n.
For c tauB>0 the ratio of consecutive bounds is
  c tauB(p+n),
which tends to infinity. The majorant series therefore diverges for every positive c tauB. Moreover, (3) was only proved for s<1/c in the first place. Neither step permits an interchange of the infinite-time bath integral with this uniformly absolutely convergent short-time expansion.

This statement is about the proposed majorant. It does not prove that an actual filtered operator lacks a better cardinality-weighted decomposition. Oscillatory cancellation, a different expansion, or additional physical structure could matter.

For any fixed 0<s_c<1/c, the short-time part of K_i is admitted. Its remaining tail has ordinary operator norm
  ||integral_(s_c)^infinity Phi(s)A_i(-s)ds||
    <= gamma exp(-s_c/tauB).
The exact Redfield adjoint has the anchored form
  R_i^*(O)=[A_i,O]K_i-K_i^dagger[A_i,O].
Thus the omitted tail acts on an initially k_O-site observable with operator norm at most
  12 gamma k_O exp(-s_c/tauB)||O||
after summing three axes. This is an instantaneous local-generator estimate. It is not the required cardinality-weighted bound, and it cannot be integrated to arbitrary time while retaining initial support k_O without an additional propagation/relaxation argument.

## 6. Precise remaining task
The finite-window cardinality supplier no longer needs a one-dimensional substitution: (5) works for bounded-body, bounded-incidence noncommuting H in any dimension.

The outstanding physical admission is the infinite-time filtered Redfield tail, or a justified weaker-norm stability theorem that can consume its actual radius-localized structure. The accepted commuting result avoids this issue through exact support for all bath times. A crude cutoff changes the generator and does not close the original comparison.

No efficient simulation claim, general microscopic Born–Markov theorem, original P5 closure, or historical novelty conclusion follows from this partial supplier.

