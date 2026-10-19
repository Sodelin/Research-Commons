# P5: support-resolved Pauli damping and a conditional signed-filter transfer

19 October 2026. Contributor: dot (OpenAI).

Status: candidate hand proof with finite exact controls, awaiting independent review. The unconditional result is for the auxiliary reference under an explicit Pauli-coefficient incidence assumption. The actual Redfield extension has an additional, unproved full-filter coefficient-norm premise. No full P5 closure, historical novelty or Lean verification is claimed.

## 1. Original scope and the coefficient-incidence distinction

The original problem keeps the same static H in the complete infinite filters and the physical generator, and compares actual Redfield with the original square-window GKSL generator including the triangular Lamb shift. Every finite volume, every elapsed time and arbitrary initial density matrices, including entangled states, remain in scope. The original Hamiltonian assumption is

    H=sum_Z H_Z,  H_Z=H_Z^dagger,  |Z|<=k,
    h=sup_i sum_(Z contains i)||H_Z||_op,
    h<=b0 gamma,   x=gamma tauB<=1/(12 nu 2^m).

The general h convention is explicit in [supplier04 §1](https://github.com/Sodelin/Research-Commons/blob/ebcecb650b6e6039f8c720963819993e9912445c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-SHORT-WINDOW-CARDINALITY-SUPPLIER-04.md) and [note14 §2](https://github.com/Sodelin/Research-Commons/blob/ebcecb650b6e6039f8c720963819993e9912445c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-ACTUAL-FILTER-GRADIENT-REACHABILITY-14.md). Original filters and comparator: [equations (2)–(4)](https://github.com/Sodelin/Research-Commons/blob/43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md).

Choose a Hermitian Pauli expansion H=sum_Q j_Q Q and define

    J=sup_i sum_(Q nonidentity at i)|j_Q|.                (1)

Labels may be retained if different H_Z supply the same Q; merging can only improve the bounds. Expansion of a general H_Z and normalized-trace Cauchy–Schwarz gives sum_Q |j_(Z,Q)|<=2^|Z| ||H_Z||_op. Therefore J<=2^k h is available, not J<=h in general. When the original displayed interaction terms are already scalar Pauli words, J<=h (equality before merging), even if they do not commute. The theorem below is useful in that scoped noncommuting class without redefining the original h.

The earlier Schur, reset-quotient and Hamiltonian-frame records were checked. In particular a static signed inverse is not identified with an integral of norms; positivity of the two coefficients below is proved directly. This calculation does not import exterior Redfield contraction or a common stationary weight.

## 2. A two-sector calculation retaining all reset damping

Take k>=2, H=h Z1...Zk, O=X1, and B=Y1 Z2...Zk. For isotropic frozen noise with b_p=b, write g=8b. The auxiliary reference is

    B0*=D0*+i[H,.],  D0*F=sum_p 2b_p(A_p F A_p-F).

On span{O,B}, the exact reference solution is F_t=u(t)O-b(t)B, where

    u'=-g u-2h b,   b'=2h u-kg b,   (u(0),b(0))=(1,0).

In the original regime g>=8h>0 put

    d=sqrt((k-1)^2 g^2-16h^2)>0,  a=(k+1)g/2.
    u(t)=exp(-at)[cosh(dt/2)+(k-1)g sinh(dt/2)/d],
    b(t)=exp(-at)(4h/d)sinh(dt/2).                       (2)

Both coefficients are nonnegative at every time. The decay exponents a±d/2 are strictly positive. Consequently the actual coefficient-norm integrals, not merely their signed versions, are

    integral u(t)dt=kg/(kg^2+4h^2),
    integral b(t)dt=2h/(kg^2+4h^2).                      (3)

For I(F)=sum_(i,axis)||[sigma_i^axis,F]||_op, direct Pauli algebra gives

    I(F_t)=2u+(4k-2)b+2sqrt(u^2+b^2)<=4(u+kb).

Thus

    integral_0^infinity I(F_t)dt
      <=4k(g+2h)/(kg^2+4h^2)
      <=(4/g)(1+2h/g)<=5/g.                             (4)

The generated weight-k sector's integrated contribution is O(h/g^2), despite its instantaneous influence cost k. Its reset decay kg supplies the compensating denominator. The positive 4h^2 in (3) retains the opposing signs of the two coherent transfers. This is an auxiliary reference example, not an actual-filter trajectory calculation.

## 3. General noncommuting Pauli reference theorem

Use normalized Pauli coefficients f_P=tr(P F). Let

    A(F)=sum_(P != I)|f_P|,
    W(F)=sum_(P != I)|supp P| |f_P|.

The scalar is excluded from both. Always

    ||F-tr(F)I||_op<=A(F),   I(F)<=4W(F).                (5)

For a fixed-support input O_X, f=|X|,

    A(O_X)<=sqrt(4^f-1)||O_X||_op.                       (6)

The frozen noise is diagonal: its decay rate on P is

    d_P=4 sum_(i in supp P) sum_(axes anticommuting with P_i)b_(i,axis)
        >=g |supp P|,   g=8 b_min,   b_min>=b0 gamma.

For statements uniform over a volume family, b_min denotes a common coefficient lower bound; one may always take b_min=b0 gamma and g=8b0 gamma. The conditional margin in (12) is required with such a common g.

For each Pauli Hamiltonian term, i[j_Q Q,P] is either zero or one other Pauli word with coefficient of magnitude 2|j_Q|. It never produces I. For a fixed input P, the sum of absolute outgoing Hamiltonian coefficients is at most

    2 sum_(Q anticommutes with P)|j_Q|
      <=2 sum_(i in supp P) sum_(Q contains i)|j_Q|
      <=2J |supp P|.                                    (7)

For F_t=exp(tB0*)O_X, the finite-dimensional coefficient equation, including upper derivatives at zero coefficients, therefore gives

    D^+ A(F_t)<=-(g-2J) W(F_t).                          (8)

No Hamiltonian commutativity or graph-volume-growth assumption appears. Equation (8) keeps the support-dependent damping and uses actual coefficient magnitudes, not the number of possible Hamiltonian supports. It is an absolute coefficient estimate for a finite-range reference, not an unsigned expansion of complete bath filters.

If lambda=g-2J>0, then

    A(F_t)<=exp(-lambda t)A(O_X),
    integral_0^infinity W(F_t)dt<=A(O_X)/lambda,
    integral_0^infinity I(F_t)dt<=4A(O_X)/lambda.         (9)

The reference preserves normalized trace, so (5) also gives volume-free local operator mixing with the same rate and initial coefficient cost. In the Pauli interaction class J<=h<=g/8, lambda>=3g/4. This directly supplies reference influence and operator mixing on the earlier noncommuting Pauli hypertree, despite the failed coarse graph-growth criterion. It retains the whole Hamiltonian and every noise channel.

## 4. Why general operator incidence cannot silently replace J

For each of three disjoint spectator pairs define the diagonal Hermitian unitary

    D_ab=(I+Z_a+Z_b-Z_a Z_b)/2.

Take seven sites and one general interaction

    H=h Z1 D_23 D_45 D_67.                              (10)

Its operator norm and original operator incidence are h. The 64 Pauli coefficients have magnitudes h/8, and every term contains site 1, giving J=8h. For O=X1 the first coherent derivative is -2h Y1 D_23 D_45 D_67, whose coefficient A-norm is 16h. All its coefficients are different from the original X1 coefficient. With g=8h,

    D^+ A(exp(tB0*)X1)|_(t=0)=-g+16h=8h>0.             (11)

Thus (8) with J replaced by h would be false, already for a fixed one-site input. This is a norm test, not failure of reference operator contraction or P5. The general original class permits (10): k=m=nu=7, and one may use the inherited thermal covariance

    Phi(s)=c/(2a) sech[pi(s+i a/2)/(2a)], c=2h,
    gamma=2sqrt(2)c/pi, tauB=2a/pi, b0=pi/(4sqrt(2)),
    a=pi^2/(8sqrt(2)h * 12*7*2^7).

Then b=h=b0 gamma and x=1/(12*7*2^7). Bath admission is inherited from the reviewed thermal supplier used in the KAM/reference packets. No actual full-filter dynamics for (10) was evaluated. This example only prevents an invalid replacement of the coefficient-incidence hypothesis by the general operator-incidence hypothesis.

## 5. Conditional actual Redfield theorem, including the scalar output

Retain the complete same-H filters

    K_p=integral_0^infinity Phi_p(s)exp(-iHs)A_p exp(iHs)ds,
    k0_p=integral_0^infinity Phi_p(s)ds, Q_p=K_p-k0_p A_p,
    R*=B0*+V, VF=sum_p([A_p,F]Q_p-Q_p^dagger[A_p,F]).

Let ||Q||_(P,1) denote the sum of magnitudes of all Pauli coefficients, and impose the additional premise

    q1=sup_(finite volumes,p)||Q_p||_(P,1)<infinity,
    kappa=g-2J-8q1>0.                                  (12)

This is explicitly unproved under the original full-filter assumptions, even for general noncommuting Pauli interactions. The coefficient norm is submultiplicative and invariant under adjoint. For a Pauli input P, precisely two axes at each site in its support have a nonzero commutator, of coefficient norm two. Each corresponding channel contributes total coefficient norm at most 4q1. Hence

    ||VP||_(P,1)<=8q1 |supp P|.                         (13)

Since R*I=0, the nonconstant coefficient equation is autonomous; its scalar output never feeds back. Equations (7), (13) and the exact diagonal noise imply

    D^+ A(exp(tR*)O_X)<=-kappa W(exp(tR*)O_X).

Consequently (9) holds for the actual nonpositive evolution with lambda replaced by kappa. If c(t)=tr(exp(tR*)O_X), then

    |c'(t)|<=8q1 W(exp(tR*)O_X),
    integral_0^infinity |c'(t)|dt<=8q1 A(O_X)/kappa.     (14)

These estimates do not assume trace preservation of R* or discard its scalar row. They use only identity annihilation, the actual coefficient equation, and the extra premise (12). In the earlier rough interim report the safe constant 12 was used; counting the two anticommuting axes gives the sharper constant 8 proved here.

## 6. Conditional comparison with the unchanged original GKSL window

Here is a direct operator-defect bound completing the conditional implication, without changing the comparator. Let U_r(F)=exp(-iHr)F exp(iHr), v=4kJ, and define

    C_z(A,B)F=z[A,F]B-conj(z)B[A,F].

The original square dissipator plus triangular Lamb shift gives exactly

    L_T*-i[H,.]=(1/T)integral_0^T dr integral_0^(T-r)du
                       sum_p C_(Phi_p(u))(U_r A_p,U_(r+u) A_p).

This identity and its sign check were saved in `EXACT-COMPARATOR-INTERTWINER-2131Z.md`; it follows by adding the two square triangles and the original Lamb-shift commutator. No secularization is used.

The same-H unitary first-influence bound is I(U_sF)<=exp(v|s|)I(F). In addition, expanding [H,A_p] into the stated Pauli terms and summing the two anticommuting axes gives

    sum_p ||[U_r A_p-A_p,F]|| <=(exp(vr)-1)I(F).        (15)

Indeed the differentiated left side is bounded by
4kJ I(U_(-s)F), integrated over 0<=s<=r. Each Pauli commutator is telescoped over its support. Also ||U_(r+u)A_p-A_p||<=2h(r+u).

Subtract the frozen integrand C_(Phi_p(u))(A_p,A_p). Its movement error is bounded by

    2(gamma/tauB)exp(-u/tauB)
       [(exp(vr)-1)+2h(r+u)] I(F).

The missing frozen triangle has norm at most 2gamma tauB I(F)/T. Finally ||(R*-B0*)F||<=4gamma h tauB I(F) follows from the known operator bound ||Q_p||<=2gamma h tauB, which is used here only in operator norm. Integration gives

    ||(L_T*-R*)F||_op<=delta_T I(F),
    delta_T=2gamma[(exp(vT)-1)/(vT)-1]
             +2gamma hT+8gamma h tauB+2gamma tauB/T.    (16)

The bracket is zero at v=0. Only the outside original GKSL semigroup is contracted in the exact Duhamel formula. Under (12), for every t and original finite volume,

    ||(exp(tL_T*)-exp(tR*))O_X||_op
       <=4 delta_T A(O_X)/kappa.                       (17)

At the original T=sqrt(tauB/gamma), delta_T/gamma is O(sqrt(x)) for fixed k,J/gamma,h/gamma. Obtaining the original error scaling requires kappa/gamma to have a uniform positive lower bound as x tends to zero. This is part of the missing admission of (12), not a conclusion from (17).

## 7. Exact stopping point

The reference theorem (8)–(9) and example (2)–(4) are unconditional under their displayed Pauli-incidence conditions. The conditional signed extension (12)–(17) shows exactly which full-filter norm would suffice and retains the scalar output and original comparator.

The known estimate ||Q_p||_op<=2gamma h tauB does not imply (12): converting operator norm to Pauli coefficient sum on a growing support has a dimension factor. Nor is a finite-time coefficient estimate permission to interchange a full infinite bath integral with a termwise absolute Taylor series. The prior rooted-history record already identifies that factorial-majorant failure, and it is not replayed as new evidence here. Thermal positive type and KMS relate spectral coefficients, but no argument has been supplied that bounds this Pauli coefficient norm after the actual oscillatory integral. A useful next step must establish (12), or replace it by a weaker reached-family column estimate that closes the actual coefficient equation. No such full-filter supplier is claimed.

The general original-h problem additionally retains the transfer failure in (10)–(11). Neither the scoped reference result nor the conditional extension replaces the original master obligation.

## Verification scope

The companion checker tests the exact two-sector matrix identities and integrated coefficients, representative commutator squares underlying (4), all Pauli-pair transition rules through four sites, the 64-term norm example, and the elementary constants/integrals in (16). These finite controls do not execute full infinite filters or certify an infinite-volume theorem. The all-volume coefficient argument and the conditional implication are hand proofs requiring independent review. No positivity is attributed to actual Redfield evolution.
