# P5: original full-filter counterexample proof packet

Edition2: explicit thermal-envelope, noise-floor and ORIGINAL comparator proof included. Edition1 is preserved at SHA256 70becba502bdbacaa27714d9146bb0d238fa2f71cc53956e64c1d0aa32f8fc81.

21 October 2026. Complete authored HAND derivation, partly audited and
still under review. This export is not an independently accepted full
resolution, a large-system computation, Lean verification or a claim of
historical novelty. The persistent P5 goal remains active. No local Git
change, new chat, sub-agent or held execution is part of this packet.

The claimed result is failure of the unrestricted original comparison:
for arbitrarily small FIXED original x, fixed j,b0,k,m,nu and one fixed
three-qubit Pauli observable O, admitted finite systems have unbounded
original Redfield predictions. The original same-H square-window GKSL
prediction is bounded by1, so their discrepancy is unbounded. This is
the original-comparator claim, not merely failure of a sufficient
influence bound or nonpositivity on a growing initial support.

Every mathematical supplier in the final analytic implication has a
hand proof included below. The remaining evidence boundary is full
independent acceptance of that assembled proof. The current scoped
reviews are: D3/D5 under their finite-tensor hypotheses;
T4/T7 conditional on the displayed commutation/tail/cb premises;
and C4 gauge/isometry/S5 conditional on S3 and exact embeddings.
They are attributed assistant hand audits, not external peer review or
full formal checks. The current mutable review ledger remains authoritative
for subsequent evidence; this export freezes the present source state.

## Exact original target and comparator

The authoritative contract is the18 October closing handoff:
https://docs.google.com/document/d/1mMx52upWlAWHs3KkHqlETT80KxC5VdhSCDlq0Ene7Ec/edit
and P5-SCOPE.md, SHA256
54c3a9563fdc7c82497dc815af5711fc720ec3866551037d7621bdb94ac4140e.
Finite systems are qubits, H=sum Hermitian H_Z, |Z|<=k,
h=max_i sum_(Z contains i)||H_Z||. Closed neighborhoods and their
multiplicity are bounded by m,nu. Every site has all three bare Pauli
channels with independent positive-type genuine thermal/KMS baths.

To avoid a normalization collision, baseline gamma below is NOT the
original common envelope parameter. The original parameter is
Gamma=9gamma/4. Its bath time is tau and

 |Phi_p(s)|<=(Gamma/tau)exp(-|s|/tau),
 Re integral_0^infinity Phi_p(s)ds>=b0 Gamma,
 h<=b0 Gamma, x=Gamma tau<=1/(12nu 2^m),
 j=h/Gamma, T=sqrt(tau/Gamma).

Write A_p(s)=exp(-isH)A_p exp(isH), so this is A_p(-s) in the source
handoff. The original Redfield filters and generator are exactly

 K_p=integral_0^infinity Phi_p(s)A_p(s)ds,
 R*(F)=i[H,F]+sum_p([A_p,F]K_p-K_p^dagger[A_p,F]).

For completeness, the original Schroedinger comparator is

 D_T(rho)=(1/T)sum_p integral_(s,s' in[0,T]) Phi_p(s'-s)
   [A_p(s')rho A_p(s)-{A_p(s)A_p(s'),rho}/2] ds ds',

 H_T=(i/(2T))sum_p integral_(0<=s'<=s<=T)
   [Phi_p(s'-s)A_p(s)A_p(s')-Phi_p(s-s')A_p(s')A_p(s)] ds ds',

 L_T(rho)=-i[H+H_T,rho]+D_T(rho).

These preserve the literal ordered Lamb shift. The SAME H and baths are
used on both sides. Positive type makes D_T a GKSL dissipator and
covariance symmetry makes H_T Hermitian. Therefore exp(s L_T*) is unital
and completely positive, with Hermitian norm-one predictions bounded by1.
No such assumption is made about exp(sR*).

The target is the operator-norm discrepancy on O_X, with X fixed, uniformly
over every admitted finite volume and every s>=0, for all initial density
matrices. The declared geometry permits bounded-degree binary trees;
translation invariance and polynomial ball growth are not required.
The counterexample is a parameter-uniform finite-model family, not a
claim that all its root covariances are restrictions of one nested model.
Within each selected model all parameters, baths and H are fixed in time.

## Binding conventions that are mandatory in this compilation

- H_blocks=sum of the three-qubit H_c terms; H_iso=h_*Z_isolated;
  H_total,0=H_blocks+H_iso; H_r=H_total,0-r*pi_all(K_0).
  The isolated term occurs EXACTLY ONCE. C4's H0 excludes it; T1/W2's H0
  includes it. All full and auxiliary filters use this same family.
- The local amplifier rotation v=y/144 in the C2 module is distinct from
  the physical bath-modulation parameter v in[-1,1] in the final family.
  The local reflection W is distinct from the clock gauge W(z).
- At complex r/u/v all adjoint filters have the specified analytic sharp
  using the SAME analytic parameters. It equals the literal adjoint only
  on the corresponding real parameters. No positivity is claimed there.
- rho_N is chosen ONCE from t_N. Varying observation time, r, root u or
  bath v never retunes the clock mixture. Untouched BASE blocks alone are
  contracted; touched factors remain in their complete physical algebra.
- Only ONE global logical probe is estimated by D5. Higher v orders use
  the coarse finite-volume exponential norm, not a multi-probe extension.
- The cutoff is an analytic increment cutoff. The ORIGINAL physical
  filters remain infinite. The delayed central pulse is matched exactly
  before its actual shifted-variable tails are estimated.
- The mandatory admission correction near the end applies to EVERY
  search specification. For a completely explicit computable family take
  gamma=1,tau=2^(-ell),ell>=40 and tree depth q>=4ell+80. No smaller q may
  be treated as an admitted initial mixture without another proof.

## A dimension-free scalar-functional fact used by D3/D5

For a scalar matrix functional phi and an arbitrary amplification Q,
the matrix element of (Id tensor phi)(Q) between u,v is phi of
(bra(u) tensor I)Q(ket(v) tensor I). This compressed operator has norm
at most||u|| ||Q|| ||v||. Hence ||Id tensor phi||<=||phi|| at every
amplification, with equality at amplification1. Iterating gives the
product bound for partial contractions on entangled logical Q. Physical
operators C_S on the retained factors pass through that partial map on
either side: it is a physical S-bimodule map. This proves precisely the
scalar cb and code-leaving contractions used in the Dyson source.

## Reading order and evidence

The modules below contain the model/claim, Gaussian admission, actual C2,
static C4 with its remaining premises, D3/D5, explicit W2/W4, actual T7,
the finite analytic endpoint I13, the fully real finite-grid corollary,
and the mandatory admission threshold. Historical candidate-status
paragraphs remain attributed to the pinned source that contains them;
the review boundary above states the current compilation's status.
Each module names its full-source hash and its exact included projection.

Existing finite synthetic controls have passed, including clock/gauge/
geometry identities, code-leaving contractions and interpolation rows.
The NEW admission correction's18 exact rational controls also passed.
These do not evaluate a large original-system prediction or prove the
all-volume theorem. Private full reports remain encrypted locally before
persistence; no runtime payloads are included in this authored export.

Primary prior ingredients retain their attribution: the original
Ikeuchi-Mori comparator is arXiv:2604.21366v2, equations19-20, and the
standard engineered spin-chain transfer ingredient is Christandl et al.,
quant-ph/0309131v2, equations12-15. The present parallel-clock/Dyson/
interpolation assembly is an authored composition, with novelty unassessed.


---

## Source module 1: P5-STATIC-CLOCK-ANALYTIC-COUNTEREXAMPLE-v1.md

Full-source SHA256: 204f368e17b6b544eda5b471237d505f997f26d50e3161a5c3a6f0a6a1de9540.

Included projection: source prefix before ## 5. A large coupled auxiliary response.

Projection SHA256: 3246b9c859fe8341071232a9aa689debd35e7e77640fedda0f3583ac7c3ba71b.

# Candidate obstruction to the unrestricted P5 comparison

21 October 2026. Self-reviewed mathematical proof candidate. NOT independently
accepted, formally checked or a declaration of P5 closure. The critical new
supplier is the touched-block estimate in CODE-FUNCTIONAL-DYSON-BOUND-v1.md.
This source assembles it with the earlier static-clock and thermal-amplifier
hand candidates. Finite controls of those components do not verify this
all-volume argument. No physical/model experiment is being reported.

## Candidate statement and fixed physical parameters

For arbitrarily small fixed positive x in the original parameter box, the
candidate construction below has fixed b0,j,k,m,nu, a FIXED three-qubit
support X, a FIXED Hermitian Pauli observable O_X of norm one, and positive
normalized initial densities, such that the supremum of its ACTUAL
Redfield predictions over admitted finite systems and times is infinite.
In fact the finite-family maximum P_N below grows at least

    P_N >= exp(c_y sqrt(N))                            (C1)

for sufficiently large N, where c_y>0 depends only on the fixed physical
parameters. All Hamiltonians are static and use the SAME full Hamiltonian
in every filter. All three bare Pauli channels at every physical site are
present in the admitted physical systems. No assumed actual positivity or
norm contraction appears in the proof.

If (C1) survives review, it disproves the desired finite uniform P5 bound:
the ORIGINAL square-window GKSL comparator, including its ordered Lamb
shift, has Hermitian predictions bounded by one. Its prediction difference
is therefore at least P_N-1 for the selected positive initial state.
The comparator is used only for this last bound, not as actual dynamics.

Use the thermal Gaussian from GAUSSIAN-THERMAL-RESPONSE-REDUCTION.md:

    Phi(t)=(gamma*c/tau) exp[-2(t/tau)^2] exp[-i t/(4tau)],
    c=exp(-1/8), b_G=c sqrt(pi/8)exp(-1/128), beta=tau/8.

Its strictly positive spectrum J_G satisfies the common KMS condition.
Every independent three-qubit amplifier block has

    H_c=(J/2)(Z1 X2+X2 Z3),

full Phi on sites1,2 and Phi/2 on site3, with all nine channels present.
Fix J=b_G gamma/32, omega_0=b_G gamma/96 and y=Jtau>0.
Common physical envelope and floor for the later admitted family are

    Gamma=(9/4)gamma,        b0=2b_G/9.

Choose Gamma*tau<=1/(360*2^30). This can be arbitrarily small but is
FIXED as N varies. An unrelated additional noisy qubit with the single
Hamiltonian term h_* Z, h_*=b_G gamma/4, fixes the EXACT original operator
incidence h=h_* in every volume and at every parameter value. The active
clock system has incidence at most J+3omega_0=b_G gamma/16<h_*.
Thus j=h/Gamma=b_G/9=b0/2 is fixed, with h<b0 Gamma.
The extra qubit is independent and has no effect on the root prediction.

## 1. The base code functionals, including intermediate times

Use W,G,S and pi from SYMMETRIC-AMPLIFIER-AND-CLOCK-PREIMAGES.md:

    pi(Z)=W, pi(X)=G=X1Y2X3, pi(Y)=iGW, S=Z1.

W is a balanced Hermitian unitary commuting with H_c; G anticommutes
with W, and both G,S are physical-Pauli symmetries of the actual base
generator. The Gaussian moment bound supplies

    kappa(s)=<000|exp(s R_c*)W|000>,
    kappa(0)=1, kappa'(0)>=2a0,
    a0=gamma*y^2/6912,  ||R_c*||_cb<=38gamma=:b.

For 0<=s<=a0/(2b^2), kappa is increasing and

    1+a0 s <= kappa(s) <= exp(bs).                    (C2)

Indeed |kappa'(s)-kappa'(0)|<=b(exp(bs)-1)<=2b^2s in
this interval, and its endpoint is well below log(2)/b. This also proves
the monotonicity needed below, not merely a lower bound at one time.

Let t_N=N^(-1/2)/gamma; take N large enough for the above interval.
On every non-root DATA block use the positive initial density |000><000|.
Its restricted logical functional at time s has representative
diag((1+kappa(s))/2,(1-kappa(s))/2), of trace norm kappa(s).

On every CLOCK qubit's physical block use the positive mixture

    rho_clock,0=w |000><000|+(1-w)|111><111|,
    w=(kappa(t_N)+1)/(2kappa(t_N)),

or the reversed mixture for bit1. At time s its logical Z expectation is
plus or minus kappa(s)/kappa(t_N), and X,Y expectations are zero.
By monotonicity, its restricted functional is POSITIVE and has norm one
for EVERY 0<=s<=t_N. At s=t_N it is exactly the prescribed pure clock bit.
This statement concerns the independent base blocks; coupling is estimated
by the Dyson lemma, not silently tensorized.

On the root use pi_root(Z)=S=Z1, pi_root(X)=G and pi_root(Y)=iGS.
The observable of interest is O=G on these SAME three physical qubits.
Take the positive root initial state (|000>+i|111>)/sqrt(2), an eigenstate
of G with eigenvalue +1. Both H_c and the entire logical clock Hamiltonian
below commute with this O.

In analytic calculations allow the root's nine unshifted bath strengths
to be u. At u=0 the root is noiseless, an auxiliary parameter value ONLY;
the admitted physical family will have 1<=u<=2. At u=0 the root functional
on O is identically one. Complex u is bounded physically on its root by
exp[t(2J+36gamma|u|)]. No root-zero model is claimed to satisfy P5.

Define the data norm factor

    A_N=kappa(t_N)^(N-1).

Equation(C2) gives, for large N,

    log A_N >= (y^2/27648)sqrt(N),
    log A_N <=38sqrt(N).                             (C3)

## 2. One static circuit Hamiltonian and one fixed local root

Take N vertices of a finite binary data tree, for example N=2^(q+1)-1.
The leaf-to-root CNOT(child -> parent) circuit has G_c=N-1 gates,
D<=2ceil(log2 N) disjoint layers and at most three gates per data vertex.
Use STATIC-PARALLEL-CLOCK-FANOUT.md at fixed frequency omega_0 and a fixed
isometry error epsilon_clock<=1/32. It gives an explicitly defined static
logical K_0 with one engineered qubit chain per gate, even chain parameter

    d=2ceil(4096D^2 log(e G_c D/epsilon_clock)),
    L_0=pi*d/(2omega_0).

Its block incidence is eta_0=3omega_0, its terms occupy at most four
logical blocks, and the number of three-qubit physical blocks is

    M_N=N+G_c(d+1)=O(N log^3 N).

Its actual prepared-clock compression, uniformly in the data state, is

    ||<c|Y_0|c>-Z_root product_(other data i) Z_i||<=delta_c,
    Y_0=exp(iL_0 K_0) Z_root exp(-iL_0 K_0),
    delta_c<=1/16.                                  (C4)

The source's noncommuting-gate gauge and concentration/Duhamel argument
prove (C4); no full-clock-space approximation is assumed. Every CNOT has
the root, if involved, as a TARGET, so [K_0,X_root]=0 exactly.

For a real r>0 the SAME physical Hamiltonian is

    H_r=sum_blocks H_c-r pi_all(K_0)+h_*Z_isolated.

Set r_N=N^(-1/3) and allow r in I_N=[r_N/2,r_N]. The source time is
L(r)=L_0/r, since U_(H_r)(L(r)) S_root=pi_all(Y_0) exactly.
The root O=G commutes with H_r for every r.
The original bounds are k<=12,m<=30,nu<=30, h=h_* as fixed above.
Every physical block and clock site retains its ordinary noise in the
admitted family. The factorized base is only an expansion point.

## 3. The admitted physical two-parameter root baths

For each r use L=L(r) and theta=delta_b/cosh(L/tau), delta_b=1/4.
Scale all root base channels by u in [1,2], and replace ONLY the root's
bare Z1 channel spectrum by

    J_(root,Z1)(omega)=J_G(omega)[u+v theta cos(omega L)],
                          -1<=v<=1.                 (C5)

Other root channels are their original site-scaled u copies. All other
blocks retain their original full/half copies. The bracket is at least
3/4, so every channel is positive type and strictly present. Cosine is
even, so the SAME KMS temperature beta is retained. The lag-envelope
bound from THERMAL-LAG-ADMISSION.md gives the common envelope Gamma=9gamma/4.
The minimum zero-frequency floor is b_G gamma/2=b0 Gamma. Thus ALL real
u,v in these intervals satisfy the ORIGINAL parameter box with fixed
b0,j,x,k,m,nu. The exact maximal h is fixed by the unrelated onsite term.

The covariance increment in (C5) is

    v theta [Phi(s-L)+Phi(s+L)]/2.

Let R(r,u,v) be the ACTUAL full-filter Redfield generator for this SAME
H_r and these baths. Its dependence on u,v is affine. Its operator/cb
norm on these real parameter intervals is <=C M_N gamma, with C fixed.
The probe coefficient has cb norm <=C theta gamma, independent of volume.

Use the product positive initial density rho_N defined in section1,
including the prescribed one-excitation clock string and the root G+
state. This density depends on N,t_N, but not on r,u,v. That dependence
on volume and selected observation time is allowed by P5.

Define the maximum of ORIGINAL predictions

    P_N=sup_(r in I_N,1<=u<=2,|v|<=1,0<=s<=t_N)
          |Tr[rho_N exp(s R(r,u,v)*) O]|.             (C6)

All systems inside this supremum are admitted physical systems. The
noiseless-root value u=0 is absent from (C6).

## 4. Same-H analytical auxiliaries with a vanishing actual error

Put R_N=32r_N and S_N=1/(1000eta_0 R_N). For large N this exceeds tau
and is smaller than every L(r). Define R_tilde(r,u) by the FULL independent
base filters plus the increments truncated to [0,S_N], exactly (D6).
Keep the full Hamiltonian H_r. Also define the analytic logical probe Q_r
by (D8) and its analytic sharp version. For real r its sharp is its adjoint.
Let

    P_r(F)=[S_root,F] Q_r-Q_r^dagger[S_root,F].

On the complex r disk use the separately defined analytic sharp, not
complex conjugation of r. The auxiliary probe generator is theta P_r.
The root sharp covariance uses the SAME complex u in the analytic extension.

For real r in I_N, u in [0,2], the actual unshifted baseline and this
auxiliary differ by at most C M_N gamma exp[-(S_N/tau)^2]. The actual
probe coefficient differs from theta P_r by at most
C theta gamma exp[-(S_N/tau)^2]. To see the latter, shift s=L+z in its
actual full integral. Its central range -S_N<=z<=S_N is exactly (D8)
because rL=L_0; the missing tails and the Phi(s+L) term are bounded by
the actual Gaussian tails, since L>S_N. This captures the finite pulse
width exactly, rather than using a crude O(h tau) approximation.

Let F_actual(u,s) be the derivative in v at zero of the prediction in
(C6), at a fixed real r. Let F_tilde(u,s) be that derivative for
R_tilde(r,u)+v theta P_r. Finite-volume exponential Duhamel gives,
uniformly for the real ranges just specified and 0<=s<=t_N,

    |F_actual(u,s)-F_tilde(u,s)|
      <=C theta gamma t_N(1+M_N gamma t_N)
          exp[C M_N gamma t_N-(S_N/tau)^2]=o(1).      (C7)

All actual norms and volume factors were retained. Indeed
M_N gamma t_N=O(sqrt(N)log^3 N), whereas
(S_N/tau)^2 is a fixed positive constant times N^(2/3).
No cutoff physical bath or CP response has replaced the original problem.
This estimate concerns the UNSHIFTED Gaussian baseline. The delayed pulse
was kept in Q_r and compared by its shifted integral, not discarded as a
baseline tail.


---

## Source module 2: GAUSSIAN-THERMAL-RESPONSE-REDUCTION.md

Full-source SHA256: d0f48bc9ef7ae94786f6fb4de60c5c5057b01002df03db94474dee392b6f996e.

Included projection: source prefix before ## A rigorous error bound.

Projection SHA256: 841bc18ca75055b1ab7f520e067298a19f866591b355a88d6893a84f18a7c32b.

# Admitted Gaussian thermal baths and an actual full-tail reduction

21 October 2026. Self-reviewed hand proof and bounded continuation target.
This does not prove coupled amplification or P5 failure. The auxiliary
cutoff below has an explicit actual-generator error; it does not replace
the original full infinite filters in the physical problem.

## Positive thermal Gaussian within the original exponential envelope

Let tau,gamma>0, c=exp(-1/8), a=1/4 and

    Phi_G(t)=(gamma*c/tau) exp[-2(t/tau)^2] exp[-i a t/tau].

In the convention J(omega)=integral Phi(t)exp(i omega t)dt its exact
spectrum and temperature are

    J_G(omega)=gamma*c*sqrt(pi/2) exp[-(omega*tau-a)^2/8],
    beta=a*tau/2=tau/8>0.

The Fourier formula follows, for example, by differentiating the Gaussian
Fourier integral: F'(w)=-(w/4)F(w), F(0)=sqrt(pi/2). Therefore J_G is
strictly positive and J_G(-omega)=exp(-beta*omega)J_G(omega). Fourier
inversion makes every finite positive-type quadratic form an integral of
J_G times an absolute square. Hermitian covariance symmetry is immediate.
The positive-frequency bosonic coupling density
J_G(omega)(1-exp(-beta*omega))/(2pi) is nonnegative. Thus this is a genuine
thermal source at the SAME beta for all positive scaled channel copies.

Because -2z^2+|z|<=1/8,

    |Phi_G(t)|<=(gamma/tau)exp(-|t|/tau),
    Re integral_0^infinity Phi_G(t)dt=b_G gamma,
    b_G=c sqrt(pi/8) exp(-1/128)>0.                 (1)

In the symmetric amplifier, give sites1,2 Phi_G and site3 (1/2)Phi_G.
All nine physical channels remain and the floor is b0=b_G/2. Choose
J<=b0 gamma, gamma tau<=1/288 for its independent three-qubit model;
the static clock embedding uses its stronger fixed m,nu=30 box as before.

## The same symmetric witness retains its explicit time/gain

Put y=Jtau and use v=y/144 and the EXACT W,G,S of
SYMMETRIC-AMPLIFIER-AND-CLOCK-PREIMAGES.md. Its algebra, physical-Pauli
covariances and clock-mixture identities did not depend on the sech form.
The moment bound needed there is also supplied here:

    mu1=integral_0^infinity s Re(Phi_G(s))ds
       >=gamma*c*tau(1/4-a^2/16)
       >=(441/2048)gamma*tau,
    integral_0^infinity s^3|Phi_G(s)|ds
       =gamma*c*tau^3/8<=gamma*tau^3/8.

The first inequality uses cos(az)>=1-a^2z^2/2 and c>=7/8.
Using the ABSOLUTE sine remainder |sin z-z|<=|z|^3/6 gives

    Re(D1)>=gamma*y[441/2048-y^2/48]>=gamma*y/24,
                     0<y<=1/288.                   (2)

This absolute-remainder argument is necessary: Re Phi_G changes sign
far in the Gaussian tail. It is not being treated as everywhere positive.
Also Re(C1)<=gamma by (1). Consequently the earlier exact transition
proves a>=gamma*y^2/6912 and, at every 0<t<=t_s,

    kappa(t)=<000|exp(t R_c^*)W|000>
       >=1+(gamma*y^2/6912)t,
    t_s=y^2/(9980928gamma).                          (3)

At t_s this includes the earlier explicit gain >=1+y^4/68988174336.
The short-time form follows from 2a0t-(38gamma)^2t^2>=a0t.
For ANY such t the physical clock mixtures defined using
p(t)=(kappa(t)-1)/2 give the exact pure logical clock functional at that
selected time. They are allowed positive initial densities and may depend
on the volume-dependent observation time. This is still an independent
base-block functional statement.


---

## Source module 3: P5-GAUSSIAN-AMPLIFIER-C2-v1.md

Full-source SHA256: 10b7507cf809a22348b9b5ac82eabd1c868b9de76ec7b25074366339a0ff3f54.

Included projection: complete source.

Projection SHA256: 10b7507cf809a22348b9b5ac82eabd1c868b9de76ec7b25074366339a0ff3f54.

# C2: actual Gaussian amplifier and every-duration clock functional

21 October 2026. A literal HAND supplier for the analytic counterexample.
It isolates the Gaussian version of the symmetric block and the
intermediate-duration property required by D5. No independent acceptance,
formal check or new finite-control run is asserted.

## The actual complete block, with all nine channels

On three physical qubits take

 H_c=(J/2)(Z1X2+X2Z3),
 Phi(s)=(gamma*c/tau)exp[-2(s/tau)^2]exp[-is/(4tau)],
 c=exp(-1/8), y=Jtau in(0,1/288], J<=gamma.

The independent baths on sites1,2 have Phi; those on site3 have Phi/2.
Every site has ALL three bare Pauli channels. The spectrum, thermal KMS
condition, common exponential envelope and nonzero floor are derived in
GAUSSIAN-THERMAL-RESPONSE-REDUCTION.md, SHA256
d0f48bc9ef7ae94786f6fb4de60c5c5057b01002df03db94474dee392b6f996e.
In particular ||K_A||<=gamma for EVERY full filter
K_A=integral_0^infinity Phi_p(s)exp(-isH_c)Aexp(isH_c)ds.

Use the actual Heisenberg Redfield generator

 B(F)=i[H_c,F]+sum_A([A,F]K_A-K_A^dagger[A,F]).

It is unital and preserves adjoints; it is not assumed positive or
contractive. Since ||H_c||=J, a valid cb bound is

    ||B||cb<=2J+36gamma<=38gamma=:b.                (A1)

Put v=y/144 and define the EXACT physical vectors and operators

 phi_A=(iv|100>+|110>)/sqrt(1+v^2),
 phi_B=(-iv|001>+|011>)/sqrt(1+v^2),
 P=|phi_A><phi_A|+|phi_B><phi_B|
                         +|101><101|+|111><111|,
 W=I-2P, G=X1Y2X3, S=Z1,
 rho_+=|000><000|, rho_-=|111><111|.

These give W^dagger=W, W^2=I, Tr W=0, W|000>=|000>,
W|111>=-|111>, and

 [H_c,W]=[H_c,G]=[H_c,S]=[S,W]=0,
 GWG=-W, SGS=-G.                                  (A2)

For completeness H_c vanishes on the two sectors spanned by{100,110}
and{001,011}. It exchanges000,010 and exchanges101,111, on each of
which W is scalar. Explicitly

 G phi_A=(-i|001>-v|011>)/sqrt(1+v^2),
 G phi_B=(-i|100>+v|110>)/sqrt(1+v^2),
 G|101>=i|010>, G|111>=-i|000>.

The first two are orthogonal to phi_B and phi_A respectively. Thus G
maps the entire four-dimensional P range onto its orthogonal complement,
which proves GWG=-W. The other relations follow from the displayed
Pauli products and the S-invariance of each sector.

## Full-filter transition, without removing other channels

Let C1=integral_0^infinity Phi(s)cos(Js)ds,
D1=integral_0^infinity Phi(s)sin(Js)ds, r=Re C1, d1=Re D1.
Since P|000>=0, the transition under the ACTUAL Schroedinger adjoint is

 Tr[P B_*(rho_+)]=sum_A 2Re <A000|P K_A|000>.       (A3)

The Hamiltonian contribution vanishes since[H_c,P]=0. The two
anticommutator terms vanish because P|000>=0. A channel with P A|000>=0
contributes zero even if P K_A|000> is nonzero. Thus only X1,Y1,X3,Y3
can contribute to this transition; no channel is omitted from B itself.

Here are the literal vectors needed for those four terms, before the
site3 scaling1/2 is applied:

 K_X1|000>=C1|100>+iD1|110>,
 K_Y1|000>=iC1|100>-D1|110>,
 K_X3|000>=C1|001>+iD1|011>,
 K_Y3|000>=iC1|001>-D1|011>.

For example exp(isH_c)|000>=cos(Js)|000>+i sin(Js)|010>,
while H_c vanishes on the first-flipped sector; this gives the first
two FULL integral vectors. Their P overlaps yield a combined
4(rv^2-d1*v)/(1+v^2). The last two give the opposite sign and their
site3 strength alpha=1/2. Hence

 Tr[P B_*(rho_+)]
   =4[(1+alpha)r v^2-(1-alpha)d1*v]/(1+v^2)
   =-a.                                           (A4)

The full Gaussian moments give r<=gamma and

 integral_0^infinity s Re Phi(s)ds
   >=gamma*c*tau(1/4-1/256)
   >=(441/2048)gamma*tau,
 integral_0^infinity s^3|Phi(s)|ds<=gamma*tau^3/8.

The first follows from cos(z/4)>=1-z^2/32 and c>=7/8. The ABSOLUTE
sine remainder bounds the sign-changing tail correctly, giving

 d1>=gamma*y[441/2048-y^2/48]>=gamma*y/24.

Consequently

 a>=gamma*y^2/[3456(1+y^2/20736)]
   >=a0=gamma*y^2/6912>0.                          (A5)

The bath asymmetry is essential: alpha=1 would cancel the linear d1*v
term. All physical channels remain strictly present at alpha=1/2.

## Monotonicity for every required duration

Define the ACTUAL base expectation

    kappa(s)=Tr[rho_+ exp(sB)W].

Unitality and A4 give kappa(0)=1, kappa'(0)=2a>=2a0.
For s>=0 the finite-dimensional exponential and A1 give

 |kappa'(s)-kappa'(0)|<=b(exp(bs)-1).

For0<=s<=t_*=a0/(2b^2), bs<=log2. Therefore
exp(bs)-1<=bs exp(bs)<=2bs and the last bound is at most2b^2s<=a0.
The expectation is real, since B preserves adjoints. Thus throughout
this WHOLE interval

    kappa'(s)>=a0,
    1+a0s<=kappa(s)<=exp(bs).                       (A6)

This supplies monotonicity; a positive derivative only at s=0 would not
have sufficed for the clock argument. Fix ANY t in(0,t_*].

## Physical Pauli covariance and restricted logical representatives

Let pi be the unital *-embedding determined by

    pi(X)=G, pi(Z)=W, pi(Y)=iGW, pi(I)=I.

A2 gives the exact Pauli algebra, with two four-dimensional logical
eigenspaces. Neither pi's existence nor the following calculation
requires B to preserve pi(M_2).

Conjugation by G or S sends each bare physical Pauli A to its sign
epsilon_A times A. Because it commutes with H_c, it sends K_A to the
SAME sign times K_A. The signs cancel in every Redfield channel.
Thus B and exp(sB) commute with those two Pauli conjugations, even with
the unequal site bath strengths. Both rho_+ and rho_- are S-invariant;
pi(X),pi(Y) are S-odd, so their actual expectations vanish for all s.
G maps rho_+ to rho_- and sends W to-W. Their restricted logical
functionals therefore have the exact density representatives

 D_+(s)=diag((1+kappa(s))/2,(1-kappa(s))/2),
 D_-(s)=diag((1-kappa(s))/2,(1+kappa(s))/2).         (A7)

For0<=s<=t these have trace norm kappa(s)<=kappa(t). They need not be
positive, and that failure is precisely the amplifier. The PHYSICAL
INITIAL rho_+,rho_- are positive normalized states.

## Positive clock preimages, with norm one at ALL intermediate times

Set w=(kappa(t)+1)/(2kappa(t)) and prepare the POSITIVE initial mixtures

 rho_clock,0=w rho_+ +(1-w)rho_-,
 rho_clock,1=(1-w)rho_+ +w rho_-.

Since kappa(t)>=1, these are convex normalized mixtures. At EVERY
duration0<=s<=t their logical X,Y expectations are zero and Z is
plus or minus kappa(s)/kappa(t). A6 puts that number in[-1,1]. Thus
each restricted functional is POSITIVE of norm EXACTLY1 at every
duration, and at s=t it is exactly the desired pure logical bit.

The later D5 use takes a partial contraction at a post-probe duration
between0 and t. It uses these EVERY-duration logical norm-one suppliers,
not positivity of the full physical evolved clock or merely its final
pure logical value. The mixtures are fixed from t while the observation
time may vary. They are never redefined inside interpolation.

For N data blocks with one separately treated root and t=N^(-1/2)/gamma,
the non-root product norm is A=kappa(t)^(N-1). For sufficiently large N,
log(1+a0t)>=a0t/2 and N-1>=N/2, so

 y^2 sqrt(N)/27648<=log A<=38sqrt(N).               (A8)

All statements here concern the exact independent BASE functional.
The connected actual dynamics remains subject to D3/D5, physical C4,
the cutoff transfer and the analytic assembly. No coupled propagator has
been tensorized. Separate independent acceptance of this actual C2
supplier and the remaining assembly is still pending.

---

## Source module 4: P5-STATIC-CLOCK-C4-INTERFACE-v1.md

Full-source SHA256: 7198285e1e2c621f66a758a11903a8dfd02be6d8c51d24b20fbaa6d30eb778c2.

Included projection: complete source.

Projection SHA256: 7198285e1e2c621f66a758a11903a8dfd02be6d8c51d24b20fbaa6d30eb778c2.

# C4: the literal same-static-H clock interface

21 October 2026. A bounded HAND proof interface for review. This is not a
compiler result, acceptance of the remaining analytic suppliers or P5
closure. Its source is the COMPLETE STATIC-PARALLEL-CLOCK-FANOUT.md,
SHA256842927d32cbd03eb1bf077e5cfce199d7e20de2ccb1d7428625467e89d59ce25,
together with the embeddings in
SYMMETRIC-AMPLIFIER-AND-CLOCK-PREIMAGES.md,
SHA256ca496356d8fbd7c889976df747c1b78fa49c96a9f9f035f48813a6e623a5490b.
The thermal Gaussian replaces the earlier sech bath in the final candidate;
the static algebra below has no bath premise.

## Exact finite Hamiltonian and target

There are N=2^(q+1)-1 DATA qubits on a binary tree. List CNOT(child->parent)
in bottom-up depth order, with two disjoint rounds at each depth. Set
G_c=N-1 and let D be the number of these nonempty rounds, so
1<=D<=2ceil(log2 N). Each vertex participates in at most three gates.
Number layers l=0,...,D-1; gates in each layer have disjoint data supports.
Within a layer choose any fixed gate order. Write C=U_G...U_1.
Direct Pauli conjugation, depth by depth, gives

    C^dagger Z_root C=product_(all data) Z_i.          (S1)

Every gate involving the root has it as TARGET, so CNOT and the static
Hamiltonian terms below commute with X_root. Fix omega_0>0 and even
d>=16D. Each gate g has a SEPARATE chain of d+1 physical clock qubits,
positions j=0,...,d, initially with its single excitation at j=0.

    Delta=pi d/(4D omega_0),
    omega_l=omega_0 D/(D+l),
    a_(l,j)=(omega_l/d)sqrt((j+1)(d-j)),
    L_0=2D Delta=pi d/(2omega_0).

The FULL-qubit-space static Hermitian Hamiltonian K_0 is the sum, for
each clock bond j,j+1, of

 a_(l,j)[|01><10| tensor V_(g,j)
                         +|10><01| tensor V_(g,j)^dagger],

where V_(g,d/2)=U_g and V_(g,j)=I on every other bond. The forward hop
increases j. The norm of this term is a_(l,j)<=omega_0 and it occupies at
most four qubits. One excitation per chain is invariant under K_0.
This invariant sector is used ONLY to prove the prepared compression.
K_0 itself is defined on the complete clock Hilbert space.

For the product one-excitation clock input |c>, the literal target is

 ||<c|exp(iL_0 K_0)Z_root exp(-iL_0 K_0)|c>
                       -product_(data)Z_i|| <=2E_d,

 E_d=[pi d G_c^2+2sqrt(G_c)]exp[-d/(256D^2)].       (S2)

No approximation on arbitrary clock inputs is asserted. Choosing
d=2ceil(4096D^2 log(e G_c D/epsilon_clock)) gives E_d<=epsilon_clock.
In the candidate epsilon_clock<=1/32 and delta_c=2E_d<=1/16.

## The ordering estimate needed in the proof

Remove V from each chain and call its one-excitation Hamiltonian K_free.
It is a sum of INDEPENDENT spin-d/2 chains (2omega_l/d)J_x. Starting at
position0, the exact squared amplitudes are Binomial(d,p_l(t)), where

    p_l(t)=sin^2(omega_l t/d).

On 0<=t<=L_0 these probabilities are monotone. Their central arrival
times are t_l=(D+l)Delta. In particular the LAST layer arrives at
L_0-Delta; it does not arrive at L_0. At least Delta/2 before or after
its arrival, p is below or above1/2 by at least1/(8D). The minimum angular
margin is pi/(16D), and the elementary sine bound gives that constant.

Fix an earlier-layer gate g and a strictly later-layer gate h. Before
the midpoint of t_g,t_h, h is on the right (j_h>=d/2+1) with probability
at most exp[-d/(32D^2)]. After that midpoint, the probability that g is
at either of its central sites j_g in{d/2,d/2+1} is at most
exp[-d/(128D^2)]. The one-site offset1/d is at most1/(16D), since d>=16D.
The free clocks have independent position distributions. Thus uniformly
in t in[0,L_0],

 Pr[g central AND h right] <=exp[-d/(128D^2)].       (S3)

At L_0, each chain is left (j<=d/2) with probability at most the same
bound. These estimates are uniform in every data input; the data do not
enter K_free.

For a configuration z define x_g=1 if j_g>d/2 and zero otherwise, and

    W(z)=U_G^x_G ... U_1^x_1,
    K_id=W K_free W^dagger

on the invariant one-excitation sector. W is block diagonal and unitary;
W(c)=I. A central forward hop of clock g in K_id applies

    U_later U_g U_later^dagger,

where U_later is the ordered product of already-right gates later than g.
K_0 instead applies U_g. Gates in g's own layer commute with U_g. The
difference therefore vanishes unless at least one strictly later-layer
clock h is already right while g is central. For each pair g,h its
contribution on the ideal evolving state has norm at most

    2omega_0 sqrt(Pr[g central AND h right]).

This follows also for the reverse hop: the two central source/target
subspaces are orthogonal, and each difference of unitary gate factors
has norm at most2. A union bound on the relevant orthogonal clock
projections followed by sqrt(sum p)<=sum sqrt(p) bounds the norm by the
sum over pairs. The data-dependent W(z) preserves each position
probability. There are at most G_c^2 ordered pairs. Unitary Duhamel gives

 ||(exp(-iL_0K_0)-exp(-iL_0K_id))|c,psi>||
        <=2omega_0 L_0 G_c^2 exp[-d/(256D^2)]       (S4)

for EVERY normalized data vector psi. If all clocks are right,
W(z)=C. The union bound on a late left clock shows that the final ideal
state differs from exp(-iL_0K_free)|c> tensor C psi by at most
2sqrt(G_c)exp[-d/(256D^2)]. Combined with S4 this is the isometry error
E_d in S2. For a norm-one observable, two isometries at distance E_d have
compressions differing by at most2E_d. Applied to Z_root and S1 this
proves the literal prepared-clock target.

The deliberately conservative d choice is explicit: if
u=log(e G_c D/epsilon_clock)>=1, then d<=8194D^2u and
the prefactor of E_d is at most32778D^2uG_c^2. Use32778<exp(11),
u<=exp(u), (G_cD)^2<=epsilon_clock^2 exp(2u) and
d/(256D^2)>=32u. The resulting bound is at most
epsilon_clock^2 exp(-18u)<=epsilon_clock.

## Physical embedding, SAME H and uniform geometry

Each data or clock qubit becomes one three-physical-qubit block, with

    H_c=(J/2)(Z1X2+X2Z3), G=X1Y2X3, S=Z1,
    pi(X)=G, pi(Z)=W, pi(Y)=iGW.

The W here is the balanced local reflection from the symmetric amplifier
source, not the clock-configuration gauge W(z). Its exact defining
relations are W^2=G^2=I, GW=-WG, [H_c,W]=[H_c,G]=0. On the ROOT instead
use pi_root(X)=G, pi_root(Z)=S, pi_root(Y)=iGS. There S^2=I,
SG=-GS, and [H_c,S]=0. These are unital isometric *-embeddings of the
two-by-two matrix algebra on the COMPLETE physical block spaces. No
prepared gauge state is needed for these algebra identities.

All encoded clock terms therefore commute with H_0=sum H_c, exactly.
For EVERY real r, use the ONE static physical Hamiltonian

    H_r=H_0-r pi_all(K_0)+h_*Z_isolated.

The isolated qubit is independent. S_root commutes with H_0 and with its
term. Hence for L(r)=L_0/r and r>0 the original source convention gives

 U_(H_r)(L(r))S_root
   =exp(-iL(r)H_r)S_root exp(iL(r)H_r)
   =pi_all(exp(iL_0K_0)Z_root exp(-iL_0K_0)).       (S5)

This is a full-Hilbert-space identity; only its later base clock
functional uses the prepared compression S2. Likewise
[H_r,G_root]=0, since all root gates have the root as target. The same
H_r must be used in EVERY original Redfield filter. No effective logical
noise or deletion of physical clock noise is part of S5.

A data vertex has at most three adjacent data vertices and two central
clock sites for each incident gate: its closed logical neighborhood has
size at most10. A clock vertex has at most two clock neighbors and, only
if central, the gate's two data vertices: size at most5. The interaction
neighborhood relation is symmetric, so its multiplicity has the same
bound. Encoding each logical block in three physical sites gives

    k<=12, m<=30, nu<=30,
    h_active<=J+3|r|omega_0,
    M=N+(N-1)(d+1)=O(N log^3 N).

With 0<r<=1 and the candidate's J,omega_0 this is below h_*. The
unrelated term fixes EXACT h=h_* independently of N and r. Embedding
does not increase term norms. All physical blocks retain their full
on-site baths in the admitted model; C4 is solely a Hamiltonian and
prepared-operator lemma.

## Review boundary and next connection

These arguments have been hand-derived and finite clock/gauge/geometry
identities checked, but this C4 supplier has not received an independent
complete hand audit or formal check. The original static source's final
historical gap paragraph predates the analytic counterexample assembly;
the current open supplier list is in P5-CANDIDATE-REVIEW-LEDGER.md.

The later use is ONLY at the independent base r=0: the positive clock
preimage mixtures make their logical functional exactly |c><c| at t_N;
then S2 is contracted with the product data functional of norm A_N.
Connected actual evolution is handled separately by D3/D5 and the
analytic interpolation chain. C4 does not tensorize coupled evolution,
prove those interpolation steps or establish P5 closure.

---

## Source module 5: P5-C4-PREMISE-AUDIT-v1.md

Full-source SHA256: 0250b69790904486eccb323d6e698f17b87fd4680669203a40310af09ebfefc7.

Included projection: complete source.

Projection SHA256: 0250b69790904486eccb323d6e698f17b87fd4680669203a40310af09ebfefc7.

# Quantitative free-clock and full-space embedding premises

21 October 2026. Self-reviewed HAND completion of the PREMISES left
outside LEAN-P5-C4-GAUGE-ISOMETRY-09's bounded agreement. That return
conditionally agrees with the gauge/isometry/S5 argument; it does not
independently accept the probability constants or all block algebra.
This note is not a new independent review, test run, compiler job or
request for a further P5 proof lane.

The pinned C4 interface is P5-STATIC-CLOCK-C4-INTERFACE-v1.md, SHA256
7198285e1e2c621f66a758a11903a8dfd02be6d8c51d24b20fbaa6d30eb778c2.
Its underlying static source is842927d32cbd03eb1bf077e5cfce199d7e20de2ccb1d7428625467e89d59ce25.

## Exact distribution, derived on a finite representation

The free one-excitation chain has basis|j>, j=0,...,d, and matrix element
(omega_l/d)sqrt((j+1)(d-j)) between j and j+1. On the symmetric subspace
of d mathematical spin halves, the sum of their X operators has exactly
the matrix element sqrt((j+1)(d-j)): count the zero spins that can be
flipped between the normalized weight-j and weight-(j+1) sums.
Thus the two finite matrices are unitarily identical. These mathematical
spins are a representation, not new physical clock sites.

Starting at|0>, its evolution is therefore the symmetric tensor power
of cos(theta)|0>-i sin(theta)|1>, theta=omega_l t/d. The EXACT position
distribution is Binomial(d,p_l(t)), p_l(t)=sin^2(theta). With
omega_l=omega_0 D/(D+l), l=0,...,D-1, and
L_0=pi d/(2omega_0), every angle on[0,L_0] lies in[0,pi/2], so p_l
is monotone. Its central arrival is t_l=(D+l)Delta,
Delta=pi d/(4D omega_0). The last arrival is L_0-Delta.

## Tail constants with both central endpoints

For a Bernoulli variable X with parameter p, the centered log moment
generating function f(lambda)=log(1-p+p exp(lambda))-p lambda has
f(0)=f'(0)=0 and f''(lambda)=q(1-q)<=1/4, where
q=p exp(lambda)/(1-p+p exp(lambda)). Integrating this bound in either
direction gives f(lambda)<=lambda^2/8. Independence of d such variables
and exponential Markov, optimized at lambda=4a or-4a, give

 Pr[J/d-p>=a], Pr[J/d-p<=-a] <=exp(-2d a^2).        (P1)

The deterministic cases p=0,1 satisfy the same inequalities directly.

At distance at least Delta/2 from arrival, the angular distance a_theta
from pi/4 is at least pi/(16D), since omega_l>=omega_0/2. It lies in
[0,pi/4]. Concavity of sine gives sin(2a_theta)>=4a_theta/pi, hence

 |p_l(t)-1/2| >=1/(8D),                            (P2)

with the sign determined by before/after arrival. For strictly ordered
layers g before h, their arrival separation is at least Delta. Split
time at their arrival midpoint. Before it, h's right event J_h>=d/2+1
requires an upper fluctuation of at least1/(8D), so its probability is
at most exp[-d/(32D^2)]. After it, g's TWO central sites are contained
in J_g<=d/2+1. Because d>=16D,

 p_g-(1/2+1/d)>=1/(8D)-1/d>=1/(16D),

so the probability of that event is at most exp[-d/(128D^2)]. Free
clock positions are independent, and in each half of the interval the
other event has probability at most1. Thus at EVERY time

 Pr[g in{d/2,d/2+1} AND h right]
                             <=exp[-d/(128D^2)].   (P3)

At time L_0 every arrival is at least Delta earlier. Apply P2 and P1 to
the event J_l<=d/2; its probability is at most exp[-d/(32D^2)], also
bounded by the weaker P3 constant. These are precisely the two estimates
used by the audited gauge/isometry proof. No coupled noisy-clock
probability law is being substituted for these FREE-clock identities.

The stated epsilon_clock choice follows from the elementary E_d bound
already displayed in C4. With u=log(e G_c D/epsilon_clock)>=1,
8192D^2u<=d<=8194D^2u and the prefactor is at most32778D^2uG_c^2.
Then E_d<=epsilon_clock^2 exp(-18u)<=epsilon_clock, as in the interface.

## Exact physical embedding, including its norm

The Gaussian C2 source gives the physical balanced W, G and S with
W^2=G^2=S^2=I, GW=-WG, SG=-GS, and each of W,G,S commuting with H_c.
On a non-root block choose an orthonormal basis e_1,...,e_4 of W=+1;
the vectors G e_1,...,G e_4 are an orthonormal basis of W=-1. The
identification|0,j>->e_j, |1,j>->G e_j makes W=Z tensor I_4 and
G=X tensor I_4. Thus pi(Q) is EXACTLY a unitary copy of Q tensor I_4,
not a restriction to a code subspace. It is a unital *-embedding and
||pi(Q)||=||Q||. At the root the SAME construction uses S instead of W.
All statements hold on the COMPLETE eight-dimensional physical blocks.

The algebra premises themselves are explicitly derived in
P5-GAUSSIAN-AMPLIFIER-C2-v1.md, SHA256
10b7507cf809a22348b9b5ac82eabd1c868b9de76ec7b25074366339a0ff3f54.
In particular G maps phi_A to a vector orthogonal to phi_B, and phi_B
to a vector orthogonal to phi_A, exchanging the full negative and
positive W eigenspaces. No assertion G phi_A proportional phi_B is used.

Tensoring these exact block identifications makes the entire pi_all
isometric. Since H_c commutes with the logical X and Z, every encoded
logical operator commutes with H_0's block term. Finite matrix power
series give pi_all(exp K)=exp(pi_all K). Each static clock term therefore
keeps its norm, support on at most four blocks, and exact H_0 commutation.
No assumption of base Redfield code invariance follows or is needed.

## One isolated term, one common Hamiltonian

To remove a notation ambiguity across the sources, define ONCE

 H_blocks=sum_b H_(c,b), H_iso=h_*Z_isolated,
 H_total,0=H_blocks+H_iso,
 H_r=H_total,0-r pi_all(K_0).                       (P4)

C4 writes H_0=H_blocks and lists H_iso separately. T1 and W2 include
H_iso in their H_0. In the I13 premise, "H_0 plus the independent
incidence-fixing qubit" means H_blocks plus ONE H_iso. These are aliases
for P4, never a second copy of H_iso. D6's reference U_(H_0) is U_(H_total,0).
The isolated channels retain their full filters; their increments are
identically zero. Their observable factor is I and their generator is
unital, so they contribute exactly1 to the root expectation. Their real
onsite Pauli term fixes the exact original h=h_*, once.

With P4, [H_total,0,pi_all(K_0)]=0 and [H_total,0,S_root]=0 give S5
with its PLUS iL_0 pi_all(K_0) sign, exactly as the peer audited.
Every physical filter and every physical evolution uses this SAME H_r.
The prepared-clock sector enters only the independent-base compression.

The neighborhood/incidence counts in C4 are unchanged: at most10 logical
blocks in a data closed neighborhood and5 at a clock, hence k<=12,
m<=30,nu<=30 after the three-site encoding. Active h<=J+3r omega_0<h_*.
An unrelated single-qubit neighborhood adds no larger bound. The
logical-clock error and the physical-generator error remain distinct.

This supplies a complete self-reviewed proof of these C4 premises.
Independent acceptance still has exactly the conditional scope of the
peer's actual return; writing this note is not an additional peer audit
or full P5 closure. The analytic and original-prediction assembly is a
separate source obligation, not implied by prepared clock reachability.

---

## Source module 6: CODE-FUNCTIONAL-DYSON-BOUND-v1.md

Full-source SHA256: 8497d6896e820e5538c7d966349e51122eb3182d68894693201896b4fdb8b023.

Included projection: source prefix before ## Uniform weak-link interaction estimate.

Projection SHA256: a418eb8bc69f680d3ac0bb26bf07bb36550be346fc84fda274e2999c00d72849.

# A code-functional Dyson bound for weak local interactions

21 October 2026. Authored mathematical proof candidate, self-reviewed.
This is not an actual online Lean check or an independent acceptance.
Its intended application and remaining audit are in
P5-STATIC-CLOCK-ANALYTIC-COUNTEREXAMPLE-v1.md.

## Finite tensor-product setting

Physical block i has a finite matrix algebra B_i, a unital *-embedding
pi_i of a logical matrix algebra C_i, and a positive normalized initial
functional rho_i. Let B=sum_i B_i^0 be a sum of block generators, each
annihilating I. On all ordinary blocks assume

    ||B_i^0||_cb <= b.

At the selected real time t, suppose the actual base functionals restricted
to their logical algebras obey, for EVERY 0<=s<=t,

    ||rho_i exp(s B_i^0) pi_i|| <= a_i,    a_i>=1.       (D1)

These functionals need not be positive. A distinguished finite set of
root blocks can instead be included in the touched set throughout and
bounded by exp(b_root t). Write A=product_(ordinary i) a_i. All norms of
functionals here are matrix functional norms, equivalently trace norms of
their density representatives. A scalar-valued matrix functional has
completely bounded norm equal to its norm. Tensor products of those
functionals have the product norm.

Let V=sum_Z V_Z, where V_Z acts only on physical blocks Z. The decomposition
can be finite or absolutely summable in the following weighted cb norm:

    W_t(V)=sum_Z exp(b t |Z outside root|) ||V_Z||_cb.   (D2)

Let rho be the product initial functional. For any logical Q,

    |rho exp(t(B+V)) pi_all(Q)|
       <= A exp(b_root t) ||Q|| exp[t W_t(V)].         (D3)

It is enough for (D3) alone to assume (D1) only at s=t. The intermediate
times in (D1) are needed for the one-insertion variant below.

## Proof of (D3): retain exactly which blocks were touched

Expand exp(t(B+V)) in its time-ordered Dyson series around B. Fix a term
with n specified insertions V_(Z_1),...,V_(Z_n), and let S contain the
root and the union of their supports. No insertion touches any block
outside S. Its full base evolution there can therefore be moved past all
insertions and contracted against rho_i. Applied to the logical input Q,
these untouched contractions have cb norm at most
product_(i outside S) a_i. Their partial contraction leaves a logical
operator on S of norm at most that product times ||Q||.

On S use the PHYSICAL cb norm of every base segment and every insertion.
The durations of the base segments sum to t, giving the bound

    A ||Q|| exp(b_root t) exp(b t |S outside root|)
          product_j ||V_(Z_j)||_cb.

The replacement of the untouched product by A is valid because a_i>=1.
Since |S outside root|<=sum_j |Z_j outside root|, this is bounded by
A||Q||exp(b_root t) times the product of the weighted terms in (D2).
Sum the supports and integrate the n-simplex, of volume t^n/n!.
Summing n proves (D3). The same absolute estimate justifies an absolutely
summable interaction decomposition and limits of its partial sums.

No actual propagator contraction, positivity, invariant logical algebra
under B, or tensorization after adding V was used. Only the untouched
BASE blocks were contracted using their actual restricted functionals.
The touched blocks were estimated in their full physical algebras.

## A single global logical probe applied to a local observable

Let O be supported on the designated root. Consider a probe superoperator
P consisting of a fixed finite sum of elementary left/right products
whose non-root factors are GLOBAL logical operators. More explicitly the
Redfield probe used here is

    P(F)=[A_root,F] Q - Q_sharp [A_root,F],            (D4)

with A_root local, ||A_root||<=1, and Q,Q_sharp in pi_all(C_all).
For real physical parameters Q_sharp=Q^dagger; their complex analytic
continuations are kept separately. Put

    p=2(||Q||+||Q_sharp||).

Define the single-probe response

    F(t)=d/dv rho exp(t(B+V+v P)) O |_(v=0).

Under (D1),

    |F(t)| <= p ||O|| t A exp(b_root t+t W_t(V)).     (D5)

To prove this, expand in V and retain exactly ONE P. Fix the V supports
and include the root in their union S. Before P, the observable outside S
is I: O is local, B annihilates I, and no V insertion touches those blocks.
The four terms in (D4) insert one global logical Q or Q_sharp, multiplied
on either side by operators on S. On each untouched block, its base
duration AFTER P lies between 0 and t. Thus its contraction has norm at
most a_i by (D1). Partially contract that ONE global logical factor first;
its norm is at most its original norm times the product of the untouched
a_i. Everything remaining is a physical map on S and is bounded just as
in (D3). There are n+1 positions for P among n V insertions. Their ordered
time integrals total (n+1)t^(n+1)/(n+1)!=t^(n+1)/n!.
Summing gives (D5).

This argument permits base dynamics to leave the logical algebra and
permits arbitrary entanglement of the logical input. It would NOT apply
unchanged to several global probes: then an untouched block could carry
a genuine multi-time logical correlation rather than the ONE restricted
functional in (D1). The application below needs only the first derivative.


---

## Source module 7: P5-WEAK-LINK-ANALYTIC-SUPPLIER-v1.md

Full-source SHA256: 0ae3388cff05ec2ba9cfd7328a70c8b47e9a5496f2376f67212ba0abf98fd3ec.

Included projection: complete source.

Projection SHA256: 0ae3388cff05ec2ba9cfd7328a70c8b47e9a5496f2376f67212ba0abf98fd3ec.

# Explicit weak-link and analytic-probe bounds

21 October 2026. Self-reviewed numerical-constant refinement of D7/D8 in
CODE-FUNCTIONAL-DYSON-BOUND-v1.md. The frozen source is unchanged. This is
not independent review, a compiler result or full counterexample acceptance.

## Same physical blocks and one root parameter

H_0 is a sum of independent three-qubit H_c blocks (and the unrelated
incidence-fixing qubit), K_0=sum_Z K_Z is the encoded static clock, and
H_r=H_0-rK_0. Every K_Z commutes with H_0, occupies at most four blocks,
and the block incidence of K_0 is eta_0=3omega_0. The number of blocks is M.
The norm of an encoded K_Z is its original logical operator norm: pi_all
is an injective unital *-homomorphism and hence isometric.

The root's nine Gaussian base channels are scaled by the SAME u; on
non-root blocks their scalar strengths c_p are at most one. The root
strength magnitudes are at most |u|. Complex u and r below are analytic
parameters; adjoint filters are analytically extended with conjugate
scalar covariance and the SAME r,u, not conjugated r,u. On the real axis
this is precisely the physical affine Redfield family.
In all norm formulas c_p denotes the NONNEGATIVE magnitude of that
channel's scalar rate.

For fixed cutoff S, keep the full base filter and integrate only its
increment up to S, exactly as in D6. Write

    R_tilde(r,u)=B(u)+V(r,u).

For ordinary blocks ||B_i||cb<=38gamma=:b. Keep the root in the touched
set when u is complex, with root base norm at most2J+36gamma|u|.
Use the weighted interaction mass

    W_t(V)=sum_Z exp(bt|Z outside root|)||V_Z||cb.

Assume

    bt<=log(2)/4,   gamma*tau<=1,
    6eta_0 |r| S exp(3bt)<=1/2.                     (W1)

Then an explicit bound is

    W_t(V(r,u))
      <=eta_0 |r|[4M+864gamma*tau(M-1+|u|)]
      <=1000eta_0 |r|(M+|u|).                      (W2)

The root factor |u| is not multiplied by M.

## Rooted commutators with their support weights

For a bare channel A_p at one block, H_0 conjugation keeps it on that
block and preserves its norm. Since [H_0,K_0]=0, the remaining increment
is the analytic series of exp(irsK_0) conjugation of that block operator.
For each fixed n the nested commutator sum only has nonzero terms when
each new interaction overlaps the union of the preceding supports.

After j steps that union has size at most1+3j. At the next step, the sum
of norms of overlapping K_Z is at most(1+3j)eta_0. The summed product of
interaction norms through n steps is therefore at most

    eta_0^n product_(j=0)^(n-1)(1+3j)<=(3eta_0)^n n!.

The commutator contributes2^n and the exponential coefficient1/n!.
Thus the summed norm of order n is bounded by(6eta_0|r|s)^n, with
support at most1+3n. Including the support weight gives

    exp(bt)[6eta_0|r|s exp(3bt)]^n.

Each individual term is supported on that union of blocks; the outer
bare A_p in its Redfield map belongs to the same union. Base conjugation
by H_0 is a tensor product of local unitary conjugations, so it changes
neither this support nor these norms. No extensive ||H_0|| appears.

Under (W1), summing n>=1, then integrating its absolute covariance,
gives the weighted sum of increment-filter norms at most

    12 c_p eta_0 |r| exp(4bt)
                      integral_0^S s|Phi_G(s)|ds
       <=24 c_p eta_0 |r| gamma*tau.               (W3)

The analytic sharp increment has the same bound: replacing Phi_G by its
complex conjugate and a scalar rate by its absolute magnitude changes
none of these estimates. The corresponding Redfield map
[A_p,F]Q-Q_sharp[A_p,F] has cb norm at most2(||Q||+||Q_sharp||), so its
weighted contribution is at most96 c_p eta_0|r|gamma*tau.
Summing nine channels per non-root block and nine root channels proves
the864 term in (W2). The unrelated qubit has identically zero increment.

For the Hamiltonian part, sum_Z||K_Z||<=M eta_0, and each support has at
most four blocks. Its weighted cb mass is at most

    2|r| exp(4bt)sum_Z||K_Z||<=4M eta_0|r|.

This proves (W2). All series are absolutely summable in the displayed
weighted mass; they do not assert unsigned summability of an infinite
uncut bath expansion. The actual full-filter tail is handled separately
by P5-FULL-PROBE-TRANSFER-v1.md.

## Analytic global source without a global Hamiltonian norm

Let A=S_root be the bare root Z1 and Y_0=exp(iL_0K_0)Aexp(-iL_0K_0).
Then A belongs to the DIFFERENT root code pi_root(Z)=S, and Y_0 is a
global logical operator. Define

    Q_r=(1/2)integral_(-S)^S Phi_G(v)
                         exp(irvK_0)Y_0exp(-irvK_0)dv.

Conjugation by exp(iL_0K_0) commutes with conjugation by exp(irvK_0), so
apply the short-time series to the LOCAL A FIRST. The same rooted estimate
without support weights bounds its norm by

    sum_(n>=0)(6eta_0 |r| |v|)^n<=2

when 6eta_0|r|S<=1/2. The remaining long REAL conjugation exp(iL_0K_0)
is unitary and preserves operator norm. Since
(1/2)integral_R |Phi_G(v)|dv<=gamma,

    ||Q_r||,||Q_r_sharp||<=2gamma                   (W4)

uniformly on that complex r disk, independently of M and L_0.
All operators lie in the same global code algebra, including the sharp
extension. Thus the source [S_root,O]Q_r-Q_r_sharp[S_root,O] for ||O||<=1
has norm at most8gamma, and is itself logical when O is.

At r=0,

    Q_0=b_S gamma Y_0,
    b_S gamma=Re integral_0^S Phi_G(v)dv.

The actual Gaussian tail gives |b_S-b_G|<=exp[-(S/tau)^2]. Therefore
b_S>=b_G/2 whenever exp[-(S/tau)^2]<=b_G/2. The sharp version at zero
is exactly the same Q_0.

For the candidate's R_N=32N^(-1/3), S_N=1/(1000eta_0 R_N),
6eta_0 R_N S_N=6/1000. Hence (W1) holds for all sufficiently large N,
with t_N=N^(-1/2)/gamma, on the ENTIRE complex disk |r|<=R_N.
The precise bounds (W2)/(W4) prove the D7/D8 suppliers under their stated
finite-dimensional operator assumptions. Their use does not independently
validate the static-clock C4, physical amplifier C2 or final assembly.

---

## Source module 8: P5-FULL-PROBE-TRANSFER-v1.md

Full-source SHA256: 5f43d1e1da2ba34a155fc6de26b72411ebf13879fb0a2013754e7bf333094ccd.

Included projection: complete source.

Projection SHA256: 5f43d1e1da2ba34a155fc6de26b72411ebf13879fb0a2013754e7bf333094ccd.

# Literal actual-to-auxiliary single-probe transfer

21 October 2026. Self-reviewed hand proof of the C7 supplier in
P5-STATIC-CLOCK-ANALYTIC-COUNTEREXAMPLE-v1.md. This is not a compiler result,
independent acceptance of this supplier or acceptance of the whole candidate.
The D3/D5 supplier has separately received a bounded independent assistant
hand audit; that audit did not cover the present calculation.

## Fixed operators, parameters and definitions

Fix N, a REAL r in [r_N/2,r_N], r_N=N^(-1/3), and a REAL u in [0,2].
The final physical family only uses u in [1,2]. All operators below live
in the SAME finite physical Hilbert space. Let

    H_0=sum_b H_(c,b)+h_*Z_isolated,
    H_r=H_0-r pi_all(K_0),
    U_r(s)F=exp(-isH_r)F exp(isH_r).

K_0 has four-block terms, block incidence eta_0=3omega_0 and commutes
with H_0. Let M=N+(N-1)(d+1) be its number of three-qubit blocks; the
one unrelated noisy qubit is additional. The fixed candidate parameters
J=b_G gamma/32, omega_0=b_G gamma/96, h_*=b_G gamma/4 obey b_G<1.
All unshifted covariances have form c_p Phi_G with 0<=c_p<=2 for this
u interval; only the root's nine channels depend on u. There are 9M
active block channels and three unrelated-qubit channels.

Put R_N=32r_N and

    S=1/(1000eta_0 R_N)=1/(32000eta_0 r_N),
    L=L_0/r,       L_0=pi*d/(2omega_0),
    theta=(1/4)/cosh(L/tau).

For ALL r in this interval,

    L/S >=48000*pi*d>1.                              (T1)

Let A=S_root=Z1 be the bare modulated root channel. It commutes with H_0.
All sharp filters in this real calculation are literal matrix adjoints.
The complex analytic sharp in the other source restricts to these same
adjoints because U_r(s)A is Hermitian for real r,s.

## A Gaussian tail bound used only where its variable is correct

For every a>=0,

    integral_a^infinity |Phi_G(s)|ds
       <=gamma exp[-(a/tau)^2]=:gamma delta_a.         (T2)

Indeed, for z>=a/tau, 2z^2>=z^2+(a/tau)^2 and
c integral_0^infinity exp(-z^2)dz<=sqrt(pi)/2<1.
Also |Phi_G(-s)|=|Phi_G(s)|, so (T2) bounds the negative tail in its
ACTUAL shifted integration variable. It does not put a Gaussian tail
bound on the delayed covariance as a function of the original s near L.

For an unshifted channel B_p define

    K_p(r,u)=integral_0^infinity c_p Phi_G(s)U_r(s)B_p ds,
    K_tilde,p(r,u)=K_p(0,u)
       +integral_0^S c_p Phi_G(s)[U_r(s)B_p-U_0(s)B_p]ds.

The full and auxiliary Redfield generators, denoted D and E respectively,
both include the SAME i[H_r,.]. Their exact filter difference is

    K_p-K_tilde,p
       =integral_S^infinity c_p Phi_G(s)[U_r(s)B_p-U_0(s)B_p]ds.

Since B_p is a Pauli and both real-H conjugations are unitary,

    ||K_p-K_tilde,p||,||K_p^dagger-K_tilde,p^dagger||
       <=2c_p gamma delta_S<=4gamma delta_S.

The unrelated-qubit increment is exactly zero, as it is disjoint from K_0.
Each Redfield channel difference has cb norm at most four times its filter
difference. Therefore

    ||D-E||_cb <=144M gamma delta_S.                 (T3)

## Match the FULL delayed probe to D8 before bounding its tails

The exact covariance coefficient of v is
theta[Phi_G(s-L)+Phi_G(s+L)]/2. Its filter is theta Q_full, with

    Q_full=(1/2)integral_0^infinity
                  [Phi_G(s-L)+Phi_G(s+L)]U_r(s)A ds.

Let Y_0=pi_all[exp(iL_0K_0)Z_root exp(-iL_0K_0)]. Because A commutes
with H_0, K_0 commutes with H_0, and rL=L_0, the exact identity is

    U_r(L+z)A=exp(irz pi_all(K_0))Y_0 exp(-irz pi_all(K_0)).

Thus shifting s=L+z in the FIRST term gives

    Q_full=(1/2)integral_(-L)^infinity Phi_G(z)U_r(L+z)A dz
          +(1/2)integral_0^infinity Phi_G(s+L)U_r(s)A ds.

The central interval [-S,S] in the first term is EXACTLY the D8 operator

    Q_S=(1/2)integral_(-S)^S Phi_G(z)
          exp(irz pi_all(K_0))Y_0 exp(-irz pi_all(K_0))dz.

In particular the finite pulse width and both operator orders are retained.
Using (T1)-(T2), the two outside pieces and the second shifted integral
give

    ||Q_full-Q_S|| <=gamma delta_S+(gamma/2)delta_L
                   <=(3/2)gamma delta_S<=2gamma delta_S. (T4)

The same bound holds for the literal adjoints. Also ||Q_full||<=2gamma
and ||Q_S||<=gamma for these REAL parameters. Define the EXACT and
auxiliary coefficient superoperators

    V(F)=theta([A,F]Q_full-Q_full^dagger[A,F]),
    W(F)=theta([A,F]Q_S-Q_S^dagger[A,F]).

Consequently

    ||V||_cb,||W||_cb <=8theta gamma,
    ||V-W||_cb <=8theta gamma delta_S.                (T5)

No covariance pulse near s=L has been assigned delta_L as a whole:
its central part is Q_S and is kept. Only its genuine z tails and the
separate Phi_G(s+L) term were estimated.

## Keep every finite-volume propagation factor

For this real r,u range both baseline generators satisfy

    ||D||_cb,||E||_cb <=300M gamma=:d_M.              (T6)

One direct conservative verification is enough. The Hamiltonian norm is
at most M(J+eta_0)+h_*<=M gamma. Exact filters have norm at most 2gamma
on blocks. Auxiliary filters have norm at most 2gamma+4gamma=6gamma.
Each channel has cb norm at most four times its filter norm. Thus 9M
channels contribute at most216M gamma, the unrelated three contribute
12gamma, and the Hamiltonian contributes at most2M gamma. Their sum is
at most230M gamma, below (T6). This estimate needs no actual positivity.

Fix ANY normalized positive initial density rho and ANY O with ||O||<=1.
They are the SAME in the two responses. For s>=0 define

    F_D(s)=d/dv Tr[rho exp(s(D+vV))O]|_(v=0)
          =integral_0^s Tr[rho exp((s-q)D)V exp(qD)O]dq,

    F_E(s)=integral_0^s Tr[rho exp((s-q)E)W exp(qE)O]dq.

These are Heisenberg generators; the star is suppressed in D,E,V,W.
All expressions are finite-dimensional and the Duhamel differentiation
is justified by their absolutely convergent matrix exponential series.
Put e_M=144M gamma delta_S. Equation(T3) gives

    ||exp(aD)-exp(aE)||_cb<=e_M a exp(d_M a),  a>=0.

Subtract the two integrands by changing the left exponential, then the
probe, then the right exponential. Using (T5)-(T6), their total norm is
at most

    8theta gamma exp(d_M s)[delta_S+e_M(s-q)+e_M q].

Integration proves the explicit C7 bound

    |F_D(s)-F_E(s)|
       <=8theta gamma s(1+144M gamma s)
             exp(300M gamma s) exp[-(S/tau)^2].       (T7)

This is uniform in the SAME real r in I_N, real u in[0,2], and the
fixed rho_N used by the candidate. The actual physical use requires only
u in[1,2]. No positive output state, contraction, tensorized coupled
propagator, changing rho with s or switching physical generators was used.

Finally, at t_N=N^(-1/2)/gamma,

    M gamma t_N=O(sqrt(N)log^3 N),
    (S/tau)^2=N^(2/3)/(32000eta_0 tau)^2.

The latter dominates the former and every polynomial prefactor, so the
right side of (T7) tends to ZERO uniformly for 0<=s<=t_N. This proves
the stated actual-to-auxiliary first-probe comparison, conditional only
on the explicit finite operators and Gaussian covariance above. It does
not by itself prove the static-clock compression, D3/D5, C2, or the full
counterexample conclusion.

---

## Source module 9: P5-INTERPOLATION-AND-ADMISSION-v1.md

Full-source SHA256: 963c61d9c337cd8dc099a19cd2aec5c57b22f7bd30e78f31b88fd562aa9bb753.

Included projection: complete source.

Projection SHA256: 963c61d9c337cd8dc099a19cd2aec5c57b22f7bd30e78f31b88fd562aa9bb753.

# A finite lower-bound interface for the P5 analytic assembly

21 October 2026. Self-reviewed HAND refinement of sections5-8 of
P5-STATIC-CLOCK-ANALYTIC-COUNTEREXAMPLE-v1.md, SHA256
204f368e17b6b544eda5b471237d505f997f26d50e3161a5c3a6f0a6a1de9540.
It makes all four analytic variables and remainder terms explicit.
This is conditional on the physical and operator suppliers below,
not independent acceptance, a computation of a large-system response,
a compiler result or P5 closure.

## Fixed finite system, density and supplier premises

Use the candidate's positive constants gamma,tau,J,omega_0, eta_0=3omega_0,
b_G, delta_b=1/4 and its balanced-tree sizes N. Let t=N^(-1/2)/gamma,
r_N=N^(-1/3), R=32r_N, S=1/(1000eta_0 R), and M=N+(N-1)(d+1).
The static clock's L_0,d are exactly those of C4. Put

    b=38gamma, a0=gamma*y^2/6912, y=Jtau,
    A=kappa(t)^(N-1), delta_c<=1/16.

Assume N is large enough that t<=a0/(2b^2), bt<=log(2)/4,
U=N^(1/4)>2, and exp[-(S/tau)^2]<=b_G/2. The further elementary W1
condition holds on the whole r disk because6eta_0 R S=6/1000.

The POSITIVE INITIAL density rho_N is fixed ONCE for this N. All data
blocks except the root have rho_+=|000><000|. Every clock block has
the prescribed bit's positive mixture with weight
(kappa(t)+1)/(2kappa(t)). The root has its G+ pure state. The unrelated
incidence-fixing qubit can have any fixed positive normalized density.
In every variable and time variation below these same exact densities
remain fixed. In particular the clock weights are NEVER retuned to the
varied observation time s<=t.

The conditional suppliers are:

1. C2 and the exact base Pauli symmetries: data restricted-functional
   norm kappa(s)<=kappa(t), clock norm1 for EVERY duration0<=s<=t,
   and the pure prepared-clock functional at exactly t. They give
   log A>=y^2 sqrt(N)/27648 and log A<=38sqrt(N).
2. C4: prepared parity compression error delta_c, the distinct root
   code pi_root(Z)=S_root, pi_root(X)=O=G, exact H_0/K_0 commutation
   and [H_r,O]=0. The physical Hamiltonian is H_r=H_0-rK_0, plus the
   independent incidence-fixing qubit.
3. D3/D5: the touched-block code-functional bound and its ONE-probe
   version, with full physical touched-block maps. They do not assume
   code invariance of those maps or positivity after evolution.
4. W2/W4 in P5-WEAK-LINK-ANALYTIC-SUPPLIER-v1.md: on the stated domains,
   W_t(V(r,u))<=1000eta_0|r|(M+|u|) and
   ||Q_r||,||Q_r_sharp||<=2gamma. All sharp extensions use the SAME
   analytic r,u; they agree with actual adjoints on the real parameters.
5. T3/T5/T6/T7 in P5-FULL-PROBE-TRANSFER-v1.md: real baseline/auxiliary
   cb norms<=d_M=300M gamma, probe norms<=8theta gamma, and actual
   first-probe transfer error at real r,u,s bounded by T7.

No member of the final physical family has u=0 or complex parameters.
Those are finite-dimensional analytic proof tools only.

## One elementary extrapolation and one derivative inequality

For a complex polynomial p of degree at most m>=1, interpolation at
x_j=a/2+j a/(2m), j=0,...,m, gives

    |p(0)|<=12^m max_j|p(x_j)|.                     (I1)

Indeed the denominator of the j-th Lagrange coefficient is
(a/(2m))^m j!(m-j)!, while its numerator is at most a^m. Summing the
absolute coefficients gives (4m)^m/m!<=(4e)^m<12^m. The same proof
with nodes1+j/m gives I1 on[1,2]. Complex coefficients cause no change.

For a complex polynomial p of degree at most n>=1 on[-1,1],

    ||p'|| <=2n^3 ||p||.                            (I2)

Expand p(cos x) in cos(kx). Orthogonality gives each nonconstant
coefficient modulus<=2||p||. The identity
T_k'(cos x)=k sin(kx)/sin x and |sin(kx)|<=k|sin x| give
||T_k'||<=k^2, with endpoint limits. Since sum_(k=1)^n k^2<=n^3,
I2 follows. On[0,t] the factor is4n^3/t. This proof applies to
polynomials with complex coefficients as well as real ones.

If an analytic function is bounded by H on a complex disk of radius R_0,
the Taylor remainder at |z|<=a<R_0 is at most

    H (a/R_0)^(m+1)/(1-a/R_0).                     (I3)

This follows by summing the Cauchy coefficient estimates. All functions
used here are entire at each FIXED finite N; every specified circle lies
inside their domain. The cutoff S is fixed as r varies.

## 1. A nonzero REAL weak-link grid point

Let E(r,u) be the full-base plus cut-increment auxiliary generator and
P_r(F)=[S_root,F]Q_r-Q_r_sharp[S_root,F]. Define

    g(r)=rho_N exp(t E(r,0))P_r(O).

The source excludes theta, which depends on the subsequently chosen
real r. It is entire in r, including at r=0. D3 and W2/W4 give on|r|<=R

    |g(r)|<=H_r,
    H_r=8gamma A exp(E_r),
    E_r=2Jt+1000eta_0 R M t.                        (I4)

At r=0 the root base has only its unitary H_c evolution, fixing the root
code. Q_0=b_S gamma Y_0 with b_S>=b_G/2. Pure clock compression and the
root G+ state give

    -g(0)>=4b_S gamma(1-delta_c)A
           >=G_0=(15/8)b_G gamma A.                (I5)

Here [S,O](S product W)-(S product W)[S,O]=-4O product W.
The compression error is bounded in the product BASE functional of norm
A, not in a postulated positive evolved state. The root uses pi_root,
and the non-root data use pi(Z)=W.

Set m_r=ceil(N^(1/4)) and

    eps_r=H_r (1/32)^(m_r+1)/(1-1/32),
    G_N=12^(-m_r)G_0-eps_r.

Apply I1/I3 to g's Taylor polynomial, whose value at0 is EXACT g(0).
Some finite REAL grid point

    r_*=r_N/2+j r_N/(2m_r), j in{0,...,m_r},

satisfies |g(r_*)|>=G_N. For large N, G_N>0. There is no assertion
that every real r retains the sign or magnitude of g(0).

## 2. A time derivative yields a large finite-time first probe

Fix this r_* ONCE. Let L=L_0/r_*, theta=delta_b/cosh(L/tau),
and let F(u,s) be the derivative at v=0 of

    rho_N exp[s(E(r_*,u)+v theta P_(r_*))]O.

At the auxiliary value u=0, E(r_*,0)O=0 EXACTLY. All non-root bare
channels have commutator[A_p,O]=0, and the Hamiltonian commutes with O.
Thus

    partial_s F(0,t)=theta g(r_*).                  (I6)

The Duhamel integral at complex s has bound
|F(0,s)|<=8theta gamma|s|exp(d_M|s|). On the circle|s|=2t use the
uniform, r-independent bound

    H_t=16delta_b gamma t exp(2d_M t).

Set n=N^2 and

    eps_t=H_t 2^(-n),
    eps'_t=(H_t/t)(n+2)2^(-n),
    theta_min=delta_b/cosh(2L_0/(tau r_N)),
    B_N=[t/(4n^3)](theta_min G_N-eps'_t)-eps_t.      (I7)

The first two quantities bound the degree-n time Taylor polynomial's
value and derivative errors uniformly on[0,t]. In fact
sum_(k=n+1)^infinity k 2^(-k)=(n+2)2^(-n). Since theta>=theta_min,
I2 and I6 prove

    max_(0<=s<=t)|F(0,s)|>=B_N.                     (I8)

This uses a polynomial derivative bound instead of any sign assumption
on the response integral. Choose a maximizing time s_* in[0,t]; the
initial density is still rho_N fixed from t, not a new density based on s_*.

## 3. Return to admitted positive ROOT noise

For complex|u|<=U=N^(1/4), D5 applies to the ONE global code probe.
Every untouched clock's actual restricted functional has norm1 for the
needed post-probe duration. Touched physical factors need not be code
operators; the physical bimodule contraction in D5 handles them.
The root base norm is at most2J+36gamma|u|. W2 therefore gives uniformly
for real0<=s<=t

    |F(u,s)|<=H_u,
    H_u=8delta_b gamma t A
       exp[(2J+36gamma U)t+1000eta_0 r_N t(M+U)].    (I9)

Only the root channel count carries |u|; the non-root physical base has
already been contracted with its actual code functional. No factor
exp(CM gamma t) is inserted for the untouched BASE clocks.

Put

    m_u=ceil(sqrt(N)/sqrt(log N)),
    eps_u=H_u (2/U)^(m_u+1)/(1-2/U).

The degree-m_u Taylor polynomial of F(u,s_*) has EXACT value F(0,s_*)
at zero and error<=eps_u on[1,2]. I1 at nodes1+j/m_u proves that SOME
REAL u_* on that admitted grid satisfies

    |F(u_*,s_*)|>=12^(-m_u)B_N-eps_u.              (I10)

This is an analytic extrapolation implication, not an inverse-positive
map and not physical admission of the auxiliary u=0 system.

## 4. Transfer to the FULL physical generator, then physical v

At the SAME real r_*,u_*,s_* and the SAME positive initial rho_N, the
full-filter first derivative F_full differs from F by at most

 D_N=8delta_b gamma t(1+144M gamma t)
                  exp[300M gamma t-(S/tau)^2].     (I11)

This is T7 with theta<=delta_b and s<=t. It keeps the delayed pulse,
its sharp, and the full baseline. It is not a cutoff physical bath.

Let f(v)=rho_N exp[s_*R(r_*,u_*,v)]O for the ORIGINAL full Redfield
generator and the original covariance family C5. This is entire in v,
with |f(v)|<=H_v=exp[t(d_M+16delta_b gamma)] on|v|<=2: the baseline
norm is at most d_M and the physical probe coefficient at most8theta gamma.
The degree-n v Taylor polynomial has EXACT derivative F_full at0 and
value error at most

    eps_v=H_v 2^(-n)

on[-1,1]. Applying I2 to it gives

 |F_full|<=2n^3[max_(v in[-1,1])|f(v)|+eps_v].       (I12)

Every value on that real interval is a FULLY ADMITTED physical model:
u_* in[1,2], all bare Pauli channels positive with the same beta, the
fixed Gamma,b0,j,x,k,m,nu, and the exact SAME static H_(r_*). Complex
v was only an analytic norm bound. Higher v Taylor coefficients are
bounded by this coarse GLOBAL norm, never by the one-probe D5 lemma.

Combining I7-I12 gives the following SINGLE FINITE lower bound for the
candidate's admitted maximum P_N:

 P_N >= L_N
     :=[12^(-m_u)B_N-eps_u-D_N]/(2n^3)-eps_v.       (I13)

All quantities on the right are explicitly defined above. This is a
conditional operator theorem at each sufficiently large finite N, not a
reported numerical evaluation. It selects r on a finite real grid and
u on a finite physical grid, then a real time and physical v in compact
intervals, always with the one predeclared positive density.

## The asymptotic lower bound, with each loss separated

M=O(N log^3 N), d=O(log^3 N), L_0=O(log^3 N) at fixed parameters.
Hence E_r=O(N^(1/6)log^3 N)=o(m_r). Relative to G_0*12^(-m_r),
eps_r tends to zero because exp(E_r)(12/32)^m_r tends to zero.
Eventually G_N>=G_0*12^(-m_r)/2.

Also

 log(1/theta_min)<=log(1/delta_b)+2L_0/(tau r_N)
                      =O(N^(1/3)log^3 N)=o(sqrt(N)).

The time errors eps_t,eps'_t vanish absolutely: their negative n log2
beats log H_t=O(sqrt(N)log^3 N), even with the derivative's polynomial
and1/t factors. Thus I7 gives

    B_N>=exp[log A-o(sqrt(N))].                     (I14)

The logarithm of H_u is at most38sqrt(N)+o(sqrt(N)); the extra terms
36gamma U t and eta_0 r_N U t even tend to zero. The logarithm of
(2/U)^m_u is

    -(1/4)sqrt(N)sqrt(log N)+O(sqrt(N)/sqrt(log N)),

so eps_u tends to zero absolutely, also after multiplication by12^m_u.
Meanwhile12^m_u=exp[o(sqrt(N))]. The transfer error D_N vanishes
absolutely because the NEGATIVE fixed multiple of N^(2/3) beats
O(sqrt(N)log^3 N). Finally eps_v vanishes because n=N^2 beats that same
coarse global exponent. The polynomial factors n^3 and1/t cost O(log N).

It follows from I13-I14 and log A>=y^2 sqrt(N)/27648 that, eventually,

    P_N>=exp[y^2 sqrt(N)/55296].                    (I15)

The coefficient y is fixed and may be extremely small; every threshold
is asymptotic at those fixed constants. No computationally tractable
threshold is claimed. The finite-witness search specification retains
this dependence rather than claiming a small experimental counterexample.

## Final original-comparator implication and exact remaining gaps

For a selected physical model, the original square-window generator,
INCLUDING its ordered Lamb shift, is a unital GKSL Heisenberg generator.
It uses the SAME H_(r_*), the SAME physical covariances and the original
window T=sqrt(tau/Gamma), with Gamma=9gamma/4; no alternate CP reference
is inserted.
Its Hermitian norm-one prediction in the same positive rho_N has modulus
at most1. Therefore its prediction difference from the original Redfield
prediction is at least P_N-1 in the supremum. Complete positivity is used
only here for the actual comparator, never for the Redfield dynamics or
the analytic auxiliaries.

If the suppliers above and this assembly are accepted, I15 rules out a
finite volume/time-uniform P5 bound at these fixed original parameters,
including arbitrarily small fixed x. It does not merely refute a CP
reference estimate or a practical cutoff solver. No assumption about
translation invariance or polynomial ball growth has been introduced;
the authoritative P5 scope allows the bounded-neighborhood binary tree.

The ledger still lists independent C2/C4, W2/W4 and full assembly audits
as open. Bounded peer agreement on D3/D5 and conditional T4/T7 is not
acceptance of all those premises. This note does not change the goal
status or create independent verification by restating the derivation.

---

## Source module 10: P5-FINITE-GRID-COROLLARY-v1.md

Full-source SHA256: 1f4389f3877c8d085320a8a81c265bda9f679a3e0209244f065a8defe9cec07d.

Included projection: complete source.

Projection SHA256: 1f4389f3877c8d085320a8a81c265bda9f679a3e0209244f065a8defe9cec07d.

# A completely finite real-parameter witness grid

21 October 2026. Conditional HAND corollary of the explicit I13 assembly
in P5-INTERPOLATION-AND-ADMISSION-v1.md, SHA256
963c61d9c337cd8dc099a19cd2aec5c57b22f7bd30e78f31b88fd562aa9bb753.
It adds finite grids for observation time and physical bath modulation
to the already finite r/u grids. It is not an executed witness search,
independent proof acceptance or a new model/compiler job.

## The elementary grid lemma

Let p have degree at most n>=1 on a real interval[a,b] and let
J_g=8n^3. At the grid x_j=a+(b-a)j/J_g, j=0,...,J_g,

    max_j|p(x_j)| >=(3/4)max_(x in[a,b])|p(x)|.     (G1)

Indeed I2 after interval rescaling gives
||p'||<=(4n^3/(b-a))||p||. A maximizing point has a grid point within
(b-a)/(2J_g). Integrating p' along that real segment changes its value
by at most(2n^3/J_g)||p||=||p||/4. This also holds for complex p.
Endpoint maxima cause no issue because the endpoints belong to the grid.

## The actual physical grid and lower bound

Retain ALL notation and conditional supplier premises of I1-I15. In
particular rho_N is the one predeclared POSITIVE initial density based
on t_N, and n=N^2. Use the finite sets

 R_N_grid={r_N/2+j r_N/(2m_r): j=0,...,m_r},
 U_N_grid={1+j/m_u: j=0,...,m_u},
 T_N_grid={t_N j/J_g: j=0,...,J_g},
 V_N_grid={-1+2j/J_g: j=0,...,J_g}.

Here m_r=ceil(N^(1/4)), m_u=ceil(sqrt(N)/sqrt(log N)) and J_g=8N^6.
Every tuple is REAL and fully admitted: r>0, u in[1,2], v in[-1,1],
s in[0,t_N], the SAME original static H_r and all physical bath channels.
Neither u=0 nor a complex parameter is a grid member.

Let G_N,theta_min,eps_t,eps'_t,eps_u,D_N,eps_v be exactly those in
the I13 source. Define

 B_N_grid=[3t_N/(16n^3)](theta_min G_N-eps'_t)-eps_t,

 L_N_grid=[3/(8n^3)]
            [12^(-m_u)B_N_grid-eps_u-D_N]-eps_v.     (G2)

Then the finite maximum of ORIGINAL full-filter predictions obeys

 max_(r,u,s,v in the displayed grids)
       |Tr[rho_N exp(s R(r,u,v)*)O]| >= L_N_grid.   (G3)

To prove this, choose r_* from the already finite I4-I5 interpolation
grid. Its degree-n TIME Taylor polynomial p_t has derivative at t_N
of modulus at least theta_min G_N-eps'_t. I2 and G1 give

 max_(time grid)|p_t|
    >=[3t_N/(16n^3)](theta_min G_N-eps'_t).

Subtract eps_t. Thus some displayed time s_* has
|F(0,s_*)|>=B_N_grid. The finite u interpolation of I9-I10 then
selects u_* with

 |F(u_*,s_*)|>=12^(-m_u)B_N_grid-eps_u.

I11 transfers this to the SAME full physical first derivative with loss
D_N. Its degree-n v Taylor polynomial p_v has EXACT derivative F_full
at zero, so I2 gives ||p_v||>=|F_full|/(2n^3). Apply G1 on[-1,1] and
subtract eps_v to obtain G2-G3. The only extra losses are two fixed
factors3/4. All analytic remainders and initial states are unchanged.
If a displayed lower expression is negative the inequality is vacuous;
the asymptotic claim is for the sufficiently large N where it is positive.

Consequently the I14-I15 asymptotic remains valid:

    max_(finite physical grid)|prediction|
                 >=exp[y^2 sqrt(N)/55296]          (G4)

eventually. In particular the parameter existence does not rely on
choosing an unspecified continuous maximizer. The size of this grid is
finite and polynomial in N; evaluating its matrices remains enormously
more expensive because physical Hilbert-space dimension is exponential
in M=O(N log^3 N). No efficient algorithm is claimed.

## An exact sequence without deciding ties

For a computable witness specification fix gamma=1, a positive rational
tau in the original box and epsilon_clock=1/32. One can avoid any exact
real-ceiling decision by the following equivalent certified roundings.
For x=4096D^2[1+log(32G_cD)], compute a rational upper bound q_x with
x<=q_x<=x+1, then take d=2ceil(q_x). If d_*=2ceil(x) is the candidate's
original length, d_*<=d<=d_*+2. The C4 error E_d is decreasing for
d>=256D^2: differentiating its displayed linear prefactor times the
exponential proves this directly. Since d_*>=8192D^2, the larger length
still gives E_d<=epsilon_clock and the same hardware/runtime orders.

Similarly, a rational upper bound q_u in
[sqrt(N)/sqrt(log N),sqrt(N)/sqrt(log N)+1] gives m_u=ceil(q_u), at most
one above the original m_u. Use these chosen integers consistently in
the clock construction, I7-I13 and G2. Their proofs are unchanged: Cauchy
and interpolation apply to ANY chosen integer degree, and all asymptotic
orders and strict exponent separations stay the same. Such rational
enclosures of elementary positive functions are computable by convergent
series and bisection. For example log z=2sum_(k>=0)w^(2k+1)/(2k+1),
w=(z-1)/(z+1), after dyadic range reduction has an explicit geometric
remainder with |w|<=1/3. Thus this variant needs neither transcendence
claims nor comparisons of an unknown exact real with an integer.

For each integer B>=2 enumerate balanced-tree sizes and the finite
physical grids, dovetailing certified interval precision. Stop at the
first tuple whose ORIGINAL prediction is certified in modulus>B.
G4 guarantees a strict successful tuple at all sufficiently large sizes,
so this procedure terminates conditional on the candidate proof.
Restrict each next search to a larger tree depth to obtain an increasing
sequence of volumes for B=2,3,... . No comparison of equal maxima or
uncertified rounded density is required.

Full filters are computable by finite integration with their common
exponential envelope tail; the delayed pulse is retained until that tail
bound applies. The finite-block kappa(t_N) and positive mixture weights
are computable exact real expressions. This is the finite-grid version
of P5-FINITE-WITNESS-SELECTION-v1.md's rational-dovetail specification.
Neither version has been executed. Their termination remains conditional
on the complete mathematical suppliers and admission audit, as recorded
in P5-CANDIDATE-REVIEW-LEDGER.md.

---

## Source module 11: P5-FINITE-WITNESS-ADMISSION-CORRECTION-v1.md

Full-source SHA256: 7ee9f3b094b943c4a9b564be91f8149cf2f73bb007f869c04ac2f3d43715251b.

Included projection: complete source.

Projection SHA256: 7ee9f3b094b943c4a9b564be91f8149cf2f73bb007f869c04ac2f3d43715251b.

# Mandatory admission threshold for the finite witness search

21 October 2026. A substantive source-specification correction, not a
new execution or independent acceptance. The main counterexample and
I13/G4 proofs already assume N sufficiently large. Their mathematical
bounds are unchanged. The search wording must also enforce that
condition BEFORE interpreting a returned value as an admitted witness.

This corrects the unrestricted q enumeration wording in
P5-FINITE-WITNESS-SELECTION-v1.md, SHA256
01f23003ae3292ce0a7f41328c0e6b52b688a7adef29f2f212459512f72fbc06,
and supplies the starting condition for the search paragraph of
P5-FINITE-GRID-COROLLARY-v1.md, SHA256
1f4389f3877c8d085320a8a81c265bda9f679a3e0209244f065a8defe9cec07d.
Those frozen sources retain their bytes and history. No search has run.

## Why this condition is necessary

The clock mixture weight is w=(kappa(t_N)+1)/(2kappa(t_N)). Its
positivity is proved by C2 only when t_N<=a0/(2b^2), b=38gamma and
a0=gamma*y^2/6912. Merely enumerating q>=1 without this restriction
would not prove each input mixture positive. A large output at an
unqualified early q could therefore not be accepted as a P5 witness.
The corrected procedure below enumerates ONLY qualified volumes.

For arbitrary computable fixed parameters one may dovetail strict
eligibility certificates with the prediction evaluation, retaining only
sizes with certified t_N<a0/(2b^2), bt_N<log(2)/4, U_N>2 and
exp[-(S_N/tau)^2]<b_G/2. All sufficiently large sizes qualify.
The following explicit dyadic family avoids those certification decisions.

## An entirely explicit starting depth

Fix ANY integer ell>=40 and use

 gamma=1, tau=2^(-ell), Gamma=9/4,
 J=eta_0=b_G/32, omega_0=b_G/96,
 N=2^(q+1)-1 with q>=q_min=4ell+80.                 (A0)

The other constants, all baths and physical terms are exactly those of
the candidate, with epsilon_clock=1/32. For a computable clock length
use the certified integer rounding variant already proved in G's search
paragraph, consistently throughout the construction and finite bound.

First,1/2<b_G<1. The upper bound follows from its formula. For the lower,
exp(-1/8)>=7/8, exp(-1/128)>=127/128 and
sqrt(pi/8)>3/5 because pi>3. Thus

 b_G>(7/8)(3/5)(127/128)=2667/5120>1/2.

It follows that y=Jtau>tau/64 and

 a0>tau^2/(4096*6912),
 t_*=a0/(2*38^2)>tau^2/10^11.                     (A1)

Indeed2*38^2*4096*6912<10^11. From N>=2^q and A0,

 t_N=N^(-1/2)<=2^(-q/2)<=tau^2*2^(-40)<t_*.

Therefore kappa(t_N)>=1, every clock mixture is a positive normalized
physical density, and its logical functional is positive of norm1 at
every duration in[0,t_N]. All interpolation keeps that same fixed density.

Moreover bt_N<=38*2^(-40)<1/8<log(2)/4, where log(2)>1/2 follows by
integrating1/x on[1,2]. Also U_N=N^(1/4)>2. Since

 S_N/tau=N^(1/3)/(1000 b_G tau)>2^ell/1000>2,

its Gaussian tail is less than exp(-4)<1/16<b_G/2. The W1 condition
then follows from6eta_0 R_N S_N=6/1000 and bt_N<log(2)/4.
Finally y<tau/32<1/288 and

 Gamma*tau=(9/4)2^(-ell)<=1/(360*2^30)

because2^10>810. Thus the original fixed parameter box, the positive
initial density and every elementary domain condition used in I13/G4
hold at EVERY enumerated q, not just at the eventual successful q.

## Corrected selection rule and its precise scope

For integer target B>=2 start the finite-grid dovetail search at
q>=4ell+80, and on subsequent searches also require q greater than the
last returned depth. Use only the stated real r/u/time/v grids and the
original full filters. Stop only when a certified interval for the
actual prediction has modulus strictly greater than B. The candidate's
eventual G4 bound guarantees termination CONDITIONAL on the full proof;
every tested input is already admitted by A0-A1 and the physical bath/
geometry suppliers, independently of whether it produces a large value.

This restriction changes neither the asymptotic result nor its fixed
local observable. It prevents an uncertified small-volume initial state
from being mistaken for a counterexample. All arbitrarily small dyadic
x=(9/4)2^(-ell), ell>=40, keep the same b0,j,k,m,nu across their volume
families. The same beta=tau/8 is fixed across every family. No practical
runtime, computed witness or formal verification is claimed.

---

## Source module 12: P5-PHYSICAL-BATH-AND-COMPARATOR-ADMISSION-v1.md

Full-source SHA256: 7a74683e27dfbb66e08ca2b935aaee39c0b2a9323803168244e3448ab4593aaf.

Included projection: complete source.

Projection SHA256: 7a74683e27dfbb66e08ca2b935aaee39c0b2a9323803168244e3448ab4593aaf.

# Physical bath admission and the original comparator's bounded prediction

21 October 2026. Complete self-reviewed HAND supplier for the exact
finite model used in the counterexample packet. This is not independent
acceptance or a new execution. The norm of the original CP comparator is
used only for the final discrepancy; actual Redfield is never assigned
positivity or contraction.

## The baseline is a genuine thermal positive-type covariance

Let c=exp(-1/8) and

 Phi(t)=(gamma*c/tau)exp[-2(t/tau)^2]exp[-it/(4tau)],
 J_G(omega)=gamma*c*sqrt(pi/2)
                        exp[-(omega*tau-1/4)^2/8].

The Gaussian Fourier integral gives this pair in the convention
J_G(omega)=integral_R Phi(t)exp(iomega t)dt. In particular J_G>0,
J_G(-omega)=exp(-beta omega)J_G(omega), beta=tau/8, and
Phi(-t)=conjugate(Phi(t)). Positive type follows by Fourier inversion:
every finite covariance quadratic form is the integral of J_G times a
modulus squared. For omega>0 the bosonic coupling density
J_G(omega)(1-exp(-beta omega))/(2pi) is nonnegative and realizes exactly
the positive/negative frequency KMS pair. Its thermal covariance is
finite, including near zero frequency and at infinity. Independent
copies give the required independent on-site bath channels.

Completing the square gives-2z^2+|z|<=1/8, hence
|Phi(t)|<=(gamma/tau)exp(-|t|/tau). Also

 Re integral_0^infinity Phi(t)dt=b_G gamma,
 b_G=exp(-1/8)sqrt(pi/8)exp(-1/128)>0.              (B1)

The Gaussian source in this packet derives its transition moments with
the absolute sine remainder; no everywhere-positive Re Phi is assumed.

## Root modulation, signs, common envelope and floor

Fix real r in[r_N/2,r_N], u in[1,2], v in[-1,1], L=L_0/r,
delta_b=1/4 and theta=delta_b/cosh(L/tau). All root base channels are
scaled by u. Modify ONLY the bare root Z1 spectrum to

    J_root(omega)=J_G(omega)[u+v theta cos(omega L)].

The bracket is at least u-|v|theta>=3/4>0 and is even. Thus this
channel stays strictly positive type, with the SAME beta and positive
bosonic coupling density. Its covariance is exactly

 Phi_root(t)=u Phi(t)+(v theta/2)[Phi(t-L)+Phi(t+L)].

For all real t,L>=0,

 e^(-|t-L|/tau)+e^(-|t+L|/tau)
                         <=2cosh(L/tau)e^(-|t|/tau).

For t>=L there is equality; for0<=t<=L multiply by exp(t/tau) and
reduce to exp(2t/tau)<=exp(2L/tau); symmetry handles negative t.
Consequently

 |Phi_root(t)|<=(u+|v|delta_b)(gamma/tau)e^(-|t|/tau)
              <=(Gamma/tau)e^(-|t|/tau),
 Gamma=9gamma/4.                                  (B2)

This includes NEGATIVE physical v and keeps the full delayed pulse.
Every other channel has a positive scaling in{1,1/2,u,u/2}, with the
unrelated site's three channels using Phi. Those factors are at most2,
so B2 is the common envelope for all channels. The same symmetry gives
Re half-integral=J(0)/2. The modulated root's value is
(u+v theta)b_G gamma>=3b_G gamma/4. The smallest channel floor in the
whole system is b_G gamma/2, attained by ordinary site3 copies. Therefore

    b0=2b_G/9, b0 Gamma=b_G gamma/2                 (B3)

are common volume-independent physical constants. Every one of the
three bare Pauli channels at EVERY physical site remains present.

## Original strength and geometry, without a different norm

The encoded static-clock source proves operator-norm preservation of
each logical term on the FULL physical blocks, at most four logical
blocks per term, three physical sites per block, and incidence eta_0.
Closed logical neighborhoods have at most10 blocks and their symmetric
incidence multiplicity the same bound. Thus k<=12,m<=30,nu<=30.

Choose J=b_G gamma/32, omega_0=b_G gamma/96, eta_0=3omega_0=J.
For0<r<=1 the active ORIGINAL operator incidence is at most
J+3r omega_0<=b_G gamma/16. The independent onsite Pauli term has
strength h_*=b_G gamma/4 and occurs once. Thus

 h=h_*, j=h/Gamma=b_G/9=b0/2,
 h<b0 Gamma,
 x=Gamma tau<=1/(360*2^30)=1/(12nu_max 2^m_max).    (B4)

No Pauli coefficient incidence or Frobenius norm has replaced h.
The actual source uses H_r=H_blocks+H_iso-r*pi_all(K_0) in EVERY
full filter and physical propagator. The independent site is unital
on its observable factor I and changes no root prediction. The
admission-threshold correction proves positivity of EVERY initial
density in the computationally specified family.

## The original square-window comparator itself

Use the literal D_T,H_T formulas in the packet, with T=sqrt(tau/Gamma),
the SAME H_r and the SAME modulated physical covariances. For any
channel define V_(p,omega)=integral_0^T exp(-iomega s)A_p(s)ds. Fourier
inversion writes its dissipator as

 (1/(2pi T))integral_R J_p(omega)
   [V_(p,omega)rho V_(p,omega)^dagger
          -{V_(p,omega)^dagger V_(p,omega),rho}/2]domega.

This is EXACTLY its square kernel with the original operator order.
All these integrals are absolutely convergent at finite T. J_p>=0
makes its finite-dimensional Kossakowski form positive, hence gives a
GKSL dissipator. The ordered H_T is Hermitian: its integrand before
multiplication by i is anti-Hermitian, by Phi(-s)=conjugate(Phi(s)).
Thus the original Heisenberg semigroup is unital and completely positive.
For Hermitian norm-one O, positivity and unitality preserve-I<=O<=I,
so every positive normalized INITIAL rho satisfies

    |Tr[rho exp(s L_T*)O]|<=1, s>=0.               (B5)

For a grid tuple with actual Redfield prediction modulus P, the SAME
rho and O therefore have original-comparator discrepancy at least P-1
by the scalar triangle inequality. Taking operator norm can only
increase this lower bound. Combined with G4 this defeats any finite
volume/time-uniform original P5 bound at the fixed admitted parameters.
Neither an auxiliary CP reference nor positivity of a Redfield output
is used. Separate independent acceptance of the full assembled claim
remains at the packet's stated evidence boundary.

---

## Frozen source projection index

```json
[
  {
    "included_sha256": "3246b9c859fe8341071232a9aa689debd35e7e77640fedda0f3583ac7c3ba71b",
    "projection": "source prefix before ## 5. A large coupled auxiliary response",
    "source": "P5-STATIC-CLOCK-ANALYTIC-COUNTEREXAMPLE-v1.md",
    "source_sha256": "204f368e17b6b544eda5b471237d505f997f26d50e3161a5c3a6f0a6a1de9540"
  },
  {
    "included_sha256": "841bc18ca75055b1ab7f520e067298a19f866591b355a88d6893a84f18a7c32b",
    "projection": "source prefix before ## A rigorous error bound",
    "source": "GAUSSIAN-THERMAL-RESPONSE-REDUCTION.md",
    "source_sha256": "d0f48bc9ef7ae94786f6fb4de60c5c5057b01002df03db94474dee392b6f996e"
  },
  {
    "included_sha256": "10b7507cf809a22348b9b5ac82eabd1c868b9de76ec7b25074366339a0ff3f54",
    "projection": "complete source",
    "source": "P5-GAUSSIAN-AMPLIFIER-C2-v1.md",
    "source_sha256": "10b7507cf809a22348b9b5ac82eabd1c868b9de76ec7b25074366339a0ff3f54"
  },
  {
    "included_sha256": "7198285e1e2c621f66a758a11903a8dfd02be6d8c51d24b20fbaa6d30eb778c2",
    "projection": "complete source",
    "source": "P5-STATIC-CLOCK-C4-INTERFACE-v1.md",
    "source_sha256": "7198285e1e2c621f66a758a11903a8dfd02be6d8c51d24b20fbaa6d30eb778c2"
  },
  {
    "included_sha256": "0250b69790904486eccb323d6e698f17b87fd4680669203a40310af09ebfefc7",
    "projection": "complete source",
    "source": "P5-C4-PREMISE-AUDIT-v1.md",
    "source_sha256": "0250b69790904486eccb323d6e698f17b87fd4680669203a40310af09ebfefc7"
  },
  {
    "included_sha256": "a418eb8bc69f680d3ac0bb26bf07bb36550be346fc84fda274e2999c00d72849",
    "projection": "source prefix before ## Uniform weak-link interaction estimate",
    "source": "CODE-FUNCTIONAL-DYSON-BOUND-v1.md",
    "source_sha256": "8497d6896e820e5538c7d966349e51122eb3182d68894693201896b4fdb8b023"
  },
  {
    "included_sha256": "0ae3388cff05ec2ba9cfd7328a70c8b47e9a5496f2376f67212ba0abf98fd3ec",
    "projection": "complete source",
    "source": "P5-WEAK-LINK-ANALYTIC-SUPPLIER-v1.md",
    "source_sha256": "0ae3388cff05ec2ba9cfd7328a70c8b47e9a5496f2376f67212ba0abf98fd3ec"
  },
  {
    "included_sha256": "5f43d1e1da2ba34a155fc6de26b72411ebf13879fb0a2013754e7bf333094ccd",
    "projection": "complete source",
    "source": "P5-FULL-PROBE-TRANSFER-v1.md",
    "source_sha256": "5f43d1e1da2ba34a155fc6de26b72411ebf13879fb0a2013754e7bf333094ccd"
  },
  {
    "included_sha256": "963c61d9c337cd8dc099a19cd2aec5c57b22f7bd30e78f31b88fd562aa9bb753",
    "projection": "complete source",
    "source": "P5-INTERPOLATION-AND-ADMISSION-v1.md",
    "source_sha256": "963c61d9c337cd8dc099a19cd2aec5c57b22f7bd30e78f31b88fd562aa9bb753"
  },
  {
    "included_sha256": "1f4389f3877c8d085320a8a81c265bda9f679a3e0209244f065a8defe9cec07d",
    "projection": "complete source",
    "source": "P5-FINITE-GRID-COROLLARY-v1.md",
    "source_sha256": "1f4389f3877c8d085320a8a81c265bda9f679a3e0209244f065a8defe9cec07d"
  },
  {
    "included_sha256": "7ee9f3b094b943c4a9b564be91f8149cf2f73bb007f869c04ac2f3d43715251b",
    "projection": "complete source",
    "source": "P5-FINITE-WITNESS-ADMISSION-CORRECTION-v1.md",
    "source_sha256": "7ee9f3b094b943c4a9b564be91f8149cf2f73bb007f869c04ac2f3d43715251b"
  },
  {
    "included_sha256": "7a74683e27dfbb66e08ca2b935aaee39c0b2a9323803168244e3448ab4593aaf",
    "projection": "complete source",
    "source": "P5-PHYSICAL-BATH-AND-COMPARATOR-ADMISSION-v1.md",
    "source_sha256": "7a74683e27dfbb66e08ca2b935aaee39c0b2a9323803168244e3448ab4593aaf"
  }
]
```

The complete assembly remains at its explicitly stated hand-proof review boundary. No source projection is relabelled as a new test, independent acceptance or formal theorem.
