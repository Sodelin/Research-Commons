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

## 5. A large coupled auxiliary response at an admitted link strength

Set u=0 and define the analytic function on |r|<=R_N

    g_N(r)=Tr[rho_N exp(t_N R_tilde(r,0)*) P_r(O)].   (C8)

The code-functional Dyson bound (D3), the weak-link bound (D7) and the
probe norm (D8) give

    |g_N(r)| <= C gamma A_N exp[B_N],
    B_N=O(M_N eta_0 R_N t_N)
       =O(N^(1/6)log^3 N)=o(N^(1/4)).                (C9)

At r=0, Q_0=b_(S_N)gamma Y_0, with b_(S_N)>=b_G/2 eventually.
All clock functionals at t_N are exactly |c><c|. The compression (C4),
root expectation of O equal to one, and

    [S,O](S product W)-(S product W)[S,O]
       =-4 O product W

therefore give

    -g_N(0)>=4 b_(S_N)gamma(1-delta_c) A_N.          (C10)

This is a statement at the base expansion point, not the conclusion.
To reach a nonzero physical r use the following explicit interpolation.

For a polynomial p of degree m, Lagrange interpolation at m+1 equally
spaced nodes of [a/2,a] proves

    |p(0)|<=12^m max_nodes |p|.                     (C11)

In fact the sum of absolute extrapolation coefficients is at most
(4m)^m/m! <=(4e)^m<12^m. Take the degree-m Taylor polynomial of g_N at
zero, with m=ceil(N^(1/4)). Cauchy's estimate on radius 32r_N bounds its
error on I_N by C gamma A_N exp(B_N)32^(-m-1)/(1-1/32).
After multiplication by 12^m this is o(gamma A_N), by (C9).
Equations(C10)-(C11) thus select one REAL grid point r_*=r_*(N) in I_N
with

    |g_N(r_*)| >=c gamma A_N 12^(-m).               (C12)

Here c>0 is fixed. This proves a large response of the ACTUAL CONNECTED
auxiliary at some weak-link value. It does not assert the response equals
the independent tensor response at every r. All coupling insertions in
(C9) were bounded in their full physical algebras.

## 6. From this response to a finite-time probe derivative

Fix that r_* and its physical theta. Root O=G commutes with H_r, and every
channel outside the root has [A_p,O]=0. Thus at the AUXILIARY root strength
u=0,

    R_tilde(r_*,0)* O=0                             (C13)

EXACTLY, including its full base filters and truncated increments.
Consequently its single-probe derivative obeys

    d/ds F_tilde(0,s)
       =theta Tr[rho_N exp(s R_tilde(r_*,0)*) P_(r_*)(O)].

At s=t_N, its absolute value is at least theta times (C12).
The physical delayed amplitude has

    log(1/theta)=O(N^(1/3)log^3 N)=o(sqrt(N)).        (C14)

No sign-preservation of the time integral is needed. Here is an elementary
polynomial derivative bound: for a polynomial p of degree n on [-1,1],

    sup|p'|<=2n^3 sup|p|.                           (C15)

Expand p(cos x) in cos(kx). Orthogonality bounds each nonconstant
Chebyshev coefficient by 2sup|p|. The identity
T_k'(cos x)=k sin(kx)/sin x and |sin(kx)|<=k|sin x| give
sup|T_k'|<=k^2, including the endpoints by continuity. Summing proves
(C15), also for complex coefficients. On [0,t_N] the factor is 4n^3/t_N.

The entire finite-dimensional response F_tilde(0,s) is bounded on
|s|<=2t_N by C theta gamma t_N exp(C M_N gamma t_N).
Its degree-n Taylor polynomial at s=0, n=ceil(N^2), has value and
derivative errors o(1) throughout [0,t_N] (the Cauchy geometric tail
beats exp[O(sqrt(N)log^3 N)]). Apply (C15) to that polynomial. Equations
(C12)-(C14) imply

    sup_(0<=s<=t_N)|F_tilde(0,s)|
       >=exp[log A_N-o(sqrt(N))].                  (C16)

Only polynomial factors n^3/t_N were lost. The root-noise-free value in
(C16) is not an admitted physical model; the next step removes it.

## 7. Extrapolate the root bath strength from the admitted interval

For fixed r_* the function F_tilde(u,s) is analytic in u. Apply the
ONE-probe Dyson bound (D5). Non-root DATA base functionals have norm at
most kappa(t_N), and CLOCK base functionals have norm one at EVERY
intermediate duration, by section1. The root is kept in the touched set.
Together with (D7), for |u|<=U_N=N^(1/4) and 0<=s<=t_N this gives

    |F_tilde(u,s)| <=C theta gamma t_N A_N
       exp[C(1+|u|)gamma t_N
                    +C eta_0 r_* t_N(M_N+1+|u|)].   (C17)

Its logarithm is at most C_1 sqrt(N) uniformly; C_1 is fixed. In
particular no extensive M_N gamma t_N root-independent BASE factor
appears. Untouched clock blocks were contracted using their actual
restricted functionals. Only the root channel count carries |u|.

Take the degree

    m_u=ceil(sqrt(N)/sqrt(log N))

Taylor polynomial in u at zero. Its error for real u in [1,2] is o(1):
the Cauchy bound is exp(C_1 sqrt(N))(2/U_N)^(m_u+1)/(1-2/U_N).
Interpolation from [1,2] to zero has the same 12^(m_u) coefficient bound
as (C11). The polynomial has the EXACT value F_tilde(0,s) at zero.
Therefore

    |F_tilde(0,s)|
       <=12^(m_u) [sup_(1<=u<=2)|F_tilde(u,s)|+o(1)]. (C18)

Its cost exp[O(m_u)] is exp[o(sqrt(N))]. This passes from the unphysical
auxiliary root value to derivatives at admitted positive root strengths,
without treating u=0 as a physical system or assuming inverse positivity.

## 8. A large derivative forces a large ORIGINAL prediction

For real u in [1,2], let

    f(u,v,s)=Tr[rho_N exp(s R(r_*,u,v)*) O]

be the ACTUAL full-filter prediction. Its degree-n Taylor polynomial in
v at zero, n=ceil(N^2), has value error o(1) for |v|<=1, uniformly in
u,s. Indeed on the complex disk |v|<=2 its finite-volume exponential norm
is at most exp(C M_N gamma t_N+C theta gamma t_N), again dominated by
2^n. Its first derivative at v=0 is EXACTLY the first derivative of the
polynomial. Thus (C15) gives

    |F_actual(u,s)| <=2n^3[P_N+o(1)].                (C19)

All values defining P_N are admitted systems with all channels present.
Use the ACTUAL-to-auxiliary estimate (C7), then (C18), then take the time
supremum in (C16). This yields

    exp[log A_N-o(sqrt(N))]
       <=12^(m_u) [2n^3(P_N+o(1))+o(1)].           (C20)

Both the interpolation exponent m_u and log(n) are o(sqrt(N)). Equation
(C3) now proves (C1), for example with c_y=y^2/55296 for sufficiently
large N. This also proves unbounded predictions at some times <=t_N->0.
The argument locates parameters through finite interpolation maxima; it
does not identify a numerically tractable threshold volume.

## 9. Original comparison, exact scope and review boundary

Every REAL model used by P_N has positive-type thermal covariances with
the SAME beta, all three on-site Pauli channels, fixed original h,b0,j,x
and bounded fixed geometry. The original square-window generator with
its ordered Lamb shift is GKSL and unital in the Heisenberg picture.
Its Hermitian norm-one prediction is bounded by one for every positive
initial density, including rho_N. Therefore (C1), if accepted, contradicts
ANY finite E_X for these fixed parameters, and hence the unrestricted P5
target. No time-dependent Hamiltonian, missing physical clock noise,
global initial observable, unphysical member of P_N, independent response
after coupling, or alternate comparator has been substituted.

This is a candidate proof, not yet an independently accepted resolution.
The three priority audits are:

1. The touched-block cb-norm contraction and the ONE-global-probe variant
   (D3)/(D5), particularly when the base evolution leaves the code algebra.
2. The static parallel-clock noncommuting-gate isometry (C4) with its
   fixed incidence and operator-norm compression, already a hand candidate.
3. The analytic r/u extensions, exact root conservation (C13), and the
   full shifted-pulse-to-(D8) comparison (C7), with every volume factor.

The Gaussian amplifier transition/moment calculation and its intermediate
clock-functional monotonicity must also remain in the review chain.
If a priority supplier fails, the candidate conclusion is withdrawn at
that precise gap; earlier algebraic/formal components retain their scope.
No assertion of P5 completion, independent review or historical novelty
follows from authoring this file. Continue auditing the proof.
