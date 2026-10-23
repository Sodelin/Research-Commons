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
