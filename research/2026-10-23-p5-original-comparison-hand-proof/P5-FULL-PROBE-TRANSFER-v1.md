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
