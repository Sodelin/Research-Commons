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
