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
