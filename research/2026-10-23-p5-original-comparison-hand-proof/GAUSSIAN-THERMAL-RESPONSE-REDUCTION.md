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

## A rigorous error bound for the actual connected full generator

For EVERY original static finite-volume H, define its actual full filters
K_A and the explicit analytical auxiliaries
K_A^S=integral_0^S Phi_p(s)U_H(s)A ds, S>=0, with the SAME H.
The physical filters are K_A, never K_A^S. Since
2z^2>=z^2+(S/tau)^2 for z>=S/tau and sqrt(pi)/2<1,

    ||K_A-K_A^S||<=gamma exp[-(S/tau)^2].            (4)

This also bounds the half-strength channels. Let R and R_S be their
Redfield generators including the SAME i[H,.], and n_phys the number of
physical qubits. Every filter has norm <=gamma, h<=b0 gamma<=gamma and
there are 3n_phys bare channels, so on operator norm

    ||R^*||,||R_S^*||<=14n_phys gamma,
    ||R^*-R_S^*||<=12n_phys gamma exp[-(S/tau)^2].

Finite-dimensional exponential Duhamel therefore gives, for EVERY t>=0,

    ||exp(tR^*)-exp(tR_S^*)||_(infinity->infinity)
      <=12n_phys gamma t
             exp[14n_phys gamma t-(S/tau)^2].        (5)

No actual positivity, contraction or volume-independent generator norm is
assumed. Scalar H terms can be discarded from its commutator; the remaining
norm bound uses sum_Z||H_Z||<=n_phys*h. Equation(5) is an actual finite
volume bound with all volume factors displayed.

## A compatible scale for the static clock reached family

For N data blocks in the clock construction, clock size gives
n_phys=O(N log^3 N), at fixed compression tolerance. Let

    omega_N=omega0 N^(-alpha),
    t_N=N^(-beta)/gamma, eventually <=t_s,
    S_N=c0/omega_N, c0>0 fixed.

If 2alpha>1-beta, equation(5) tends to ZERO absolutely, since its negative
exponent is order N^(2alpha) and the positive one is at most
N^(1-beta)log^3 N. This is valid even on a global reached input of norm one.
It transfers any proven auxiliary RESPONSE back to the actual full base-
bath generator, rather than changing the physical question to a cutoff.

Meanwhile static clock delay is O(N^alpha log^3 N/omega0), and the
independent data amplification from (3) has logarithm >=c1 N^(1-beta)
for a positive fixed c1. These scales leave room for the admitted delayed
probe if alpha<1-beta. In particular alpha=1/3,beta=1/2 satisfies BOTH
strict inequalities. This compatibility is a scale lemma, not proof that
the connected response equals the independent response.

## Delayed Gaussian probes remain physically admitted

Exactly the positive even spectral modulation in THERMAL-LAG-ADMISSION.md
can be applied to J_G. For fixed 0<delta<1 use
epsilon_L=delta/cosh(L/tau) and J_L=J_G(1+epsilon_L cos(omega L)).
Its shifted covariance has the SAME beta and a common exponential
envelope Gamma=(1+delta)gamma, with common floor at least
b_G gamma/2=(b_G/[2(1+delta)])Gamma when the other half-strength channels
remain. Choose h<=b_G gamma/2 and Gamma*tau inside the ORIGINAL geometry
box. Thus Gamma,tau,b0 and geometry are fixed as L and N vary.

The previously proved full-filter delayed-source approximation applies:
its main term is epsilon_L b_G gamma U_H(L)A, with all finite-width and
tail errors retained. The square-window comparator must keep this same
modified covariance and its original ordered Lamb shift. No lower bound
for their full predictions is being claimed here.

The Gaussian cutoff estimate(4)-(5) applies to the UNSHIFTED baseline
covariance. The delayed covariance has a pulse near L; it must not be
assigned that baseline Gaussian tail bound or silently cut off by it.

## Exact next response obligation

The required new supplier is a sign-preserving or relative lower estimate
for the actual connected AUXILIARY R_(S_N) on the clock-reached family,
with its clock inputs defined by the positive preimage mixtures at t_N.
Equation(5) then makes this an actual FULL-generator response statement.
One possible approach is a finite-block expansion in the weak logical
clock links: first-order clock hopping is off diagonal, and a useful bound
would control the touched-clock contributions without replacing their
functional by a product after coupling. No such expansion or lower bound
has been proved in this note. A generic global norm Duhamel bound alone
does not supply it.

Even after that supplier, converting propagated generator amplification
into a lower bound for the ORIGINAL comparator requires a separate
argument. A possible bounded-parameter polynomial/Markov argument would
have to prove its actual delayed-bath derivative and approximation bounds;
it is only a follow-on idea here. General P5 remains OPEN.
