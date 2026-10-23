# Static parallel clocks with fixed qubit interactions

21 October 2026. Self-reviewed hand-proof candidate for PREPARED-CLOCK
root reachability. No actual connected Redfield response is asserted.
Finite controls and remaining review are recorded in PROGRESS.md.

The engineered spin-chain ingredient is standard: see Christandl, Datta,
Ekert and Landahl, [quant-ph/0309131v2](https://arxiv.org/pdf/quant-ph/0309131v2),
equations(12)-(15), actually inspected. It identifies the engineered
one-excitation chain with a spin rotation. The normalization below keeps
each physical interaction bounded as the chain length grows. The scheduling
and error argument here is an authored assembly, not a novelty claim or a
result attributed to that paper.

## Explicit logical Hamiltonian

Let a circuit have G>=1 unitary gates on at most two data qubits each,
in D>=1 layers numbered l=0,...,D-1. Gates in one layer have disjoint data
supports. Choose an even integer d>=16D and a frequency omega>0. Each gate
g receives its OWN chain of d+1 CLOCK QUBITS, numbered j=0,...,d, initially
in the computational-basis string with one excitation at j=0.

Put

    Delta=pi d/(4D omega),
    omega_l=omega D/(D+l),
    a_(l,j)=(omega_l/d)sqrt((j+1)(d-j)),  j=0,...,d-1,
    L=2D Delta=pi d/(2omega).

Each a_(l,j)<=omega. Every clock bond is ordinary excitation hopping,
except its central bond j=d/2, whose forward hop applies gate U_g to its
data and whose backward hop applies U_g^dagger:

    a_(l,j) (|01><10|_(j,j+1) tensor V_(g,j)
                +|10><01|_(j,j+1) tensor V_(g,j)^dagger),

where V_(g,j)=U_g on the central bond and I elsewhere. Call the sum K.
This is ONE time-independent Hermitian Hamiltonian on qubits. Each term
has norm a_(l,j), support size at most four, and preserves one excitation
per clock chain. The Hamiltonian is defined on the full qubit Hilbert
space; this last invariant sector is used only to prove the prepared-clock
compression, not to delete physical noise channels.

Let |c> be the product of all initial clock strings. If every data qubit
participates in at most q gates, the logical incidence is <=max(q,2)omega.
No clock site couples to all positions of a chain and no local Hilbert
space dimension grows with d.

## Free-clock distribution, including all constants

On a chain's one-excitation space, removing the U_g dressing gives the
tridiagonal matrix (2omega_l/d)J_x for spin d/2. Equivalently this is
(omega_l/d)sum_(a=1)^d X_a restricted to its symmetric subspace; the d
auxiliary spins in this identity are a mathematical representation, not
additional physical clock hardware. Starting at j=0, its amplitudes are

    sqrt(binomial(d,j)) cos(theta)^(d-j) [-i sin(theta)]^j,
    theta=omega_l t/d.

Thus j has the EXACT Binomial(d,p_l(t)) distribution with
p_l(t)=sin^2(omega_l t/d). On 0<=t<=L every theta is in [0,pi/2], so p_l
is monotone. The central arrival time is

    t_l=(D+l)Delta.

At distance at least Delta/2 before or after t_l,

    p_l(t)<=1/2-1/(8D),  or  p_l(t)>=1/2+1/(8D),    (1)

respectively. Indeed the angular margin is at least pi/(16D), and
sin(2a)>=4a/pi on 0<=a<=pi/4. The one-sided binomial tail estimate
Pr(j/d-p>=a)<=exp(-2d a^2), and its lower-tail version, follows directly
from the centered Bernoulli exponential-moment bound exp(lambda^2/8).

If gate g is in an earlier layer than h, split time at their arrival-time
midpoint. Before that midpoint h is unlikely to be right of its central
bond. After it, g is unlikely to be on either of its two central sites.
Since d>=16D accounts for the one-site endpoint offset, at EVERY t in
[0,L] the product of these two free-clock probabilities is at most

    exp[-d/(128D^2)].                               (2)

At t=L every clock is right of its central bond except with probability
at most exp[-d/(128D^2)]. All these probability estimates refer to the
explicit free clocks and are uniform in the arbitrary data state.

## Gauge comparison handles noncommuting gates

Order gates by circuit layer (arbitrary order inside a disjoint layer).
For a clock configuration z let x_g(z)=1 if clock g is right of its central
bond, and zero otherwise. Define the block-diagonal unitary

    W(z)=U_G^x_G ... U_1^x_1.

Let K_free be the sum of the free clocks on the invariant sector, and
K_id=W K_free W^dagger. Initially W(c)=I. Its evolution is exactly
W exp(-itK_free)|c> tensor the input data state.

For a central forward hop of clock g, K_id applies

    U_later U_g U_later^dagger,
    U_later=product of the already-right later gates.

K applies U_g. Their difference is zero unless a strictly later layer
already has a right-hand clock; gates in g's own layer commute with U_g.
For each bad later clock h the difference on the ideal evolving state
has norm <=2omega times the square root of the probability in (2).
The data-dependent W(z) preserves each clock-configuration probability.
Summing over at most G^2 ordered pairs and using unitary Duhamel proves,
UNIFORMLY in the normalized data input psi,

    ||[exp(-iLK)-exp(-iLK_id)] |c,psi>||
       <=2omega L G^2 exp[-d/(256D^2)].              (3)

At time L the ideal state differs from
exp(-iLK_free)|c> tensor C psi, C=U_G...U_1,
only where at least one clock is still left. Its norm error is at most
2sqrt(G) exp[-d/(256D^2)]. Hence the final circuit isometry error is

    E_d=[pi d G^2+2sqrt(G)] exp[-d/(256D^2)].        (4)

This comparison uses a nonlocal gauge Hamiltonian only as an EXACT proof
object. The physical K above has remained static and four-local throughout.
No scheduled external switch is part of its implementation.

For an entirely explicit choice, let 0<epsilon<=1,
u=log(e G D/epsilon)>=1 and d=2ceil(4096D^2 u). Then d>=16D and E_d<=epsilon.
For example d<=8194D^2u, so the prefactor in (4) is <=32778D^2uG^2.
Using 32778<e^11, u<=e^u and (GD)^2<=epsilon^2 e^(2u), the product is
<=epsilon^2 exp(-18u)<=epsilon. All constants are deliberately conservative.

## The root-to-parity compression and admitted physical embedding

On an N-vertex finite binary tree use CNOT(child -> parent), scheduled
from leaves toward the root, with two disjoint rounds per depth. There
are G=N-1 gates, D<=2ceil(log2 N), and each data vertex participates in
at most three gates. For the resulting circuit C,

    C^dagger Z_root C=product_(data v) Z_v.

The isometry estimate above gives the actual operator-norm compression

    ||<c|exp(iLK)Z_root exp(-iLK)|c>
                         -product_v Z_v||<=2E_d.    (5)

It does NOT claim a full-clock-Hilbert-space approximation to that parity.
It is sufficient at the independent base functional in equation(7) of
SYMMETRIC-AMPLIFIER-AND-CLOCK-PREIMAGES.md, because its allowed positive
physical clock inputs make the clock functional exactly |c><c| at t_s.

Embed each logical site in that fixed noisy three-qubit block. Use the
bare-root embedding pi_root(Z)=Z1, pi_root(X)=X1Y2X3; use pi(Z)=W on
other data and clock blocks. Choose

    H_phys=sum_b H_(c,b)-pi_all(K).

The MINUS sign is intentional: source U_H(L)A=exp(-iLH)Aexp(iLH)
on the bare root A=Z1 is exactly pi_all[exp(iLK)Z_root exp(-iLK)].
Every encoded link commutes with the base gauge Hamiltonian. The same
full H_phys must still be used in every actual Redfield filter.

Each logical data neighborhood has size <=10: itself, <=3 data neighbors,
and two clock sites per incident gate. A clock neighborhood has size <=5.
Thus common physical bounds, INDEPENDENT of N and d, are

    k<=12, m<=30, nu<=30, h<=J+3omega.

Taking J<=b0 gamma/2, 3omega<=b0 gamma/2 and
gamma tau<=1/(360*2^30) gives the ORIGINAL P5 box with all physical
thermal channels retained. The local clock-block Hilbert space is fixed;
the number of noisy blocks grows. The runtime is
L=O(log^3(N/epsilon)/omega) at fixed epsilon, and clock hardware is
O(N log^3(N/epsilon)) logical qubits. An onsite Pauli term of fixed strength
on an unrelated noisy site can fix the exact maximal incidence across volumes if needed;
no such addition is required for the stated common upper bounds.

## What this closes, and what it does not

This supplies a concrete static, fixed-locality PREPARED-CLOCK root-flow
hand-proof candidate with quantitative sublinear runtime and operator-norm
compression error. The positive clock-preimage lemma supplies its
independent-base functional interpretation. Separate review/formalization
of this assembly has not occurred.

The connected ACTUAL Redfield response of H_phys, rather than the
independent base response, remains unproved. Its full filters change when
K is added, even though the base energy and the root orbit identities are
exact. Propagated delayed-filter errors and the ORIGINAL square-window
comparison lower bound remain missing. This is not a counterexample to
P5, not an actual-response estimate, and not permission to tensorize after
coupling. The unrestricted master remains OPEN.
