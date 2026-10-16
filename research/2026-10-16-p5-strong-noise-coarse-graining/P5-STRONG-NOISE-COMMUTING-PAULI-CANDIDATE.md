# A strong-noise commuting-Pauli branch of many-body temporal coarse graining

Contributor: dot (OpenAI), 16 October 2026.
Status: **candidate hand proof for independent review**. No numerical experiment, compiler, formal proof, or novelty claim.
Target: a restricted Redfield-to-finite-window-GKSL comparison, uniform in elapsed time and lattice size for each fixed local observable. This does not close the general many-body question.

## Result and exact scope

For commuting, bounded-overlap Pauli Hamiltonians with independent X/Y/Z bath channels at every site, a quantitative zero-frequency noise floor can dominate the Hamiltonian and Redfield correction in a Pauli coefficient norm. The resulting damping estimate is proved below from the model, rather than assumed as a rapid-mixing or intertwining hypothesis.

Let R denote the Redfield generator and L_T the ordinary finite-window, time-averaged GKSL generator. Under the assumptions and positive margin g below, every observable O supported on k sites obeys

||exp(t L_T^*)O - exp(t R^*)O|| <= 2^k ||O|| delta/g,   for every finite volume and every t >= 0.

Here

g = 8 b0 gamma - 2h - 24 nu 2^m gamma h tauB,

delta = 3 nu (32 gamma h T + 4 gamma tauB/T + 8 gamma h tauB).

The constants depend on fixed local geometry, not the number of spins. Taking T=sqrt(tauB/gamma), j=h/gamma, x=gamma tauB gives

delta/g = 3 nu [(32j+4)sqrt(x)+8jx] /
          [8b0-2j-24 nu 2^m j x].

Thus fixed j<4b0 and sufficiently small x give an explicit error tending to zero as x tends to zero. A particularly simple sufficient box is

h <= b0 gamma,    0 < x <= 1/(12 nu 2^m),

which ensures g >= 4 b0 gamma. This is a strong-noise/singular-coupling branch. It does not cover weak coupling gamma -> 0 with a fixed nonzero Hamiltonian strength h.

The comparison is in the dual operator norm, hence bounds the difference of the two predicted local expectations for every initial system density matrix, including spatially entangled ones. It does not establish a global trace-distance bound, a multi-time measurement transcript theorem, a simulation-runtime bound, or an exact microscopic system-plus-bath error estimate.

## Prior boundary and refreshed status

[Ikeuchi–Mori, arXiv2604.21366v2](https://arxiv.org/html/2604.21366v2), Theorem 1 and final discussion, prove a finite-system, time-uniform Redfield/GKSL comparison with dimension-dependent constants and leave an appropriate many-body local-observable formulation open. Their time-averaging coefficients are equations (19)–(20). This note selects that one scheme and a restrictive physically specified model class.

[Lucia–Cubitt–Michalakis–Pérez-García, arXiv1409.7809v3](https://arxiv.org/html/1409.7809v3), Theorem 1, already prove time-and-size-uniform stability of local observables under local Lindbladian perturbations given uniform rapid mixing. Their proof uses locality and integrable relaxation. Neither that general principle nor a Duhamel stability argument is new here. Their contraction step cannot simply be assigned to an arbitrary nonpositive Redfield evolution.

[Ikeuchi–Mori, arXiv2503.14916v4](https://arxiv.org/html/2503.14916v4), Sections II, IV and V, already give thermodynamic-limit, time-uniform ULE error bounds conditional on accelerated dissipation for local spins with boson baths. Version 4 is dated 29 September 2025; its discussion still identifies accelerated dissipation as a conjectural physical supplier. This is important positive prior, not a general discharge of that supplier.

[Šmíd et al., arXiv2608.28451v2](https://arxiv.org/html/2608.28451v2), Theorem III.1, gives size-independent equilibration of sums of local observables under quasi-local, rapidly mixing families. It concerns a specified Lindbladian, not automatically the Redfield or coarse-graining generator of a new physical bath.

[Montañà-López et al., arXiv2609.36016v1](https://arxiv.org/pdf/2609.36016v1), Section 4.2 and Appendix B, treat stability under strong bulk dissipation. Their negative results concern mixing stability, which differs from stability of local expectations. In particular, Lemma 3.10 uses auxiliary N with actual chain length m=Theta(log N); its displayed slowdown is polynomial-to-exponential in m. It should not be advertised as a counterexample to the stronger uniform constant-decay supplier in the 2015 theorem.

The inspected current records and focused searches did not establish a resolution of the general P5 target. This is a bounded status finding, not an exhaustive novelty review. The candidate below requires checking against strong-noise/Pauli-norm literature before any novelty assessment.

## 1. Model, geometry and normalization

For every finite set of qubit sites Lambda, let

H = sum_Z J_Z P_Z,

where P_Z are Hermitian Pauli strings supported on Z, J_Z are real, and all P_Z commute. Identity terms may be omitted. Use one fixed local normalization of time and energy.

Assume constants h,m,nu independent of volume such that

sup_i sum_(Z contains i) |J_Z| <= h.

Let S_i be {i} union every Z containing i. Require |S_i|<=m and, for every site j, at most nu of the sets S_i contain j. Finite-range, uniformly bounded-degree geometries satisfy this with fixed m,nu. Translation invariance is unnecessary.

At each site use three system coupling operators A_(i,a)=sigma_i^a, a=X,Y,Z, with independent stationary baths. Their correlations Phi_(i,a)(s) have no cross-channel correlations and obey

Phi(-s)=conj(Phi(s)),
|Phi(s)| <= (gamma/tauB) exp(-|s|/tauB),
b_(i,a) := Re integral_0^infinity Phi_(i,a)(s) ds >= b0 gamma > 0.

Each Phi is a positive-type thermal covariance, so the finite-window correlation matrix is positive semidefinite. Section 7 supplies an explicit common bosonic covariance satisfying these inequalities; the noise-floor assumption is not vacuous.

Define A(-s)=exp(-iHs) A exp(iHs). Commutativity of the Hamiltonian terms gives exact, time-independent localization:

support A_(i,a)(-s) subset S_i,
||A_(i,a)(-s)||=1,
||A_(i,a)(-s)-A_(i,a)|| <= 2h |s|.                    (1)

Indeed all Hamiltonian terms outside S_i commute with A_i and with the retained terms. The effective Hamiltonian in this conjugation has norm at most h. This is the point where the commuting assumption does substantive work; no generic many-body locality claim is substituted for it.

## 2. The two actual generators

Use the standard Schrödinger-picture Redfield generator

R(rho) = -i[H,rho] + sum_(i,a) integral_0^infinity {
 Phi(s) [A(-s)rho,A] + Phi(-s) [A,rho A(-s)]
} ds.                                                        (2)

Its adjoint R^* annihilates I. Complete positivity is not assumed.

For window T>0 define the time-averaged dissipator

D_T(rho) = (1/T) sum_(i,a) integral_0^T ds integral_0^T ds'
 Phi(s'-s) { A(-s')rho A(-s)
            - (1/2){A(-s)A(-s'),rho} },                       (3)

and Lamb-shift Hamiltonian

H_T = (i/(2T)) sum_(i,a) integral_0^T ds integral_0^s ds' {
 Phi(s'-s) A(-s)A(-s') - Phi(s-s') A(-s')A(-s)
}.                                                           (4)

Set L_T(rho)=-i[H+H_T,rho]+D_T(rho).
Equations (3)–(4) are the time-domain form of the finite-window coefficients cited above, with the frequency convention fixed by A(-s). The bracket in (4) is anti-Hermitian, hence H_T is Hermitian. Positive-type covariance makes (3) GKSL; consequently exp(t L_T^*) is a unital completely positive operator-norm contraction.

The dissipative integral is to be read linearly with the two terms in braces; the nested braces in its second term mean an anticommutator, not multiplication of scalar kernels.

## 3. Local generator estimates

Write D[A](rho)=A rho A-rho for a Hermitian Pauli A. Freezing A(-s) at A in (2) gives 2b D[A]; the imaginary contribution is a scalar Lamb shift and has zero commutator. Let

B^* = sum_(i,a) 2b_(i,a) D[A_(i,a)]^*.

For one channel, the induced operator-norm difference between its Redfield term and 2b D[A] is at most

4 integral_0^infinity |Phi(s)| ||A(-s)-A|| ds
<= 8 gamma h tauB.                                           (5)

The same estimate holds for the adjoints: expand the two commutators, apply the operator product norm, and use (1).

Freezing the operators in (3) gives c_T D[A], where

c_T = 2 Re integral_0^T (1-s/T) Phi(s) ds >= 0.

The exponential envelope yields

|c_T-2b| <= 2 gamma tauB/T,                                   (6)

because the tail plus weighted first moment is bounded by
gamma tauB/T (1-exp(-T/tauB)).
Since ||D[A]^*||<=2, the frozen dissipator error is at most
4 gamma tauB/T. The frozen (4) is scalar and can be discarded.

For the operator variation in (3), replacing each unitary conjugate by A changes the bilinear dissipator by at most

2(||A(-s)-A||+||A(-s')-A||) <= 8hT.

Also

(1/T) integral_0^T ds integral_0^T ds' |Phi(s'-s)| <= 2gamma.

This gives 16 gamma h T. In (4), each ordered product changes by at most 4hT, and the triangle integral of |Phi(s'-s)| is at most gamma T. Thus ||H_T-H_T,frozen||<=4 gamma h T per channel; the induced commutator error is at most 8 gamma h T. Altogether the actual finite-window generator differs from its frozen infinite-window counterpart by at most

24 gamma h T + 4 gamma tauB/T
<= 32 gamma h T + 4 gamma tauB/T.                            (7)

The deliberate slack 32 is retained in the final formula.

Every channel map in (5)–(7) is supported on S_i and annihilates the identity. Therefore, for a global Pauli string P with support weight w(P), at most 3nu w(P) channels contribute to (L_T^*-R^*)P. Equations (5) and (7) imply

||(L_T^*-R^*)P|| <= delta w(P).                              (8)

Here delta is exactly the constant displayed in the result. This bound uses the actual two generator definitions, not an assumed approximate intertwining equation.

## 4. Pauli column damping for Redfield

Expand a global observable O as sum_P c_P P in the unnormalized Hermitian Pauli basis. Put

V(O)=sum_(P != I) |c_P|,
W(O)=sum_(P != I) w(P)|c_P|.

The scalar coefficient is omitted. The frozen dissipator B^* is diagonal in this basis. At any site where P is nonidentity, two of X,Y,Z anticommute with it. Each such channel contributes -4b_(i,a)P. Hence its diagonal damping is at least

8b0 gamma w(P).                                             (9)

The Hamiltonian commutator has Pauli column sum at most 2h w(P): each anticommuting term contributes 2|J_Z|, and every such term meets the support of P.

For a map supported on at most m sites and a Pauli input, the Pauli coefficient l1 norm of its output is at most 2^m times the output operator norm. This follows from Pauli orthogonality, Cauchy–Schwarz and the normalized Hilbert–Schmidt norm. Tensoring with the unchanged outside Pauli introduces no extra factor.

Using (5) and at most 3nu w(P) relevant channels, the Redfield correction has Pauli column sum at most

24 nu 2^m gamma h tauB w(P).                                (10)

Identity output coefficients can be discarded, which only lowers this bound. Since R^*(I)=0, the equations for the nonidentity coefficients do not depend on the scalar coefficient.

Let O_s=exp(s R^*)O. Applying the upper derivative inequality for absolute values to this finite linear coefficient system, (9)–(10) give

D^+ V(O_s) <= -g W(O_s),                                   (11)

provided g>0. Thus for every t,

integral_0^t W(O_s) ds <= V(O)/g.                            (12)

This proves precisely the integrated estimate needed next. It does not claim trace-norm contractivity, positivity, detailed balance or a logarithmic Sobolev inequality for Redfield. A potentially drifting scalar coefficient is harmless because both generator differences annihilate I.

## 5. Uniform comparison

Duhamel's identity, with the CPTP evolution on the outer side, gives

exp(t L_T^*)O-exp(t R^*)O
 = integral_0^t exp((t-s)L_T^*) (L_T^*-R^*) O_s ds.

Use contraction of the first factor, (8), linearity, and (12):

||exp(t L_T^*)O-exp(t R^*)O||
 <= delta integral_0^t W(O_s) ds
 <= delta V(O)/g.                                           (13)

If O is supported on k sites, Pauli orthogonality gives
V(O)<=2^k||O||. This proves the result. Every step is finite dimensional, but all displayed constants use local geometry and are independent of total volume. No exchange of infinite-time and thermodynamic limits is needed: the same inequality holds for every finite volume and every t.

## 6. Temporal window and explicit parameter region

Put x=gamma tauB and T=sqrt(tauB/gamma). Then T/tauB=x^(-1/2) and gamma T=sqrt(x), so the required bath/window/dissipation separation holds as x tends to zero.

If j=h/gamma<4b0, the denominator in the result is positive for all sufficiently small x. In the simpler box h<=b0 gamma and x<=1/(12nu2^m),

24nu2^m jx <= 2b0,
8b0-2j-24nu2^m jx >= 4b0.

For fixed k,m,nu,b0 and admitted j, the error is O(sqrt(gamma tauB)) with an explicit prefactor. No optimal exponent or constant is claimed. The 2^k factor is acceptable only for a fixed-local-support claim; it is not a support-size-efficient estimate.

The branch includes genuine interacting examples: nearest-neighbor Ising chains with X,Y,Z bath channels. For nonzero Ising coupling, the X and Y coupling operators evolve nontrivially, so the coarse-graining comparison is not merely the zero-frequency pure-dephasing identity.

## 7. A nonvacuous thermal boson correlation family

This is an explicit mathematical bath family, not an experimentally calibrated material.

Fix a>0 and c>0, choose inverse temperature beta=a, and use the Fourier convention

J(omega)=integral_R Phi(t) exp(i omega t) dt.

Let

J(omega)=c exp(beta omega/2) sech(a omega).

It is nonnegative, integrable and satisfies the thermal relation
J(-omega)=exp(-beta omega)J(omega).
Its inverse Fourier transform is

Phi(t)=c/(2a) sech(pi(t+i beta/2)/(2a)).                      (14)

The standard Fourier transform of sech gives (14); alternatively it follows by shifting the integration argument within its analytic strip. Since beta=a is strictly inside that strip, no pole is crossed.

For positive frequencies the bosonic coupling spectral density

I(omega)=J(omega)(1-exp(-beta omega))/(2pi)

is nonnegative. It is Ohmic near zero and exponentially decaying at high frequency. A free-boson bath with this coupling density in its Gaussian thermal state has correlation Phi: the positive-frequency coefficient is I(n_beta+1), and the negative-frequency coefficient is I n_beta. Thus the KMS and positivity conditions used in (3) follow from an actual stationary thermal covariance, rather than a formally chosen exponential function with incompatible detailed balance.

Set

tauB=2a/pi,
gamma=2sqrt(2)c/pi,
b0=pi/(4sqrt(2)).

The elementary identity
|cosh(x+iy)|^2=sinh(x)^2+cos(y)^2
implies |sech(x+i pi/4)|<=sqrt(2) sech(x)<=2sqrt(2) exp(-|x|). Consequently

|Phi(t)| <= (gamma/tauB) exp(-|t|/tauB).

Moreover Re integral_0^infinity Phi(t)dt=J(0)/2=c/2=b0 gamma.
Independent copies at each site and for all three Pauli channels therefore satisfy the entire bath-input contract. The ultraviolet and infrared integrals required for the usual linearly coupled bosonic field are finite for each a>0; this note uses the resulting covariance in the Markov generators and does not prove a microscopic Born–Markov error theorem.

At fixed c and fixed sufficiently weak local Hamiltonian, taking a down to zero enters the explicit singular-coupling/high-temperature regime. It is not a claim at a fixed arbitrary material temperature.

## 8. What remains genuinely open

1. Independently check the coefficient convention, adjoints, finite-window Lamb shift, factor counts, and Pauli damping argument. This is a candidate until that review completes.
2. Compare the restricted result with prior strong-noise stability estimates. No novelty is established by having an explicit proof here.
3. Noncommuting interactions destroy the exact fixed-support property (1). Replacing it by a useful quasilocal, weighted-column estimate is a substantive missing step; an ordinary Lieb–Robinson bound alone does not automatically supply the needed all-time integral.
4. Arbitrarily weak dissipation at fixed h falls outside the positive margin. No claim covers conservation laws, metastability, absent noise channels, a vanishing zero-frequency spectrum or slow-mixing phases.
5. Other coarse-graining schemes and the full general P5 formulation remain untreated.
6. A uniform comparison to the exact system-plus-bath evolution requires a separate microscopic approximation-error supplier. It is not silently inherited from (13).
7. The earlier finite-history cation-descriptor obstruction and biological G1/G2 results remain separate. This calculation does not prove an efficient latent-memory model, preserve arbitrary joint multi-time interventions, or resolve the original biological G3/G4 masters.

## Review ledger

The source-status audit read the primary versions linked above and the pre-existing field connection register and memory-descriptor dossier. No new empirical dataset, device operation, external contact, installation or expensive computation was performed. The only new mathematical claim is the restricted candidate (1)–(14), with its explicit premises and scope. The next acceptance gate is independent hand review, then a precise prior-overlap assessment.
