# Independent scoped hand review: strong-noise commuting-Pauli branch

Reviewer: dot, independent review lane. Date: 2026-10-16.
Reviewed candidate: P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md, SHA256 9731ab69a406ef42c7494bd2a5e20f21db6e114b7f72cd43f7df5e0550066c30.

Verdict: scoped mathematical hand-proof PASS. No blocking error found in the displayed generator-to-generator comparison under its explicit assumptions. This is not a formal verification, execution receipt, novelty determination, or acceptance of general P5 closure.

## Exact generator binding

Independently read [Ikeuchi–Mori, arXiv2604.21366v2](https://arxiv.org/html/2604.21366v2), definitions (5)–(10) and time-averaging formulas (19)–(20). Its frequency convention gives A(-s)=sum_omega exp(i omega s) A[omega]. Substitution reproduces the candidate's square-window dissipator, the order A(-s)A(-s') in the Lamb shift's first product, and the reversed order in its second product. The sign i/(2T) matches. The Redfield two-commutator expression matches the same one-sided correlation transform. Writing this explicit Fourier identity in the candidate would make the convention check easier to reproduce.

## Algebra and estimates checked

1. Commuting Hamiltonian terms allow discarding every term not incident on i in A_i(-s). The remaining generator has norm at most h, yielding exact support S_i and variation at most 2h|s|. This step genuinely uses mutual commutativity.
2. Freezing the Redfield channel gives 2b(A rho A-rho). Its adjoint correction is bounded by four times the integral of |Phi| times the operator variation, hence 8 gamma h tauB. At a nonidentity Pauli site exactly two of X,Y,Z anticommute, giving frozen damping at least 8b0 gamma per occupied site.
3. The finite-window kernel has absolute square integral divided by T at most 2gamma. The variation of the bilinear dissipator is at most twice the sum of the two operator variations. This gives 16gamma hT. The Lamb-shift variation has norm at most 4gamma hT and commutator norm at most 8gamma hT. The stated total 24gamma hT, relaxed to32, is valid.
4. The frozen coefficient error satisfies |c_T-2b|<=2gamma tauB/T, so its dissipator error is at most4gamma tauB/T. The frozen Lamb shift is scalar.
5. A local identity-annihilating channel contributes only if its support meets the Pauli support. The channel-count bound3nu w(P) is valid. Pauli coefficient l1 norm is at most2^m times operator norm on m sites, by normalized Hilbert–Schmidt orthogonality and Cauchy–Schwarz. Tensoring the unchanged outside Pauli introduces no factor depending on total volume.
6. The Hamiltonian Pauli-column bound2h w(P) follows by charging each anticommuting term to an occupied site. Together with the Redfield correction this yields exactly the displayed positive margin g.
7. Since R*(I)=0, nonidentity coefficients evolve autonomously; identity output can be omitted from the column bound. The upper derivative inequality for their l1 norm therefore gives D+V<=-gW. Integrating and using V>=0 yields the required integral bound. A drifting scalar does not re-enter this system or the generator difference.
8. Duhamel has the completely positive unital evolution on its OUTER side. Only that side needs operator-norm contraction. No positivity of Redfield is used. Combining the local difference bound with integrated W gives delta V(O)/g. The initial local-support inequality V(O)<=2^k||O|| is valid.
9. Substituting T=sqrt(tauB/gamma), x=gamma tauB and j=h/gamma gives exactly the displayed ratio. The sufficient box implies the denominator is at least4b0. Constants depend on local geometry and support, not volume or elapsed time.

## Bath feasibility checked

For J(omega)=c exp(beta omega/2)sech(a omega), beta=a, the inverse transform with exp(-i omega t)/(2pi) is c/(2a)sech(pi(t+i beta/2)/(2a)). Its spectral density is positive and obeys J(-omega)=exp(-beta omega)J(omega). The imaginary shift is inside the convergence strip. The stated cosh identity gives the envelope with tauB=2a/pi and gamma=2sqrt(2)c/pi. Stationarity symmetry gives Re integral_0^infinity Phi=J(0)/2=c/2=b0 gamma. The positive-frequency bosonic density I=J(1-exp(-beta omega))/(2pi) has the correct normalization against the thermal occupation factors. Its near-zero Ohmic behavior and exponential ultraviolet decay make the cited covariance integrals finite for each a>0.

This verifies a mathematically nonempty bath-input family. It does not establish a Born–Markov error estimate for the actual system-plus-bath dynamics. The singular a-down-to-zero regime changes bath temperature and spectral width; the candidate states that limitation.

## Scope and prior boundary

The claim is a restricted commuting, bounded-overlap, three-channel, positive-noise-floor, strong-noise result. It does not cover arbitrary weak noise at fixed h, noncommuting interactions, missing channels, arbitrary bath spectra, or multi-time interventions. The finite-volume inequalities are uniform, but no infinite-volume dynamical construction or exchange of limits is asserted.

The Duhamel/relaxation stability principle is established prior; the candidate credits this. This review independently binds the actual finite-window generator to the primary source, but does not certify an exhaustive prior-overlap search for strong-noise Pauli-norm estimates. Novelty remains unresolved. General P5 and microscopic approximation error remain open.
