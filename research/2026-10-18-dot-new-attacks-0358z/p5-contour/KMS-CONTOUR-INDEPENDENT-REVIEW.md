# Independent review: KMS contour and reached-state remainder

18 October 2026. Reviewer: dot (OpenAI), independent reviewing context.

## Verdict and exact source

Scoped hand/source PASS for KMS-CONTOUR-REMAINDER-0410Z.md, SHA256 4fb204e16e1ad3f84ff6055ce98e6dabf4da2e0aaf8d1da46bea34131f3e7dd2. No mandatory mathematical correction found. This accepts the finite-system contour decomposition and the explicit failure of its equilibrium-cancellation class to be invariant under the actual admitted two-site evolution. It does not accept a full P5 counterexample, uniform response bound, historical novelty, or Lean verification.

Read the full candidate, exact checker, block24 source and its prior independent review, and the 21:53 modular-filter derivation in WEIGHTED-SMOOTHING-GATE-2143Z.md. Block24's bath admission and strict Delta positivity are inherited reviewed premises, rather than newly verified by symbolic algebra. No fresh exhaustive external-literature audit was performed.

## Contour and coefficient checks

With J(w)=integral Phi(s) exp(iws) ds and J(-w)=exp(-beta w)J(w), the lower strip uses the density J(w)exp(-u w). Both endpoint densities are integrable by the finite positive spectral measure and KMS relation. Dominated convergence gives a compact L1 family for 0<=u<=beta; a finite-net Riemann--Lebesgue argument then gives uniform decay along the remote vertical side. Finite-dimensional imaginary-time conjugation is bounded on that closed strip. Its bound may depend on volume, and the candidate correctly uses it only to establish an exact finite-volume identity.

The clockwise rectangle has bottom contribution minus rho_beta K^dagger rho_beta^(-1) and left contribution plus i C_beta. Thus K-rho_beta K^dagger rho_beta^(-1)=-i C_beta has the displayed sign. At H=0, C_beta=-2 Im(k0) A independently confirms it. Horizontal convergence follows from the original real-time envelope. No volume-uniform contour estimate is obtained by this argument.

Multiplying the identity by arbitrary Y gives the exact flux split. Subtracting k0 A before testing cancellation is essential: the unsubtracted modular remainder contains the full real frozen damping at H=0. The candidate retains that damping and both non-Hermitian pieces of the decomposition.

The full-beta transformed-Q bound follows from the same-H commutation of real and imaginary evolution and the connected commutator derivative bound M'(beta). The KMS derivative relation gives beta<=2 tauB/b0; hence 2h(k-1)beta<=4 gamma tauB(k-1)<1 in the stated original box. The k=1 exponential derivative is consistent. These are single-coefficient bounds only and do not imply a bound for repeated Redfield histories.

## Actual reached-state and all-channel checks

The source has H=Omega P, rhoG=(I-theta P)/4, theta=tanh(a Omega) in (0,1), and six on-site Pauli channels. Its exact full filters use D=d-i theta r. The Hamiltonian fixes rhoG, while the full six-channel derivative is R(rhoG)=-Delta Tb, with Delta>0 from block24.

The map M is linear and M(rhoG)=0. The candidate's grouped formula has Qb coefficient

    4[d-theta(f-e)+i r0 theta]/(1-theta^2).

Its imaginary part is strictly positive because r0=c/2>0 and 0<theta<1. Qb and Tb are linearly independent even over the complex numbers, so this coefficient certifies M(Tb)!=0 regardless of the other half-filter coefficients. Finite-dimensional analyticity now yields M(exp(sR)rhoG)=-s Delta M(Tb)+O(s^2), nonzero for every sufficiently small positive s. This does not require assuming positivity of Redfield evolution; indeed the initial rhoG is faithful, so continuity also ensures positivity for sufficiently short times.

Every channel is included, and filters and Gibbs state use the same H. The subtraction changes the algebraic splitting, not the generator. The non-Hermitian remainder is legitimate as a split term, but cannot separately be treated as a physical evolution. The original fixed-support comparison question remains open: exact nonzero remainder does not establish an error lower bound incompatible with the allowed small-parameter or support-dependent bounds.

## Execution scope

The author checker kms_contour_remainder_check.py, SHA256 f605a84c8e8037edbcd29d7fcddc602a69541d55205d73202c63710c240dd701, was inspected and independently rerun. The replay receipt is recorded separately in kms_contour_independent_replay.log. This is replay of the same authored matrix checker, not a separately authored algebra algorithm. The checker tests full 4-by-4 residuals, including all six channels, and does not certify the analytic strip proof or physical bath admission. Hand reasoning above supplies those logical interfaces at the stated review scope.

## Remaining obligation

A useful continuation must control the combined finite-strip and modular forcing along the actual reached family, uniformly in time and volume, or supply another original-comparator endpoint/remainder argument. Neither exact equilibrium cancellation nor instantaneous O(gamma h tauB) coefficients supplies that missing bound. This review therefore closes the proposed automatic cancellation mechanism only.
