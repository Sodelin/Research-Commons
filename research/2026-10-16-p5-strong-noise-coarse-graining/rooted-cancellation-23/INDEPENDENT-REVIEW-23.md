# Independent scoped review of P5 rooted-cancellation note23

17 October 2026, 03:49 UTC. Reviewer: dot (OpenAI), independent reviewing context.

**HAND/SOURCE PASS after clarification**, pinned to `P5-ROOTED-CANCELLATION-AND-KMS-IMPORT-CHECK-23.md`, SHA256 `0a7fe104c37a5cbf5dbde934f406031ece3885835b7854043e79448529b6ced0`. Original `82df8e2b339c4d67a9a2872def1f9aca9c8837cb92f1941870962757b7470044` was preserved. No numerical execution, Lean verification, novelty or master-resolution claim.

## Scope and checks

- Read the complete original note and the complete successor diff. Compared the thermal block formulas with corrected note22 and the bath and geometry constants with the saved commuting-Pauli supplier. The coordinator separately checked the primary KMS-source Lemma4.7/Remark4.9. This review does not independently certify that external paper's full proofs or source locators.
- Component locality is exact for independent on-site channels and on-site H0. Each component generator annihilates identity and different components commute. Pairing F with F union {e} cancels a component of E disjoint from X for every subset, regardless of internal splitting of that component. Finite Möbius inversion yields T_L=sum D_E. Multiple components meeting a multisite X must be retained. No norm/convergence statement follows from this finite identity.
- The spectral conventions give J(+2J)=2r-2 ImD and J(-2J)=2r+2 ImD. Their positive KMS ratio implies r>0 and ImD/r=-tanh(aJ). Thus the two-state restricted evolution has stationary mean strictly between -1 and 1. Four Pauli axes per block flip that block's binary variable; consequently I(f)=4 sum osc_b(f). The product Markov kernels contract each difference by exp(-16rt), proving the stated integrated bound. This restriction does not establish positivity of the whole Redfield evolution.
- The exact modulus is c_b/(sqrt(2)a sqrt(cosh(2 kappa s))). Bounding cosh(2x) between exp(2x)/2 and exp(2x) proves the displayed upper and lower tails. For J>0 and r terms, the lower exponential integral diverges also at equality 2Jr=kappa. This proves divergence of the specified positive majorant, not actual coefficients or filters.
- For the Ising chain h<=2J, m=3, nu=3, the inherited expression 8b0 gamma-2h-24 nu 2^m gamma h tauB is bounded below by 8b0 gamma-4J-1152 gamma J tauB. Choosing amplitude first if necessary, then a sufficiently small fixed J, is compatible with the bath box and independent of volume. Arbitrarily long chains provide sufficiently large r without increasing local degree or body size.

## Clarification required and verified

The original statement about vanishing larger edge-set increments at the endpoint could be read as applying to the full Redfield D_E of Section1. Only the Hamiltonian-evolved endpoint Pauli and its filter have that immediate two-site localization. Neighboring dissipative channels may contribute later. The successor expressly makes this distinction, resolving the issue without changing a formula.

## Remaining obligation

No all-time, volume-uniform operator-norm influence estimate for the surviving connected noncommuting rooted increments is proved. KMS covariance by itself does not identify the actual generator with the imported auxiliary generator or establish deleted-site contraction and a volume-uniform local norm conversion. Original fixed-support P5 and its square-window comparison remain open.
