# Coordinating hand review: reservoir-amplified clone locks

2026-10-17 20:15 UTC. Reviewer: dot, coordinating pass separate from the producing pass. This is mathematical hand review, not external peer review, formal verification, or numerical execution.

Reviewed candidate: P1-RESERVOIR-AMPLIFIED-LOCK-CANDIDATE-24.md, SHA256 1e43bc2ab48800c2807baab6cf98701d110fb86405eeda866723392e6474b646.

## Verdict

Accepted at scoped coordinating hand-proof level for the candidate's fixed k>=3, fixed beta>0 and fixed 0<epsilon<=1/4, coefficientwise-bounded, at-most-k-local Gibbs-state testing experiment with unrestricted degree and total per-site interaction strength. The component lower bound is Omega(N^(2k/3)/(log N)^(2/3)) for all sufficiently large N. The prior lower bound is preserved; the improved logarithm does not resolve the exponent gap to O(N^k log N), the full accuracy dependence, or k=2.

## Checks

1. The conditional clone lock strength is mu_R=2j binom(R,k-2), obtained from distinct physical supports. Same-block penalty pairs are the only signal/lock support collision, with combined coefficient at most beta/8+beta/32. Signal monomials have at most one clone from each block. Removing the scalar identity coefficient does not affect Gibbs states.
2. The minority-count argument retains both halves of the lock energy. The rounded-weight penalty gives g(a)>=4a log(2s); the finite leakage inequalities imply the stated conditional total variation bound. The ideal shell partition is exactly one.
3. The reservoir perturbation includes the entire lock magnitude B0. Near plus, changed subset products cost at most 2kl(S0+B0)/R. Exactly-one-minus k-subsets supply the required reservoir energy margin. No independence between clone and reservoir configurations is assumed.
4. Even k uses the exact simultaneous clone flip and the reservoir field penalty to control the second phase. Odd k uses all-minus k-subsets and gamma C>=2(S0+B0); the even-phase identity is not incorrectly imported.
5. With R proportional to sm, the new B0 contribution to the strength ratio is O_k(1/(C_*^2 s)). The original S0 contribution is controlled by m^k>=16(V+lambda)/beta and large constant C_*. Hence m=O((log s)^(1/k)) and all reservoir/clone spins give N_s=O(s(log s)^(1/k)). This construction depends essentially on unrestricted interaction degree.
6. Smoothing preserves exact equality and leaves sufficient trace-norm separation after leakage. The ideal source simulator needs samples only. Diagonal-state measurements, including collective and adaptive processing with a worst-case total budget, reduce to classical postprocessing with at most a constant-factor sample cost. Padding with maximally mixed zero-Hamiltonian spins covers all sufficiently large physical sizes.

For the amplification step, take a sufficiently small constant c in T<=cL, including the fixed repetition factor in the budget. Then the hybrid error T*eta remains small while amplification restores success above the classical supplier's threshold. This is a constant-factor clarification, not an extra asymptotic claim.

## Sources and limits

Independently read the accepted shell21 coordinating review at commit5055e470b32c17bdf93c55e09a891969be9ea23f, research/2026-10-16-g6-gibbs-certification/FIXED-BETA-ALL-K-SHELL-21-COORDINATING-REVIEW.md, and the full present candidate.

Independently reopened Chan, Diakonikolas, Gregory Valiant and Paul Valiant, Optimal Algorithms for Testing Closeness of Discrete Distributions, Theorem1.1, PDF page2: https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf . The categorical lower bound is their established result. The present review checks its transfer and the changed physical encoding; it does not claim historical priority for either.

No Lean build, experimental validation, efficient preparation, bounded-degree result or complete P1 solution follows. No P5, G3 or G4 obligation is discharged by this bound.
