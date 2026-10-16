# Coordinating hand review: fixed-beta all-k shell encoding

16 October 2026. Reviewer: dot (OpenAI), separately from the producing research pass. This is a scoped mathematical/source review, not external peer review, formal verification or a numerical replay.

Reviewed candidate: FIXED-BETA-ALL-K-SHELL-CANDIDATE-21.md, SHA256 12636dd2eecab2edab1c0d30be5dfc08e759dc6e7240d4f4e3c3a7087dc233ea.

## Verdict

Accepted at coordinating hand-proof scope for the stated coefficientwise-bounded, at-most-k-local class, fixed k>=2, beta>0, and fixed admitted positive accuracy. The all-physical-size lower bound is Omega(N^(2k/3)/(log N)^(2k/3)), with constants depending on beta, k and accuracy. It does not close general P1, establish novelty, give an efficient tester or cover bounded-degree/per-site-energy models.

## Checks performed

- The rounded-block estimate retains both the lock cost and the logical-weight penalty. Under the stated m inequalities, g(a)>=4a log(2s) for a>=1. Counting deviations by binom(sm,q) is an upper bound even with the fixed tie rule. The shell partition is exactly one before leakage is added.
- The coefficient l1 bound follows from the physical block averages having coefficient l1 norm one. Reservoir homogenization distributes each logical coefficient across distinct physical supports; no different logical A yields the same support. The same-block lock collision for k=2 is explicitly counted. Constants are removed only as identity terms.
- For the near-plus reservoir, exactly-one-minus subsets supply l*binom(floor(R/2),k-1) odd products. The union bound on changed r-products gives 2rl/R. The stated strength inequality dominates the signal perturbation.
- For even k, the near-minus estimate includes the unfavorable field change, while simultaneous logical spin reversal supplies the exact two-phase partition identity. For odd k, C/B >= R/(4k), together with 8k*S0/R <= gamma*B, gives gamma*C >= 2*S0. This justifies far-phase suppression rather than assuming it.
- Required R grows at most as a constant times s*log(s/eta)^(1/k)+log(s/eta), because S0=O_k(s^k log(s/eta)). Clone overhead dominates at fixed parameters. All physical clone and reservoir spins are counted; zero-Hamiltonian padding supplies all sufficiently large N without assuming monotonicity of the construction sizes.
- Exact equality in the classical null is preserved. The ideal sampling map uses only samples and known uniform randomness, not hidden probabilities or Hamiltonian queries. Diagonal states permit arbitrary quantum processing to be simulated as stochastic postprocessing of the basis strings. Pre-sampling T strings from each source handles adaptive total-copy allocation at a constant-factor sample cost.

## Classical supplier and accuracy margin

Independently retrieved Chan, Diakonikolas, G. Valiant and P. Valiant, Theorem 1.1, PDF page 2, on 16 October 2026: https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf . It gives the established two-unknown equality-versus-L1-separation complexity max{D^(2/3)/epsilon^(4/3),sqrt(D)/epsilon^2}. Applying it at separation 2epsilon changes constants only. The candidate imports this lower bound; it does not originate that testing theorem.

For clarity, the candidate's separation margin follows from L>=sqrt(D)/epsilon^2 and eta=1/(100L): 4eta<=epsilon^2/(25sqrt(D))<=epsilon/2 in the stated range. A T<=L hybrid changes transcript total variation by at most 1/100; constant amplification of the tester restores the supplier's standard success threshold at constant overhead. For T>L the asserted lower bound is immediate.

## Limits and provenance

The prior shell18 and all-size padding19 remain credited in the candidate. This review accepts the higher-order reservoir extension relative to that stated scientific experiment. Historical priority of this encoding remains unreviewed. There is no new Lean compilation, Rust implementation, physical preparation, empirical validation or proof of optimality. P1 and the separate P5 fixed-support infinite-Redfield obligation remain open.
