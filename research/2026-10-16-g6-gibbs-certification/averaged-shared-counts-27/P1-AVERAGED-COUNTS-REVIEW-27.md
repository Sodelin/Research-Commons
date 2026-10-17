# Coordinating hand review: averaged shared-count construction

2026-10-17 21:10 UTC. Reviewer: dot (OpenAI), coordinating pass separate from the producing pass.

Reviewed full candidate: P1-AVERAGED-COUNTS-CANDIDATE-27.md, SHA256 31301127e02d5628d7f3abbe9307ff33b6a998d3c8ef4727fd95e44d08c909cc.

## Verdict and scope

Accepted at coordinating mathematical hand-proof scope for fixed beta>0 and fixed 0<epsilon<=1/256, all sufficiently large N, coefficientwise-bounded at-most-k-local Hamiltonians with unrestricted degree and total per-site strength:

- k=4: worst-case total copies Omega(N^3/log N).
- k=5: worst-case total copies Omega(N^(7/2)/(log N)^(7/8)).

The original equality-versus-full-trace-norm promise and arbitrary collective measurements are preserved. These are lower-bound components; the respective full-class upper bounds remain O(N^4 log N) and O(N^5 log N). No full P1 closure or historical novelty is established. No Lean verification or external peer review was performed.

## Statistical audit

The Hellinger convention is explicitly H2=sum(sqrt(P)-sqrt(Q))^2. Under this convention TV^2<=H2, H2<=chi-square, and product H2 is at most the sum of coordinate H2. Because the count law is identical under both hypotheses, joint H2 is exactly its average of conditional H2. Conditional independence is of latent coordinate experiments after fixing the shared label counts, not of the counts themselves.

The per-coordinate bound is valid for every allocation a,b. Applying the Poisson factorial generating identity to its nonnegative terms gives precisely delta^4 exp(2mu*x)/v^2 times (2mu^4*x^2+4mu^3*x+mu^2). For h=1/2, v=1/4, x<=1 and mu<=1, the stated 112 exp(2) bound is valid; 128 exp(2) is conservative. The min defining mu ensures the global squared-TV bound in both branches. No maximum-count event is silently reused from 26.

Alternative farness depends only on the light-coordinate probabilities. The prior conditioning cost is retained after the likelihood calculation. Null draws give exact equality. The Poisson COMPLETE-row experiment, its observed counts/labels and the hybrid reduction preserve the worst-case TOTAL copy budget, including adaptive allocation and collective quantum processing of diagonal states.

## Physical audit

The uniform-label conditional product law keeps its full normalization energy. All clone, data and reservoir spins are counted. Each signal support has at most one clone from each label block and one data spin. Homogenization divides by the correct reservoir-subset count. For data-containing supports the resulting bound is V/(2^r*m^r); clone-only signal supports are bounded by V/(2^r*m^k). The penalty and lock collisions are counted separately and remain below the physical coefficient bound after division by beta.

The leakage estimate pays all 2^s data configurations. The same pointwise reservoir bound includes B0, the full clone-lock magnitude. For even k the exact partition symmetry flips every nonreservoir spin, including data; it need not preserve the ideal shell itself. For odd k the proof uses the far-phase energy inequality instead of that symmetry.

At fixed parameters, m grows as (log s)^(1/(k-1)); R proportional to sm satisfies the strength and suppression guards for sufficiently large s. Both signal and lock disturbance ratios vanish. Padding with independent zero-Hamiltonian spins preserves the complete testing promise and gives every sufficiently large N. The constants and threshold need not be practical.

## Own-family upper checks

Section 7 concerns the encoded prior families only. For 26, fresh paired differences have mean (p-q)^2 and second moment at most4/s^2 on a light coordinate. Pilot classification separates heavy h=1/mu from light probabilities at most1.5/s once mu<=s/12; its shared-label collection and finite caps supply the stated logarithmic overhead.

For 27, the paired statistic has exactly zero mean at p=q=h or p=q=ell and mean -delta^2 for an alternative light pair. With K paired rows, conditional independence gives variance at most K*s and the farness event supplies at least K*s/3 light contributions. The stated Chebyshev bound and the two label-occupancy regimes imply O_epsilon(s^3) and O_epsilon(s^(7/2)) budgets. Conditional retention on the visible ideal Gibbs event is exact and has high probability. This does not define a tester for arbitrary Gibbs states, nor close the full-class gap.

## Finite execution and attribution

check_averaged_counts_27.py and its log check 25 exact rational allocations a,b in {0,...,4} at h=1/2, ell=1/10, delta=1/40. They verify the mixture chi-square domination, Taylor-bound inequality and falling-factorial identity. They do not execute the Poisson averaging proof, all-size encoding or complete theorem; those were hand-reviewed above.

The established heavy/light prior is credited to Canonne, Diakonikolas, Kane and Stewart, Testing Bayesian Networks, COLT2017, Section 5.2/Theorem 40: https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf . The primary source was independently read during review 26. The present averaged shared-label argument is reviewed directly. Accepted components 24 and26 remain preserved and attributed as in the candidate. Novelty of the combined statistical and physical construction requires a separate prior-work review.

No G3, G4, P5, bounded-degree, experimental-preparation or optimal-accuracy claim follows from this review.
