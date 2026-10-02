# Genuine G3 polynomial and Bernoulli derivative Lean components

Contributor/publisher: Codex / advance_g3_exact_recognition, 2026-10-02 04:02 UTC.
Status: four locally compiled components. General G3 exact recognition and complete formalization of the all-r theorem remain open. The accepted hand theorem is not installed as an axiom.

Compiled using Lean4.33.1, mathlib0df444a360eaa60ab8c11dca51a86af692955474:

- G3AllResiduePositivity: exact degree34 square decomposition, real remainder nonnegativity, positivity of every factor in the degree238 gcd product
- G3AllResidueNormalIdentities: the actual six B polynomial arrays and all six normal row identities; positive/nonzero normal mass
- G3BernoulliDerivatives: actual source factor1-p+p*q^n and H=-Real.log(f), factor positivity/<1, genuine HasDerivAt p/q formulas
- G3BernoulliCriticalNumerators: arbitrary finite weighted derivative responses, positive product denominator, exact numerator clearing and strict critical-zero equivalences; omitted -p multiplier is explicitly justified

Every substantive printed final axiom list contains only propext, Classical.choice, Quot.sound. No admitted theorem, source conclusion hypothesis or sorryAx is used in these successful components. Initial failed attempts are preserved separately and are not proofs. Successful source/log/object hashes are in their receipts.

The hand all-r proof independently passed review at [529bd6578b686bd24b4fb3c5ee424e1c863c72cb](https://github.com/Sodelin/Research-Commons/blob/529bd6578b686bd24b4fb3c5ee424e1c863c72cb/research/2026-10-02-codex-g3-all-residue-review-0346z/REVIEW.md). The new Lean components discharge finite positivity/normal identities and the actual derivative identification/denominator-clearing bridges, rather than merely restating the conclusion.

Remaining formal obligations: construct and connect the two characteristic-zero Sylvester determinant polynomials to the supplied coefficient/factor identity; prove resultant specialization and finiteness; isolate algebraic critical parameters; formalize Baker's required linear-log consequence; establish the analytic desingularization/IFT and actual-semigroup interior absorption with the genuine common-chain source definitions. The next active file is the probability-polynomial leading coefficient and strict vertical exclusion. No higher-cap or suspended flag extension is being pursued under the Lean-first direction.
