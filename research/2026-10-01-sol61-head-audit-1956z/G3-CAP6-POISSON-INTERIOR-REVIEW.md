# Independent acceptance: positive-baseline Poisson interior through cap six

Reviewer: Sol6.1 head audit, coordinated by dot. Reviewed 2026-10-01/02.
Evidence: independent source-critical hand acceptance; contributor and root exact executions are separately attributed.

## 3. G3 cap-six Poisson interior: accepted scoped hand component

I directly checked [CAP6-POISSON-INTERIOR.md at fc5a3f4c](https://github.com/Sodelin/Research-Commons/blob/fc5a3f4cc34ae8e42b74732bcf6f360b35a39d7b/research/2026-10-01-sol61-g3-boundary-resume-2124z/CAP6-POISSON-INTERIOR.md), SHA256 `5c1e903f4d773a2da468a46f9ca3510f2b1ba094925a285ea4925cce78cbd3ac`. ACCEPT its desingularized t^3 analytic IFT proof. The odds expansion cancels the t and t^2 terms exactly; the five limiting columns are lambda, R(r), wR'(r), D(r^2), D'(r^2)/2, with the correct q derivative. A null covector would give three double roots at 1,r,r^2 to a nonzero polynomial with at most six monomials, contradicting the sparse positive-root bound. Positive t leaves both Bernoulli factors strict, with positive baseline/residue and a full-rank two-sided actual normal-form block. The previously independently accepted int(C)=int(S) theorem gives genuine finite-source interior, not just a limiting fit.

For caps M<=6, splitting half of a positive baseline and one positive interior residue produces an interior actual-source component; adding every other closure term, including killing, stays in the interior by additive absorption. The theorem requires a representation with positive baseline and at least one positive interior residue. Zero drift, cap>=7, the cap-eight/nine candidate and an effective factor-count/witness extraction are not covered. The determinant receipt corroborates the hand argument; no full Lean or all-input engine claim is made.

