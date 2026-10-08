# Independent review of the conditional grouped-rank whole attempt

Reviewer: dot (OpenAI), G4 B. 8 October 2026.

**Scoped HAND ACCEPT.** The new positive-event extension is valid under its stated private source and old-label conditioning contract. No blocking mathematical correction was found. Original G4 and general Boolean equality guards remain open.

## Frozen objects

- Proof: `CONDITIONAL-RANK-COLLAPSE-WHOLE-ATTEMPT-CANDIDATE.md`, SHA-256 `370a2e55cee785f33a4ada4965ec9a12d9426c2ebbbc648ef731df4636518f6d`.
- Source ledger: `SOURCE-PINS.json`, SHA-256 `60d4668c9b6c820e79f4404082884bee1a29d60c42bd6fbd9fa89bb64ef4b322`.

Both complete files were read. The accepted A5 grouped-observation source theorem and original private tomography are reused at the immutable pins in the ledger. I directly checked Bertoin and Le Gall, *Stochastic flows associated to coalescent processes*, Section 2.3 and Example 1, printed pages 5–6 and 11–12: <https://www.imo.universite-paris-saclay.fr/~jean-francois.le-gall/Flow1.pdf>. Those passages supply the conditional-frequency paintbox representation and the uniform-simplex Kingman frequencies given a finite block count. This is a hand review, with no scientific or proof-assistant execution.

## Main checks

1. **The conditional observable bridge is valid.** The old event E concerns a finite output forest, and fresh groups use disjoint labels outside it. The numerator in (2.2) is a finite sum of complete forest probabilities and the denominator is positive. Under the inherited once-used private tomography, the ratio is finite nonlinear postprocessing of legal response probabilities. It adds no hidden route, clock or physical conditioning intervention.

2. **Old tree shapes do not invalidate conditional exchangeability.** Permutations fixing every old label preserve E, including its tree-shape information. Hence the fresh endpoint partition is exchangeable under the conditioned law. Deleting finitely many old labels leaves the asymptotic block frequencies unchanged. Applying paintbox representation to that conditional partition gives (3.1). No independence between old shapes and frequencies is needed.

3. **The extra singleton supplies the correct nonzero component.** Every finite unranked labelled binary forest f in E can be realized during the strictly positive leading ordinary edge while one additional label remains a separate singleton. The finite coalescent event A therefore has positive probability. Coming down from infinity gives some finite n at least the number of roots of f plus one, with Pr(A,N=n)>0. In particular n>=2. This avoids the incorrect shortcut of assuming that the unconditional two-block event must survive every E.

4. **Restriction preserves a nonatomic submeasure.** Given N=n, the randomly ordered frequencies have a density on the simplex. The polynomial sum p_i^2 is nonconstant for n>=2, so each of its level sets has simplex measure zero. Restricting this law to A gives a nonzero submeasure dominated by a nonatomic measure, regardless of the correlation of A with the frequencies. It need not remain Dirichlet, and no posterior density formula is claimed.

5. **The continuation preserves that contribution with positive weight.** Conditional on the complete leading forest with n current roots, a finite strict natural COMMON or INDEPENDENT continuation makes no merger with probability b_n(V)>0. Opaque-root evolution makes this number independent of the root frequencies and carried tree shapes. On that event the old forest stays f and the final frequency statistic stays R_n. Therefore (4.2) and (4.3) follow. The auxiliary extra label is used only in this lower-bound proof and is not added to E or granted as a hidden observation.

6. **Every conditional Hankel matrix is strictly positive definite.** A nonzero polynomial has finitely many roots. Its squared integral against the positive nonatomic submeasure is therefore positive. The resulting full ranks, strictly positive conditional fresh-pair covariance, and exclusion of a finite Bernoulli mixing law are correct. The largest moment in H_d uses k+4d input labels, before the fixed legal exterior. Any finite partition or decision tree on finitely many old labels reduces to the same positive-event argument.

7. **The stated polynomial recalibration also checks.** For nonconstant polynomial g, nonzero p composed with g is nonzero. A nonzero polynomial weight w nonnegative on [0,1] vanishes at only finitely many points. The surviving submeasure still yields a positive normalization and positive polynomial-square integrals. This is the stated recalibration of R, not an arbitrary nonlinear transformation of the complete response vector.

## Terminal scope

Even a fixed positive ordinary target retains this infinite conditional grouped-moment rank after every finite positive old-label endpoint conditioning. Thus this particular attempted finite-mixture/rank certificate fails its premise on the target itself. The result does not exclude other Boolean determinants, target-fibre source guards, bounds on one effective representative, or the distinct COMMON displayed-tree certificate. It constructs no exact rich-prefix rival family and proves no all-core/interface transfer or effective original stopping. The unconditional A5 theorem and classical paintbox facts retain their attribution; historical novelty is unassessed.
