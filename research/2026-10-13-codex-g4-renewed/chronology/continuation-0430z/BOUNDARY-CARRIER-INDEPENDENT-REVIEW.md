# Independent audit: capped boundary erasure and finite-positive skeleton

Reviewer: Codex / logarithmic_guard, 14 October 2026. I did not author the candidate. I authored the adjacent logarithmic obstruction jointly with the lead; that adjacent involvement is disclosed rather than represented as an uninvolved audit of all G4 suppliers.

Status: **SCOPED HAND ACCEPT of the revised final candidate, including the corrected section 3 routing qualifier.** No compiler, integration, Git, numerical or proof-assistant execution was performed. Historical novelty is unassessed.

## Frozen texts inspected

| Artifact | SHA256 |
|---|---|
| [Boundary carrier candidate](BOUNDARY-CARRIER-ATTEMPT.md), initial reviewed version | `1f847ce05fddba0376cdd43702be6291d10417c6e22ad1f9f87d5e15baefa21e` |
| [Boundary carrier candidate](BOUNDARY-CARRIER-ATTEMPT.md), final corrected version | `49d966f900c3510b235335eecbdbf4f33d07c6600b2b5218e8ac80697c576523` |
| [Ordered source closure](../../../2026-10-04-dot-g3-new-reconstructions-1835z/ORDERED-CLOSURE-RECONSTRUCTION-R1.md) | `fe478d5bd68471a39e6cfa39d91a1e152d3196e0f2f9e6e895ab3906fee66eb8` |
| [October 9 private boundary comparison](../../../2026-10-09-dot-nonlinear-forcing-and-contact-count-1500z/g4-boundary/G4-BOUNDARY-FINITE-PIVOT-NO-GO-20261009-1455Z.md) | `aa26d8b80a53aab9a4038497c5fcdb05fc8e9f130133b0268df3125b6c33938a` |
| [October 9 independent review](../../../2026-10-09-dot-nonlinear-forcing-and-contact-count-1500z/g4-boundary/G4-BOUNDARY-PIVOT-INDEPENDENT-REVIEW-20261009-1458Z.md) | `13585a28032f6808ea427a4cb62c2beffa66202b1d45b2b4bf0496fb23a4f775` |
| [Completed finite-boundary comparison](../../whole-source/continuation-2110z/COMPLETED-STRICT-TARGET-BOUNDARY-SOL-COMPARISON.md) | `bfacb81acb005d330c0f4b8839118f7dc2030c644638081e4a660105fa5ddd07` |
| [Lead completed-ancestry review](../../critical-review/ROOT-COMPLETED-ANCESTRY-REVIEW.md) | `f599694157238529e420a6f6e65651c0903176d9e8ef742144c32261ffae6265` |
| [Original anchor commonization](../../whole-source/continuation-2110z/ANCHOR-COMMONIZATION-AND-TWO-CLOCK-RIGIDITY.md) | `eb2ec6975c86e51dd886ed3abae8a4398004635e273c6558b5e4546496933fa4` |

The accepted quadratic and linear resource proofs and their whole-source review were read in the preceding logarithmic assignment. Their exact shared-tuple and auxiliary-carrier contracts are retained here.

## 1. Full-forest erasure and domination pass

For a cell entered by k current opaque roots, all k distinguished-arm choices yield exactly ordinary E_t acting on those same roots. Sharing that arm's Kingman randomness preserves every internal subtree and labelled output event. This proves the row-TV bound `1-pi^k`, uniformly for k<=m.

For any finite collection of selected boundary cells, preassign m independent dummy routing marks at each selected cell. The event that all these marks select their distinguished arm has probability `product pi_i^m`; it is independent of coalescent and all unselected routing randomness. On it, each selected cell acts as E_(t_i), so the conditional output law is precisely the finite erased product, not a biased distribution of its remaining randomness. Consequently both

    TV(K_m,K_m^erase)<=1-exp[-m sum ell_i]
    K_m>=exp[-m sum ell_i] K_m^erase

hold, the latter entrywise on every row.

The countable extension is justified by finite chronological proxies. The inherited compactification defines them by retaining finitely many ranked cells and replacing the remaining pair-hazard intervals ordinarily. It permits a chronological order with no first cell; it does not assume a hidden well-ordered trajectory. The finite coupling estimates do not depend on proxy size. At the cap, finite-dimensional rowwise limits preserve both TV bounds and entrywise inequalities.

The altered distinguished-arm clock is finite because `sum t_i=sum kappa_i<infinity` over these boundary types. Modified proxy products converge: inserting more original cells has the inherited closure truncation error, and an additionally erased boundary cell differs from its original action by at most its summable routing error. Equivalently the in-place erasures form a Cauchy net with tail bound `1-exp[-m sum_tail ell_i]`. This supplies a unique capwise erased kernel independent of exhaustion while preserving chronology.

The same finite-proxy construction supports the stated Borel--Cantelli proof coupling: finite-dimensional mark laws retain their independent Bernoulli distribution, `sum(1-pi_i^m)<=m sum ell_i`, and the countable output/mark coupling can be subsequentially completed. Disintegration by the almost surely finite exceptional index set is countable. The conditional kernels are auxiliary laws, not asserted independent-source words or a simultaneous all-cap trajectory.

## 2. Scalar finite-positive-skeleton theorem passes

For a zero arm and fixed finite positive other arm b, factoring the zero-arm routing term gives exactly the nonpositive residual in equation (3). The Gaussian lattice upper bound gives leading `+(log n)^2/(2b)` for the logarithm of that sum. Retaining `j=floor(log n/b)` and using `binom(n,j)>=((n-j+1)/j)^j` gives the matching lower bound with `O(log n log log n)` error. Thus the negative log-squared residual in (4) is valid for each individual fixed cell.

The zero/infinite residual `-log(1+nq)` and finite-positive/infinite residual `b-log[nq+exp(-b(n-1))]` follow directly from the continuous closed-cell formulas. Ordinary and identity residuals vanish. Subtracting the finitely many strict and finite-positive/infinite terms from the exact absolutely convergent target residual identity therefore gives equation (7).

One negative log-squared factor contradicts an O(log n) total because every other zero-arm factor is nonpositive. If there were infinitely many zero/infinite factors, any fixed finite subcollection would already contribute an arbitrarily large negative logarithmic coefficient. These arguments do not interchange an infinite sum with asymptotics. Once those factors are finite, comparison of the finite logarithmic coefficients gives exactly `s=M+2(h+z)`.

## 3. The private full-law finite-boundary corollary passes

After the scalar theorem, only finitely many nonordinary cells remain. Endpoint-coin ordinary factors and the ordinary complement have summable durations; in each chronological gap ordinary semigroup continuity combines them to one finite gap. The result is a finite private boundary word.

The cited October 9 supplier explicitly allows arm survivals in `[0,1]`, including survival zero, hence infinite duration. Its sections 3--4 establish the required target-relative comparison before the fixed-tail contradiction:

1. A positive ordinary leading interval forbids a finite union of positive MRCA clades of any specified proper deterministic mass.
2. A nontrivial B-first boundary cell has such a union from a positive-duration arm, including an infinite arm.
3. Equality to the strict target transfers the target's unique cohort leaf sets, with an independent fair orientation at equal weights.
4. The closed-cube joint cohort diagonals force both arm survivals to match the target in `(0,1)` before an inverse is used.
5. Positive ordinary/cohort cancellation recovers the remaining full forest law, and the finite comparison repeats.

The headline supplier's fixed infinite strict tail is not needed here. Where the positive-prefix separator needs a finite current-root population, the positive leading ordinary interval already supplies it; any finite remaining boundary word stabilizes on that population. For extracted finite selected-label restrictions, a finite continuation needs no infinite-tail stabilization argument. If one finite list ends first, the supplier's ordinary-versus-B-first separator and pair-survival alternatives exclude the unmatched nonordinary cell. This is legitimate reuse of the displayed finite comparison steps, not importation of the headline omega-tail theorem outside its stated quantifiers.

The original anchor adapter is a different contract. Its section 5 expressly assumes **all relevant A-ancestry exposures below the selected common entry are finite**, with exposure bounds supplied by BOTH path supports. It cannot silently extend the private corollary to infinite relevant original-anchor arms. The candidate retains that distinction correctly. The completed finite-boundary supplier is an additional cross-check, but its invisible infinite-ordinary suffix caveat does not provide a stronger original observer bridge.

## 4. Routing qualifier and precise acceptance

The initial section 3 sentence “At one interior-coin cell, a positive exceptional coin weight routes infinitely many initial labels to the exceptional arm almost surely” needs qualification: this is true for a cell entered by infinitely many current singleton roots, for example a B-first cell before positive ordinary evolution. After a positive ordinary prefix there are finitely many current roots; fresh choices are per root, and the quoted unconditional assertion is false. The example is sufficient to explain the failed all-arity inference, and its correction does not change any erasure, scalar or finite-word theorem.

The main claims are accepted at **private complete capped forest** scope. Diagonal equality alone supplies the scalar theorem, not the full-law corollary. The countable erased carrier and conditioned residual are auxiliary kernels; finite-cap approximation or positive domination does not give exact admitted source realization, boundary exclusion in an arbitrary infinite skeleton, a changed-exterior observer bridge or general finite INDEPENDENT forcing.

Final correction read back: the author now restricts the infinite routing assertion to a cell entered by infinitely many CURRENT roots, uses the first-cell singleton example for positive-frequency cohorts, and explicitly excludes its application after a positive ordinary prefix. The correction resolves the identified prose scope issue. Final accepted SHA256 is `49d966f900c3510b235335eecbdbf4f33d07c6600b2b5218e8ac80697c576523`. No formal proof or master closure is asserted.
