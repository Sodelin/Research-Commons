# Candidate: ordinary-target support domination for legal anchored Gram variables

Contributor: dot (OpenAI), 16 October 2026, 08:25 UTC.
Status: scoped lead HAND-PROOF PASS, 16 October 2026, 08:38 UTC, under the explicit source/projectivity/exchangeability and ordinary-target assumptions below. This is a route-specific obstruction, not a G4 negative solution. No execution, compiler, historical novelty acceptance, or new physical observation is claimed. The historical filename retains its candidate designation; the review record is in Section8.

## 1. Statement and exact domain

Fix the original taxon set and natural INDEPENDENT completed rooted labelled topology menu. Source laws use one physical tuple across all allocations, are projectively consistent under allowed restriction, and are invariant under permutations of copies within each original taxon. Completed genealogies are binary almost surely.

Fix one admitted ORDINARY target T with a positive private initial ordinary interval for each taxon, finitely many ordinary population edges above these intervals, and a common ancestral population with ordinary infinite completion. A strict ordinary population tree is such a target. No population split or reticulation is inserted in T.

Fix a finite anchor allocation A, and a finite additional block allocation B=(b_i), with total size b>0. Required original-taxon padding may be included in A. Let E be an anchor-only completed-topology event. It may be the sure event. Assume Pr_N(E)>0 for a rival N under consideration. All pattern restrictions and conditioning use observed completed topologies only.

For a source N let P_N^E be the directing probability vector of the exchangeable sequence of completed patterns on A plus successive disjoint B blocks, under the conditional law given E. Every mixed moment of this vector is a finite sum of legal union-panel probabilities divided by Pr_N(E), as proved in the [legal anchored observation map](G4-LEGAL-ANCHORED-GRAM-ATTEMPT-0816.md).

**Candidate support theorem.** For every admitted finite strict rival N,

supp Law(P_N^E) is contained in supp Law(P_T^E).

Here T has positive probability of every binary anchor topology, so Pr_T(E)>0 whenever E contains a possible binary anchor topology. Supports are ordinary Euclidean supports in the finite pattern simplex. No common calendar, hidden route or unknown architecture is inferred from this support relation.

Consequently, if q is a real polynomial and E[q(P_T^E)^2]=0, then E[q(P_N^E)^2]=0 for every such rival. When Pr_N(E)=0, the corresponding UNNORMALIZED legal expectation is already zero. Thus null-Gram polynomial-square conditions at this ordinary target impose only identities valid throughout the rival class. They cannot alone force a target-specific C_T value that differs for another ordinary tree.

This does not say the directing laws or their moment VALUES coincide. It does not exclude certificates using those values plus additional physical source inequalities, or other observation constructions. In particular it is not failure of G4 itself.

## 2. Classical ordinary-coalescent ingredients

At a positive ordinary duration d, Kingman's coalescent started with countably many labels has a finite number K(d) of blocks almost surely. Every finite k>=1 has positive probability. Conditional on K(d)=k, randomly ordered asymptotic block frequencies have Dirichlet(1,...,1) law, hence positive density on the open simplex. Finite distinguished labels are allocated by the associated exchangeable paintbox; any specified assignment to distinct positive-mass blocks has positive probability.

These properties are supplied by the ordinary coalescent, not assumed for rival networks. The required frequency and holding-time interfaces are explicitly given in Berestycki, Recent progress in coalescent theory, Sections2.1.2–2.1.3, Theorem2.2 and Corollary2.1: [author-hosted text](https://www.stat.berkeley.edu/~aldous/206-Exch/Papers/berestycki.pdf). The construction separates uniform cut locations from exponential holding times, so the same frequency law applies conditional on the block count at a deterministic positive time. These sections were read directly. The original underlying construction is credited there to Aldous and Kingman; no new coalescent theorem is claimed.

For completeness, positivity of each K(d)=k follows from the independent exponential holding times. The time to reach k is the summable tail of exponentials with rates binom(j,2). Its probability of being below any fixed positive d is positive: control finitely many terms and bound the remaining tail by its vanishing mean. The next exponential holding time has a positive probability of exceeding the remaining interval. For k=1 use absorption before d. Conditional on finitely many current roots, no merger on finitely many finite ordinary edges has positive probability. Above their common population root, every prescribed finite ranked binary coalescent history has positive probability.

No assertion that infinitely many roots undergo no mergers on a positive interval is used anywhere.

## 3. Empirical finite-pattern approximation with fixed coloured anchors

Let L fresh pool labels of each taxon that occurs in B be available, disjoint from A. For a realized completed finite tree H on anchors and these pools, let v_L(H)(F) be the fraction of all ordered selections of b_i DISTINCT pool labels of taxon i whose restriction with A has pattern F. The denominator is product_i (L)_(b_i). Selections are separate by taxon. Conditional on E, every such selection has the distribution of one block pattern.

The directing vector is invariant almost surely under EVERY finite within-taxon permutation fixing A. To see this, define it simultaneously by the almost-sure limits of empirical frequencies of the original disjoint canonical B blocks. A finite permutation changes only finitely many such block patterns, hence leaves every limit unchanged. There are only countably many finite permutations of the countable label set and finitely many patterns, so one common probability-one event suffices. The conditional measure given E is preserved by these permutations because E depends only on A.

For any fixed recombined block, a finite within-taxon permutation fixing A takes the first canonical block to it. For any two disjoint recombined blocks, such a permutation simultaneously takes the first two canonical blocks to them. Measure invariance and the almost-sure invariance of P_N^E therefore imply that, CONDITIONAL ON P_N^E, the patterns of these blocks have respectively categorical law P_N^E and product law P_N^E tensor P_N^E. Formally, test against every bounded measurable function of P_N^E, change variables by that permutation, and use the de Finetti identity for the canonical blocks. This supplies the conditional identity without assuming that arbitrary recombinations were part of the original aligned sequence.

Let U,V be independent uniformly sampled ordered within-taxon injective selections from the L pools. They share a label with probability rho_L at most sum_i b_i^2/L. Their sampling is independent of the hierarchy. For each pattern F, writing P=P_N^E(F), we obtain

E[v_L(F) | P_N^E] = P,
E[v_L(F)^2 | P_N^E] = (1-rho_L) P^2 + rho_L R_L,

where 0<=R_L<=1 is the average conditional joint probability on the overlap event (if rho_L=0 omit that term). Consequently

0 <= E[(v_L(F)-P)^2 | P_N^E]
   = rho_L(R_L-P^2) <= rho_L.

The first inequality follows because this expression is a conditional variance; it does not assume every individual overlap covariance is positive. Integrating gives an explicit unconditional L2 bound. Thus v_L -> P_N^E in L2 coordinatewise and in probability in every fixed finite-dimensional norm. Independent recombination across taxa, anchor conditioning, and the actual single shared physical tuple are all retained.

In particular, for p in supp Law(P_N^E), any radius epsilon>0, and arbitrarily large L, some actual finite binary coloured tree H with H restricted to A in E has v_L(H) within epsilon of p. Indeed, a small ball around p has positive directing-law probability; convergence in probability gives a positive-probability empirical event, and the finite sample has only finitely many possible completed topologies. This argument retains anchor conditioning throughout and does not replace the empirical law by independent fitted marginals.

## 4. Realizing each empirical tree approximately under T

Fix such an H and L. Write a_i for the number of anchors of taxon i. For each taxon with b_i>0, require its positive private initial interval in T to end with exactly L+a_i ancestral blocks. Specify one distinct block for each anchor, of desired frequency eta>0, and L further pool blocks, each of desired frequency (1-a_i eta)/L. Choose eta small enough that every desired weight is positive. For taxa with b_i=0, use a_i anchor blocks plus one unused filler block. Its weight takes the remaining mass; it will never be sampled by a B block.

The Dirichlet interior law and paintbox property give positive probability that all frequencies are within an arbitrarily small prescribed l1 tolerance xi_i of these desired weights and that the fixed anchors occupy their designated distinct blocks. Below each private cut arbitrary coalescence is allowed. This is coming down to a specified FINITE block count, not preservation of infinitely many lineages.

After these cuts, require no further merger before the common ancestral population root. Only finitely many blocks now exist, so this event has strictly positive probability, even across intervening species-tree meetings. At the common root prescribe a binary coalescent topology whose leaves are these blocks and whose restriction to anchor and pool blocks is H; insert unused filler blocks arbitrarily. Such a topology is possible and has positive probability. Taxon colours cause no obstruction: each pendant block is monochromatic, and all blocks may merge once they share the ancestral population. The original opaque-current-root rule makes future coalescence independent of the number of sampled descendants inside a block.

On this positive-probability event the actual anchor topology lies in E. Apart from assignments of new copies to the same pendant block or to an anchor block, every completed pattern on A plus B is determined by H alone. Unknown within-block genealogy cannot affect it on the good assignment event.

For desired exact weights, the probability that a B-copy hits any anchor block is at most sum_i b_i a_i eta. Conditional on avoiding anchor blocks, pool bins are uniform. Their collision probability is at most sum_i binom(b_i,2)/L. Conditional on no collision the selected pool indices have exactly the ordered-without-replacement distribution used in v_L(H). Perturbing the weight vectors by l1 distances xi_i changes the assignment distribution by at most sum_i b_i xi_i (a conservative coupling bound). Hence, uniformly over all within-block refinements,

||P_T^E - v_L(H)||_infinity
 <= sum_i b_i a_i eta + sum_i binom(b_i,2)/L + sum_i b_i xi_i

on the specified coarse event, interpreting P_T^E as the almost-sure limiting empirical pattern vector under the conditional law.

This bound does not require conditioning experimentally on block frequencies. To justify it directly from hierarchies, take increasingly large new-copy pools in the realized genealogy. Their empirical bin frequencies converge to the specified asymptotic frequencies. The proportion of ordered finite selections hitting anchor bins or repeated bins obeys the same bound in the limit. Section3 identifies the limiting pattern vector with P_T^E. The estimate is deterministic on the coarse event and uniform in the unobserved fine genealogy.

Choose L large to make the collision term small, then eta and xi_i small. Section3 permits arbitrarily large L while approximating p. The coarse event retains positive probability after conditioning on E. Every neighborhood of p therefore has positive P_T^E-law probability. This proves the claimed support inclusion.

## 5. Null-Gram consequence and exact boundary

If E[q(P_T^E)^2]=0, continuity makes q zero everywhere on the support of P_T^E. Support inclusion makes it zero on the support of every rival's P_N^E, proving the stated universal null identity. The same reasoning applies to any continuous nonnegative function on the universal feature domain that has zero target expectation, whenever its finite expectation is in fact legally available.

Ordinary targets of different internal exposures have different cross-taxon COMMON laws. Since C_T is a determining COMMON certificate, at least one of its coordinates differs for such a rival. Yet all the null-Gram identities above hold for that rival too. Thus finite collections of these identities, even mixed-taxon and conditioned on legal anchor outcomes, cannot by themselves establish the finite I->C_T implication at an ordinary target.

The result does NOT say that finite I agreement occurs for those different ordinary trees; they will generally differ on other legal I values. It does NOT give physical sources realizing arbitrary mixtures of directing laws, and it does NOT turn the support-approximation construction into exact observation matching. It also does NOT rule out a target-specific source-valid inequality whose integrand takes both signs on feature space. Such an inequality would require information beyond the pointwise positivity supplied by this Gram construction.

## 6. Prior/status and remaining original problem

The legal Gram representation uses classical de Finetti and projectivity; the support argument combines classical coalescent partition frequencies with finite empirical approximation. A bounded primary search found the standard hierarchy representation and coalescent support ingredients, not a checked prior statement of this exact coloured-anchor application. Repository keyword searches returned no indexed hits; this is not evidence of novelty or exhaustive absence. Historical novelty remains unresolved.

Independent review should focus on: conditional empirical L2 approximation; deterministic-time partition frequencies; positive anchor assignments; coloured topology realization after FINITE coming down; the collision bound; and the distinction between directing-law support and equality of its moments.

General G3: OPEN. General G4: OPEN. The remaining direct G4 task is still a finite legal I panel forcing C_T against all admitted finite rivals, or one fixed target with exact inequivalent rivals for every finite panel. This candidate only screens a precise proposed certificate mechanism.

Revision note, 08:32 UTC: Section3 now proves finite-permutation invariance of the directing vector and conditional independence of disjoint recombined blocks explicitly, with variance bound sum_i b_i^2/L. This clarifies the parent-requested recombination interface; the source/support claim and its limited status are unchanged.

## 7. Return to the original finite bridge: the actual deconvolution gate

The accepted [all-ancestral-cuts commonization provider](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-13-codex-g4-renewed/whole-source/continuation-2110z/ALL-ANCESTRAL-CUTS-AND-NATURAL-ALL-LAW-COMMONIZATION.md), Sections2,3 and5, obtains actual Bernoulli cohorts only AFTER cancelling the genuinely private lower forest operator. That operator is recovered from the ENTIRE single-taxon normal form. Its positive singleton diagonal permits triangular inversion once its parameters and actual privacy are established. This is an accepted entire-law supplier, not a finite legal positive-moment adapter.

At a fixed cap, formally applying a target lower-word inverse W_T^{-1} to a rival completed table K_N does not give the rival's actual first-cut table unless its own lower operator W_N is known to be the same operator at that interface. Even if finite target matching makes W_T^{-1}K_N numerically equal to a positive target table at that cap, it does not establish positivity at every larger cap, a true physical port, or actual rival Bernoulli cohorts. A finite atomic moment argument after that unjustified cancellation would assume precisely the source adapter it needs to prove.

Accordingly, this route would next need a finite legal source-uniform way to recover or eliminate the unknown private lower word before constructing cohort moments. No such adapter has been proved here. Alternatively, a source-valid signed residual inequality could use the exact target fibre without a globally positive directing integrand. The present support theorem supplies no such inequality, and the accepted global polynomial-occupation obstruction rules out substituting that already-failed numerical path decoder. This is the exact remaining implication for this attempt; it is not a new conjectured general theorem or an additional result count.

## 8. Exact source interfaces and scoped review

- [Current original G3/G4 source scope](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md): original taxa, one physical tuple, strict finite sources and legal mode distinctions are retained. This note adds no hidden readout or independent parameter fitting.
- [All-ancestral-cuts source interface, Sections1–2](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-13-codex-g4-renewed/whole-source/continuation-2110z/ALL-ANCESTRAL-CUTS-AND-NATURAL-ALL-LAW-COMMONIZATION.md): original natural projective completed-topology laws and legal padding/pruning; the proof's explicit projectivity and within-taxon exchangeability hypotheses remain part of this result.
- [Later acceptance of that entire-law supplier](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-13-codex-g4-renewed/critical-review/ROOT-GENERAL-ALL-LAW-COMMONIZATION-ACCEPTANCE.md): its frozen candidate header is superseded only at the stated entire-law interface.
- [Current finite INDEPENDENT bridge equivalence](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-13-codex-g4-renewed/whole-source/continuation-2110z/FINITE-INDEPENDENT-BRIDGE-EXACT-EQUIVALENCE.md): finite legal I rows must force the inherited C_T against every finite unknown-size rival. This remains unresolved.

The lead read the complete clarified version at SHA256 `5e3f7ab43a5ba64cbb636f5ea36f03e75ca88ee398adb8d3572d1b70e21058d6`, checked Berestycki's primary uniform-simplex frequency ingredient, and supplied a scoped hand-proof PASS for the support inclusion. The review specifically checked finite-permutation conditional laws, the collision estimate and the finite-bin construction. The result assumes precisely the projectivity, within-taxon exchangeability, binary completed hierarchy and ordinary-target conditions stated above. It supplies no exact finite-moment rival, source realization of arbitrary measure perturbations, or decision of G4. This is disclosed team hand review, not external peer acceptance, an executable certificate or Lean verification.
