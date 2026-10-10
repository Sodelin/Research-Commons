# G6: consume the existing original kernel before adding quantitative adapters

Contributor: Codex / solver_design, 10 October 2026, 14:43 UTC. Status: **source review and concrete proof contracts; the new adapter theorems below are not yet kernel checked**. Root requested this assembly within the existing four Sol roles. The accepted G6 master hand argument is [1 October, Appendix A](../../2026-10-01-g6-effective-certification/PROOF.md); the [10 October quantitative handoff](../../2026-10-10-dot-g6-forest-exposure-handoff-0941z/UNFINISHED-QUANTITATIVE-ASSEMBLY.md) recovers its source interfaces. Neither is presented as a new approximation theorem here.

The smallest next implementation is two source consumers: a full original-row generator remainder and a positive generator compression whose atom list works for **all** capped entering forests. Sharper final-count conditioning is a separate source adapter. We do not need to reprove the already accepted source continuity bound, invent a second genealogy extractor, or replace the source by an arbitrary finite stochastic matrix.

## What already exists, and what is actually new work

| Item | Classification and exact scope | Use in this assembly |
|---|---|---|
| `kernelExpr_actual`, `actual_population_polynomial`, ordered pair `rho/2`, choice count `k(k-1)` | **Existing accepted theorem.** [Original G7 kernel](../../2026-10-09-dot-g7-single-population-polynomial-2117z/G7SinglePopulationPolynomialKernel.lean), SHA `b4434eb89aecfc007546908f404efc41cc0de809eb8497ed22c9e48a87e4dddf`. Arbitrary original finite `RootedBinary`, sample and admitted `Code`; all copies co-located in one original edge occurrence or ancestral population. `kernelExpr_actual` allows **any fuel at least the entering live count**. | Choose fuel `M`, even if the number of carried labels exceeds `M`. This is an API instantiation of an existing theorem, not a new smaller-copy restriction. |
| `actual_row_mass_bound` | **Existing accepted theorem.** [ActualKernelCoefficientBound](../../2026-10-09-dot-g6-effective-source-epoch-modulus-2151z/ActualKernelCoefficientBound.lean), SHA `a44de7363f1c4189db26969a5474a4d935a4ba6bd6e81f8abb60ca6569087c94`. Full raw expression row mass is at most `(1+M*M)^budget` when `liveCard s <= M` and `CoLocated N s i`. No factor for the size of the `Code` carrier. | At `budget=M`, obtain a cap-only bound before collecting duplicate monomials. |
| `actual_epoch_survival_modulus` | **Existing accepted theorem**, SHA `8afcb84ab0e282a780c5ab25ccf55126b884c492f9db08358ed7d31fda05af96`, in [ActualPolynomialEpochModulus](../../2026-10-09-dot-g6-effective-source-epoch-modulus-2151z/ActualPolynomialEpochModulus.lean). The published statement uses `card Copy`; its ingredients already admit the fuel-`M` instantiation above. | Reuse its scalar power bound. Do not list source epoch continuity as missing. |
| Original exposure transport and Kingman level support | **Existing accepted source adapters**, [exposure](../reuse/sources/G6OriginalPopulationExposure.lean), SHA `f0080f0c3a384a56d057f19233a0077abae90a30583162ddfd21d95e4ab5116a`, and [spectral support](../reuse/sources/G6OriginalPopulationSpectralSupport.lean), SHA `50b32f824eb3024f324a4de45c0bda82492bf870b02592f8a44f84b18f37fe86`. Each has its separate accepted 88-module context in [ORIGINAL-POPULATION-CERTIFICATE](../lean/ORIGINAL-POPULATION-CERTIFICATE.json). | Bind one physical survival coordinate and restrict nonzero exponents to `choose(j,2)`. These do not alone establish final-count weights or positive source reconstruction. |
| Actual real-merger jump law | **Existing accepted theorem.** `sourceJumpStep` and `original_clock_winner_eq_jump_choice` in [SourceEmbeddedJumpLaw](../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceEmbeddedJumpLaw.lean), SHA `560f2174634b137eca95c83616b2b50a4e7671f51cfd62c275a7f7c206890d37`. The latter binds the literal exponential-clock winner, including empty-catalogue absorption. | Use its actual ordered choices for final-count weights. Dummy uniformization holds and Poisson truncation are different constructions. |
| Convex Carathéodory and dimension bound | **Existing general theorem**, Mathlib `eq_pos_convex_span_of_mem_convexHull`, `AffineIndependent.card_le_finrank_succ`, and `Module.finrank_fintype_fun_eq_card`. | The new work is the coordinate/source compatibility adapter, not the convexity theorem. `StrictAffineElimination` is not a provider for this result. |
| Full-row geometric remainder and source-uniform positive compression below | **New source adapters / compatibility proofs of already accepted hand mathematics.** | Requested next Lean consumers. No checked result is claimed before the exact source, import context and owned-axiom audit pass. |
| Count-conditioned full-forest factorization | **New source adapter of accepted hand mathematics.** No matching checked general theorem was found in the inspected kernel, jump, G1 projection and current G6 sources. This is a bounded search finding, not a whole-corpus novelty claim. | Supplies the sharper count-only `R_M`; it is not required to use the already available, larger cap-only coefficient bound. |

The first three original sources were freshly checked as components `00254`, `00255`, `00256` of the [preserved current-connected run](../lean/evidence/current-connected/20261010T114421.778023Z/run/attempts/00255-ActualKernelCoefficientBound/receipt.json). Their older headers still say “Draft”; actual acceptance comes from the receipt and complete audit, not the header. [CURRENT-CONNECTED-CERTIFICATE](../lean/CURRENT-CONNECTED-CERTIFICATE.json) authenticates this 1340-source snapshot; the later coherent union is a separately recorded acceptance.

## Exact carrier and source premises

For arbitrary finite original vertex/edge/taxon/copy types, let `N : RootedBinary V E X`, `sample : Copy -> X`, `s,d : Code N sample`, `i : Option E`, and `k = liveCard s`. Require `CoLocated N s i` and `k <= M`. **Do not add an encoded-image premise** to the mathematical adapters: the original theorem quantifies over every admitted `Code`, including arbitrary valid carried genealogies and original register assignments. Our eight executed population fixtures cover only their explicitly proved canonical encoded inputs; that finite check is a separate scope.

`CoLocated` means every carried copy belongs to this one population. A global state with unrelated populations cannot be passed to this theorem by assertion. Use the existing ancestor-closed population restriction and label embedding, then the admitted join: [G7FullEpochSupport](../reuse/sources/G7FullEpochSupport.lean) constructs `populationPanel`, `panel`, and `joinedCode`, proves full register preservation and entire polynomial equality to the unchanged full-epoch coefficients. G1 opacity/grafting is needed when replacing a serial slot in a different source graph. Neither operation erases old descendant trees or draws a new register.

The one-population proof needs no cut-child or planarity hypothesis. The eventual G6 source replacement retains its original binary rooted LSA cut-child class, all protected cuts/controls, original edge occurrences, and one physical rate/inheritance bank shared across every observation row. A local `RootedBinary` theorem does not discharge that graph construction.

## Adapter A: the actual generator and a cap-only remainder

Define, using the unchanged recursion,

```text
P_M(s,d) = exprPolynomial(kernelExpr N M s d)
C = choose(M,2), B_M = (1+M*M)^M
delta(s,d) = if s=d then 1 else 0
G_z(s,d) = (eval P_M(s,d) z - delta(s,d))/(1-z)
Q(s,d) = - eval (derivative P_M(s,d)) 1
R_coarse(M) = B_M * C*(C-1)/2
```

Requested `G6OriginalPopulationGeneratorBounds` conclusions, under precisely the premises above:

1. `P_M` evaluates to the **actual full retained-state source PMF** at `z = exp(-pairRate r i*t)` for every positive original bank and nonnegative time. Reuse `kernelExpr_actual` at fuel `M`; establish `eval P_M 1 = delta` by time zero. If an alias to `populationPolynomial` is useful, prove it by actual physical evaluations and univariate polynomial uniqueness rather than assuming fuel-list equality.
2. Establish the exact unit-rate original generator:
   `Q(s,d) = sum p:Choice N s, (1/2)*delta(stepDestination N s (some p),d) - choose(k,2)*delta(s,d)`.
   The minus sign in `Q=-P'_M(1)` is mandatory because `z=exp(-t)`. Each original **ordered** choice contributes `1/2`. It is not an unordered-pair row with a silently duplicated rate. Reuse [SourceStepGeneratorBinding](../../2026-10-04-dot-complete-original-g1-1549z/src/UnifiedLean/Source/SourceStepGeneratorBinding.lean) to bind selected-view expectations when needed; it already relates actual original choices to the native generator.
3. For `0 <= z < 1`, prove the complete row bound
   `sum d:Code N sample, abs(G_z(s,d)-Q(s,d)) <= R_coarse(M)*(1-z)`.
   This is **row L1**, not TV. The eventual TV semigroup charge has its separate factor `1/2`.

The scalar proof uses `S_n(z)=sum l<n,z^l`. Mathlib's `geom_sum_mul_neg` gives `(1-z)*S_n(z)=1-z^n`. The existing power Lipschitz bound at `1` gives
`0 <= n-S_n(z) <= n*(n-1)/2*(1-z)`.
Rewrite the quotient with `eval P_M 1=delta`, apply the triangle inequality to each **raw term**, use exponent bound `n<=C`, then the accepted complete raw expression mass bound `B_M`. No new number-of-states factor is permitted. Terminal/empty rows have zero generator; handle `M=0,1` directly rather than divide by a nonexistent choice count.

This larger `R_coarse` is a legitimate cap-only quantitative adapter, not the sharper `R_M` in Appendix A. If it is used in a downstream computable size bound, name the larger constant and recalculate that bound explicitly; do not report Appendix A's sharper constants as proved by this substitution. It still preserves arbitrary source sizes and all capped forests.

## Adapter B: one positive atom list for every actual capped row

Assume `M>=2`, a finite supplied family `z_a in (0,1)` and real `alpha_a>=0`. Set `A=sum alpha_a`. For `A=0`, all weights vanish and the empty list is the result. For `A>0`, normalize by `A` and use the **tail** vector

```text
v_M(z) : Fin(M-2) -> R
v_M(z)[j-3] = sum l<choose(j,2), z^l   (j=3,...,M).
```

Apply Mathlib's positive convex-span theorem to the finite image of the **supplied** atoms. Its affinely independent output has at most `(M-2)+1=M-1` elements. Select original preimages for those coordinates and rescale the strictly positive convex weights by `A`. Requested output: `r<=M-1`, `0<beta_b`, `z'_b` from the original supplied atoms, `sum beta_b=A`, and equality of every tail coordinate. The first omitted coordinate `j=2` is identically `S_1=1`; preserving `A` restores it exactly. Merely preserving the nonconstant coordinates does not preserve the generator.

The **source** conclusion must then be universal: for every original `N`, `sample`, admitted `s,d`, population `i` and `CoLocated` entering state with `liveCard s<=M`,
`sum alpha_a*G_(z_a)(s,d) = sum beta_b*G_(z'_b)(s,d)`.
Use accepted spectral support for the same fuel-`M` recursion, collect nonzero coefficients at `choose(j,2)` for `j=2,...,M`, and eliminate the constant coefficient with `P_M(1)=delta`. This proves equality of the complete original operator, not just its lineage-count projection. **One** compressed list is chosen before `N,s,d`; do not choose separate atoms per forest, count, population or observation row.

This is mathematical positive compression of generators. Mathlib's real-weight existence theorem is noncomputable; it is not an executable Rust source extractor. Nor is the compressed generator itself declared a biological source. Explicit positive bigon factors, retained ordinary baseline redistribution, same-endpoint calendar rates and G1 source splice still need their own consumers.

## Sharper adapter C: condition the actual embedded merger chain on final count

Reuse the existing actual `sourceJumpStep`. Under `CoLocated` and `k>=2`, each real ordered pair has probability `1/(k*(k-1)) = 1/(2*choose(k,2))`; this follows by canceling the same physical rate in `choiceRate/totalRate`. Its `none` choice has mass zero. At `k<=1` it absorbs.

Define rational weights `w(s,j,d)` by exactly `k-j` iterations of that actual embedded real-merger row, or prove a rational encoding equal to those iterations. For `1<=j<=k`, prove nonnegativity, support `liveCard d=j`, and `sum_(liveCard d=j) w(s,j,d)=1`. Carried trees, original locations and the entering register remain literal destination data. For `k=0`, keep the identity row; do not request a nonexistent positive-count conditional law.

The scalar pure-death polynomial `p_(k,j)` can be defined by the **count quotient of the same recursion**: diagonal `X^choose(k,2)` and, below the diagonal, the actual ordered-pair lift summed over `k*(k-1)` choices. A convenient finite coefficient formula is
`c_(k,j,m) = product_(l=j+1..k) choose(l,2) / product_(l=j..k,l!=m) (choose(l,2)-choose(m,2))`, for `j<=m<=k`, with the terminal/empty cases separate. This is not an alternative fitted full-forest extractor.

Requested entire-polynomial identity for every original admitted destination:
`P_M(s,d) = C(w(s,liveCard d,d))*p_(k,liveCard d)` when `1<=liveCard d<=k`; otherwise prove the appropriate zero/terminal row. Nonnegative weights summing to one imply the full-forest coefficient L1 bound by the count coefficients, **without a forest-alphabet multiplier**. The same geometric proof then supplies Appendix A's rational
`R_M=max(1,max_(k<=M) sum_(j,m) |c_(k,j,m)|*choose(m,2)*(choose(m,2)-1)/2)`.

This is final-lineage-count conditioning. [G6.Conditioning](../../2026-10-07-cloud-g6-sol-ultra-1601z/sources/UnifiedLean/G6/Conditioning.lean) instead conditions/truncates an entering mixture or Poisson count and bounds discarded mass; it does not already prove this factorization.

## Remaining master consumers and next action

The reuse worker acknowledged A/B as compatible, non-overlapping next targets after its narrow old gathering and structural raw-calendar support repairs. Sole compiler/evaluator remains `lean_integration_successor`. The design worker will challenge C and the sign/mass/coordinate conventions against the already saved original-source population coefficient executions, with no producer rerun and no claim that eight fixtures prove the universal theorem.

After A/B, continue actual COMMON mixture/guarded private-register transport, stochastic semigroup norm propagation, positive Euler factors and baseline redistribution, an admitted bounded source splice, and one shared-bank joint forest/bin readout. Pointwise full-Code bounds lift through a **common** stochastic exterior with the entering history carried; they do not license arbitrary time-resolved readout, newly visible private bits, independent row fitting, rare-event posterior amplification, or a change of fixed controls. The general INDEPENDENT weak-factor/token construction is a separate noncommuting proof path. These precise downstream boundaries keep the accepted hand G6 master distinct from its unfinished formal and executable assembly.
