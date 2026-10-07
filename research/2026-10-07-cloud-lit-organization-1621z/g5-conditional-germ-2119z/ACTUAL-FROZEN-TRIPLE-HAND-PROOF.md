# Actual frozen-epoch triple row

Contributor: Codex literature/organization lane, delegated by CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026. **New source-connected hand proof, independent review pending; no Lean implementation or compiler claim.** The exact [matching contract](MATCHING-CONTRACT.md) fixes the interpretation before this derivation. The proof reuses Dot's actual source kernel/merger/renewal identities and Astra's explicit triple polynomial row. It does not assume a desired transition or conditional law as a source field.

## Statement with the full-copy assumption visible

Fix the original finite rooted binary source `N`, original arc occurrences `E`, original sample assignment and register, and positive physical bank `r : PositivePairRates E`. Let the **entire** copy carrier be `Copy=Fin 3`, with three distinct original labels `0,1,2`. For the G5 three-tip experiment the sample labels are distinct original tips. Take one entering admitted `Code s`. Assume its decoded live roots are precisely `0,1,2`, its ancestor map is identity, and each live genealogy is the corresponding singleton leaf. Assume each root is in an original edge population or `.rootPopulation N.root`; there are no node-location roots. These are actual entering-state conditions, not assertions of a stochastic row.

The source program for this lemma is one frozen interval, with no demographic transport, hybrid pulse or boundary. For physical use choose its duration inside one admitted active original calendar epoch. The constructed `sourceTimeKernel` is mathematically defined for every nonnegative duration; a physical original-calendar identification outside that active interval is not claimed.

Let `p(s)` encode equality of the three original current population locations: `0=0|1|2`, `1=01|2`, `2=02|1`, `3=12|0`, `4=012`. Let `G(d)` encode equality of the three actual endpoint ancestors in any admitted destination `d`, using the same five codes. This endpoint relation is a genuine equivalence relation, so the five cases are exhaustive and disjoint. Put

    mu_s(u,j)=sum_{d:G(d)=j} (sourceTimeKernel N r u s d).toReal.

When `p(s)` has a nonsingleton population block, let `rho(s)>0` be its actual original population pair rate. An edge block uses `r.edge e` at its unchanged original arc `e`; a root block uses the **separate** `r.ancestral`. A triple has at most one nonsingleton occupancy block, so there is no ambiguity. If all populations are separate, choose the unused positive `r.ancestral` as `rho(s)`. Then, for every `u>=0` and `j:Fin 5`,

    mu_s(u,j)=row(exp(−rho(s)*u),p(s),j).                 (R)

The result concerns the complete ancestry partition at time `u`, allowing up to two real mergers. Its pair entries do not count a first-pair mark after that pair has already joined the third ancestor.

## Actual source ingredients

The [original forest provider](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/Imported/SourceLabelledForest.lean) defines a merger by grafting the two existing genealogies, erasing only the removed live representative, redirecting exactly its ancestral fibre and retaining locations/register. `merge_never_splits` and `merge_population_preserved` hold for actual legal mergers. [FiniteSourceSnapshot](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/FiniteSourceSnapshot.lean) and [SourceStepGeneratorBinding](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceStepGeneratorBinding.lean) prove that actual coding preserves live genealogies/populations and selected views; no substitute genealogy is inserted.

[UniformizedSourceStep](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/UniformizedSourceStep.lean) enumerates exactly the ordered distinct live-root pairs at original edge/root populations. Its `choiceRate` is `pairRate/2`, so two orientations of one unordered pair have combined rate `rho`. Dummy holds do not change the entering code. The copy/rate-derived global uniformization bound is an internal algorithmic clock; it is not the genuine merger rate used below.

The actual PMF/kernel is the [original Poisson/source-step construction](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourcePoissonKernel.lean). [SourceActualHoldingClocks](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceActualHoldingClocks.lean) proves its no-real-merger return mass is `exp(−totalRate*u)`, and every genuine merger decreases live cardinality. In [SourceEpochRenewal](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceEpochRenewal.lean), `actual_source_kernel_first_jump` proves, for each actual destination `d`,

    K_u(s,d)=e^(−lambda(s)u)*1[s=d]
      + integral_0^u e^(−lambda(s)v)
          sum_{a in Choice(s)} rate(a)*K_(u−v)(dest(s,a),d) dv.   (J)

Here `K` is the actual `sourceTimeKernel`, `lambda=totalRate`, and the destination is the inherited legal source merger. The theorem is derived from the actual generator/exponential, not assumed. Finite summation of (J) over any endpoint partition class is legitimate: all sums are finite, and the exact kernel entries have continuous exponential representations. Remaining duration is `u−v>=0` on this integration interval.

Alternatively the checked [literal epoch law](../../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2LiteralEpochLaw.lean), `original_copy_cap_literal_epoch_law`, identifies this PMF with the actual full-copy clock compiler. [SourceDestinationClockReset](../../2026-10-04-dot-verified-lean-825-0203z/package/baseline/UnifiedLean/Source/SourceDestinationClockReset.lean) derives the joint winning-time/surviving-catalogue reset at the original rates. The proof below uses (J), so it does not need to posit independence of newly drawn future clocks or a fitted five-state process.

## Proof of (R)

Every legal merger joins two roots in the same current population, and the merged root stays in that population. Therefore no two labels from different blocks of `p(s)` can join during this frozen interval. Merger ancestry never splits. These facts restrict all endpoint partitions reached by actual source iterations and their Poisson mixture.

**All three populations separate (`p=0`).** There are no actual legal ordered pairs. `totalRate=0`, the source step is a hold with probability one, every source iteration is the same point mass, and hence the Poisson mixture is the point mass at `s`. The genealogy partition remains discrete for all `u`. This equals `row(q,0,j)` for any `q`, including the unused root rate convention above.

**Exactly one population pair (`p=1,2,3`).** The catalogue consists of precisely two orientations of that pair, each at `rho/2`, so its total genuine rate is `rho`. After the first legal merger the pair block has one live root and the third label remains in a different population. The destination has no legal pair and is absorbing for this interval. Thus its only attainable genealogy partitions are discrete and `p`. A discrete endpoint can only arise from no real merger: any real merger permanently identifies that pair. The actual no-merger theorem gives mass `q=exp(−rho*u)`. Normalization of the genuine PMF gives mass `1−q` on `p`, with all other masses zero. The two orientations may encode different ordered grafts/survivors; summing their common ancestry-partition class handles that internal detail without quotienting the source itself. This is precisely `row(q,p,j)`.

**All three roots in one original population (`p=4`).** There are six legal ordered pairs at `rho/2`, so `lambda(s)=3rho`. After any one real merger, there are exactly two live roots in that same population, with two legal ordered choices and total genuine rate `rho`. After the next merger only one root remains and the source is absorbing. Thus no hidden merger path can return to a different pair partition or restore the discrete partition.

The discrete endpoint has no real merger and therefore mass

    mu_s(u,0)=exp(−3rho*u)=q^3.

Fix one specified pair code `j=1,2,3`. In (J) the initial point mass gives no contribution to this class. The two first choices that join that specified pair each have rate `rho/2`; each destination retains partition `j` until its second merger. Its mass still in `j` after remaining time `u−v` is the actual no-second-merger mass `exp(−rho*(u−v))`. First choices for either other pair can never lead to partition `j`: they retain their own pair until the complete three-label block. Consequently finite aggregation of the actual renewal formula gives

    mu_s(u,j)
      = integral_0^u rho*exp(−3rho*v)*exp(−rho*(u−v)) dv
      = rho*exp(−rho*u)*integral_0^u exp(−2rho*v) dv
      = exp(−rho*u)*(1−exp(−2rho*u))/2
      = (q−q^3)/2.

This evaluation uses `rho>0`; at `u=0` the integral is zero and the same formula holds. The actual PMF is normalized and the five ancestry partitions are exhaustive. Its remaining mass is therefore

    mu_s(u,4)=1−q^3−3*(q−q^3)/2.

These five entries are exactly `discrete3`, `pair3`, `together3` and `row` in the selected polynomial provider. All active edge and ancestral cases use the same calculation at their own positive rate. This proves (R) at hand level.

## Exactly what it supplies to the analytic germ

For a genuine finite distribution `w(s)` over supported entering triple states satisfying these conditions, finite mixture of (R) is definitionally the selected analytic `frozenMixture(w,rho,p,u,j)`. For positive supported weights/rates, the already checked `occupancy_support_eq_of_right_germ` can then be applied **if actual observed conditional right-germ equality has been proved to be equality of these mixtures**. Different seed carriers, repeated rates and survival-induced dependence among weights are allowed.

This proof does not derive that posterior. It does not identify the measured whole-calendar no-selected-merger event, prove its denominator positive, or prove that its positive fibres are exactly the original feasible routes. The checked fixed-Code no-any-event residual lemma gives a useful local survival factor, not all those implications. Conditioning on continued survival through `u` would replace the complete partition row by a different law and change posterior weights. The row's analytic continuation for all `u` also does not claim that an original finite edge remains physically active after its next calendar boundary.

## Extra copies and old subtrees remain explicit

The full-copy statement above has no extra active roots and no entering nonsingleton old genealogy. Those are hypotheses, not deletions performed by the proof. In a larger original source the actual `totalRate` need not be `3rho`, even when three selected roots share a population. For example, four distinct full roots in one population have no-any-event mass `exp(−6rho*u)`, whereas the three-copy row has discrete mass `exp(−3rho*u)`. This is an exact obstruction to substituting full-source no-any-event conditioning for selected-no-merger conditioning; it is not a claim that ordinary selected-source projectivity fails.

A narrow contextual extension follows from the same proof: let a larger admitted copy carrier have **exactly three live roots**, each carrying one nonempty old well-labelled subtree, and choose one original marked label in each of their disjoint ancestral fibres. Retain every old subtree, original population, register and copy ID. Define `G` by the marked labels' ancestor equality. The legal catalogue still has exactly the same 0, 2 or 6 ordered choices, each merger grafts the existing operands, and old within-operand relations remain. The actual first-jump formula (J) therefore gives the same five-partition fusion row. The larger global uniformization bound cancels in (J); it does not change the actual 0/rho/3rho rates. This is a row about fusing three whole old blocks, not a replacement of the actual full forest by three bare tips.

For a larger carrier with additional **live** roots, extending this row must explicitly invoke the inherited source projection/generator factor-through with the actual pruned view. The checked ordinary hidden-register timed projectivity can first supply a genuine selected three-copy law, but conditioning on an earlier event still requires its correct source-connected consumer. This proof does not equate arbitrary full-source conditional laws to freshly initialized independent panels. Old chronological graft ages or an arbitrarily correlated entering past remain attached through their own actual marked-record/decoration law; the endpoint-partition row alone does not certify that attachment.

## Scope and continuation

The matching row is proved at hand level under the stated actual source conditions. The missing G5-B/C1 stochastic row is advanced; actual posterior/observable-germ binding, safe chronology, deletion, full target assembly and HG remain separate. No new Lean statement was entered, compiler run launched or historical priority claimed. The triple Kingman calculation is standard; this contribution binds its exact convention to Dot's original source PMF and Astra's already selected row.

At Nolan's new coordination instruction, preserve this packet for the external Dot/Astra G5 owner and wait for agreed allocation before further G5 work. The [posted coordination proposal](../../../handoffs/2026-10-07-codex-cloud-sol-ultra-g5-g6/inbox/G6/20261007T212900Z-DOT-CODEX-COORDINATION-PROPOSAL.md) is an actual publication; it is not evidence that Dot read or accepted it. The dated handoff and source checks preserve this distinction.
