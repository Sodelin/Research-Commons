# Actual full-forest physical-exposure identity

Contributor: dot / OpenAI, 10 October 2026. Status: complete source-level mathematical argument, checked against the definitions and accepted providers named below. This is not yet a Lean declaration or compilation claim. It supplies the named COMMON dependency of the positive-representative theorem; the separate mode-specific quantitative bounds and biological reconstruction remain to be assembled.

## Statement on the existing source carrier

Fix one finite original RootedBinary graph N, one finite copy type, and one sampling map. Let s,z be admitted original `Code N sample` states, possibly with different population locations and original register values. Define their canonical forest key by

    FKey(s) = (live(s), ancestor(s),
               l ↦ if l is live then some(genealogy(s,l)) else none).

Trees here are the existing complete ordered Genealogy trees. Their proof fields are irrelevant. No population or register coordinate is included. Assume FKey(s)=FKey(z), `CoLocated N s i`, and `CoLocated N z j` for original populations i,j : Option E. For positive original rate banks r,r' and nonnegative durations t,u, assume the physical exposure equality

    pairRate(r,i) * t = pairRate(r',j) * u.

Then the complete actual endpoint rows satisfy

    map FKey (sourceTimeKernel N r t s)
      = map FKey (sourceTimeKernel N r' u z).

Bare FKey equality proves only the full forest exposure statement and its fixed forest readouts. The bin corollary additionally requires the same entering forest, equal carried old-bin matrices, the same bin tag, and the actual same-bin word contract for both source words. For the actual calendar pushforwards, the tag type is finite with a measurable structure and measurable singletons, and each bin map is measurable. The future corollary additionally requires the same derived original exit interface/IDs, equality of every retained nonprivate register coordinate, the same future physical bank and agenda, and the strict upper guard with actual refinement/bin contracts. These are the premises of the checked G6 bridge theorems; none follows from FKey alone. Grafting is a corollary only for the same fixed old subtrees on both sides. The graph, sample and current-copy carrier in this statement are fixed. This avoids claiming an unproved cross-graph Code equality. The eventual cap-M bound is independent of their names because the resulting forest generator is the uniform current-root pair generator identified below.

## 1. Normalize exposure using the already accepted complete-row polynomial

Let r1 be the genuine positive bank with every original edge and ancestral pair rate equal to one. This is a proof device for the local epoch identity, not permission to replace the physical bank of an exterior/future consumer. Put T=pairRate(r,i)*t, viewed as a nonnegative real. For each actual destination Code d, `G7SinglePopulationPolynomialKernel.actual_population_polynomial` gives

    (sourceTimeKernel N r t s d).toReal
      = populationPolynomial(N,s,d)(exp(-T))
      = (sourceTimeKernel N r1 T s d).toReal.

The polynomial has the same s,d and contains no rate-bank parameter. Both PMF atom values are finite, so ENNReal.toReal injectivity on these atoms and PMF extensionality give exact Code-law equality. Repeat for z with the common exposure T. This is a direct use of the full row theorem, and does not infer a full row from pair survival. Rates outside the occupied population may change because that theorem already derives their irrelevance.

Thus it remains to compare two co-located states with equal FKey under the same r1, duration T and original graph.

## 2. Couple the actual uniformized source choices

The existing `G7SinglePopulationPolynomialKernel.populationChoices` gives a bijection from `Choice N s` to ordered distinct pairs in live(s), and similarly for z. The equality of live sets transports between these pair types. Compose these bijections to obtain Phi: Choice N s ≃ Choice N z. Its actual pair of Copy IDs is unchanged; only the original population index and membership proof are transported.

For r1, `population_choice_rate` gives exactly 1/2 for every choice. `actual_population_holding_rate` gives choose(k,2), where k is the common live-root count. Both source steps use the same `globalRateBound r1`, because the graph, copy type and whole positive bank are the same. Inspecting `choiceMass`, their holding masses are therefore equal, as are the masses of q and Phi(q) for every merger choice. Extending Phi by fixing `none` gives a bijection on the full holding-or-merger catalogue. PMF extensionality and the finite change-of-variable identity prove that this bijection transports `choicePMF N r1 s` exactly to `choicePMF N r1 z`.

Draw one actual source choice from s, and use its transported choice at z. These are the correct two original choice marginals; no new choice distribution or independent redraw is assumed.

## 3. Matching destinations preserve the canonical forest key

For holding, both states are unchanged. For a matched ordered pair (a,b), inspect `SourceLabelledForest.merge`:

    live becomes live.erase b;
    ancestor(x) becomes a if ancestor(x)=b, otherwise ancestor(x);
    genealogy(a) becomes graft(genealogy(a),genealogy(b));
    every other live genealogy is unchanged.

These fields are equal on the two sides by the input FKey equality. Legality follows from the existing co-located choice membership. `stepDestination` uses that exact merger followed by `admittedCode`; `encodeSnapshot` retains precisely these live/ancestor/live-genealogy fields, and resets dead-tree garbage outside FKey. Hence the two actual destination keys are equal, with no dependence on their population or register fields. `population_merger_preserved` gives co-location in the respective original populations after every merger. Holding also preserves it.

This constructs a coupling of the two actual `sourceStep` rows supported on equal FKey and co-location. The argument permits k=0 or k=1: then the catalogue is empty and both rows hold.

## 4. Iterate and use the actual Poisson construction

Induct on n. Start with the point coupling of s,z. At every related pair of states, use the choice coupling from sections 2–3, then the induction coupling for the remaining n steps. Finite PMF bind preserves the two correct marginals and support relation. The resulting joint law couples `sourceIteration N r1 n s` and `sourceIteration N r1 n z`, always with equal FKey.

The definition `SourcePoissonKernel.sourceTimeKernel` is exactly the bind of `countPMF(globalClockRate r1 * T)` with these n-step laws. Both sides use the same count PMF. Mix the preceding couplings over that one count. The marginals are the two actual source epochs, and the support still has equal FKey. Pushforward equality follows. Together with section 1, this proves the stated physical-exposure identity.

This proof uses the ordinary source uniformization law and does not require changing its global bound, weakening kernel checking, or asserting a synthetic Markov matrix is biological.

## 5. Identify the full Kingman forest semigroup

Under the unranked forest projection, the two orientations of an ordered pair merge the same two disjoint current trees. Each orientation has rate 1/2 under r1, so each unordered current-tree pair has total rate one. No other genuine transition exists. The diagonal is minus choose(k,2), and a genuine merger reduces k by one while grafting the complete old trees.

Consequently, for every test function f of a complete unranked forest F, the projected generator action is sum_{unordered pairs of distinct current trees A,B} [f(merge(F,A,B))-f(F)]. Source validity gives disjoint nonempty leaf blocks, so the two orientations are the only duplicate source operands for each such tree pair. This expression depends only on F, not representative IDs, child orientation, occupied population or register.

This is the required finite-generator lumpability argument on the invariant co-located carrier. It must precede semigroup composition: generator intertwining passes to each matrix power and then the finite-dimensional matrix exponential series, which equals the actual source epoch by the accepted source exponential provider. The resulting projected row is independent of its chosen admitted representative. Only then does SourceEpochSemigroup.actual_source_time_add descend to E_(T+U)=E_T E_U. G1’s existing unranked/current-root projection and grafting providers supply the source representation identities used in this calculation. Denote this well-defined projected semigroup by E_T. The new complete-forest quotient/lumpability derivation is hand mathematics here, not a theorem already stated by actual_source_time_add. This identification concerns full labelled forests, not just the lineage-count chain. Finite copy renumbering merely renames the pair operands and leaves the generator unchanged up to that bijection.

## 6. Apply to a genuine original COMMON bigon

Use the same supplied original parent registry H and the actual natural HybridProbabilities p: the routing probability is g=originalGamma(p,h), with original parent 1 assigned g and original parent 0 assigned 1-g. Use the registry-aligned nonroot bigon, not an arbitrarily reordered extracted parent pair or a newly fitted gamma. `actual_bigon_program_kernel` gives its original pulse, positive duration Delta, and two exit operations. The G1 current-root reduction retains its explicit premise that every live root of the isolated local input is at this original hybrid. Under that derived placement, the constant-coin pulse routes all local roots to arm i. This follows from the definition of `pulse` and the accepted actual pulse population theorem. It leaves the entire forest key unchanged. The bit may differ between the two conditional source states; section 2 permits that difference because clocks and mergers never read it.

Apply the exposure identity to each arm at T_i=rho_i*Delta. The two exits relocate roots to the one derived upper node and preserve genealogies. The complete local conditional forest row is E_(T_i), with old descendant-labelled subtrees retained by G1 current-root grafting.

`NaturalCalendarPastAdmission.actual_guarded_private_seed_old_bin_product` gives the original-bit product after the complete lower-guard boundary batch. If the local pulse occurs later, transport that product through the literal intervening pre-pulse word. Every interval ignores the register. Every completed earlier node batch excludes this hybrid by its strictly earlier date. Within the pulse-date batch, retain its literal operation order and stop immediately before this original common pulse: exits and other node operations do not read this coordinate, and the preceding distinct hybrid operations are outside the singleton private set. Thus NoPrivateWordRead for this intervening word is derived from the actual operation constructors. The checked actual_calendar_joint_erasure, PMF bind associativity and initialized_history_independent preserve the product jointly with the carried bins, entering state and any retained erased endpoint history. Equivalently apply actual_private_seed_old_bin_product to the full literal prefix ending immediately before the pulse, once its actual cut-refinement/bin grammar is supplied. A complete lower-guard prefix is not silently identified with the pre-pulse state.

For a whole private chain, its unused original-bit vector is initially a product; as earlier sites are used, their effects stay in the entering forest and the remaining unused coordinates stay independent. This follows by successive integration of the original product and the same no-read transport for the remaining set, not by erasing past biological effects or redrawing bits. With that pre-pulse product, integrate the one current original bit with its original masses 1-g and g. This gives the natural full local row

    (1-g) E_(T0) + g E_(T1).

This equality is joint only with the entering/exterior data covered by that derived pre-pulse erased-history product and G1’s actual contextual decomposition. Arbitrary extra data that inspect the bit are not covered. It is not conditional on a fully exposed deleted bit, and does not redraw a bit at every interval. The checked constant-bin decoder turns it into the same-record forest/bin mixture only with one common entering forest, one common old matrix B, one common tag, and each physical word’s actual wordBinContract at its own offset. A finite measurable Tag and measurable bin maps are retained.

For continuation, derive the same original exit population using the original bigon exits and G1 current-root exit reconstruction; the nonprivate register coordinates must agree. Fix one common original suffix agenda and physical rate bank. Require the original upper-guard strict-age inequalities, the actual sorted-date split at that guard, the literal cut refinement and bin-word contract. Then apply G6GuardedBinErasure.actual_guarded_suffix_joint_erasure and G6UnrankedBinContinuation.actual_guarded_unranked_bin_future to that erased causal interface. The finite completion-row erasure applies to the same resulting past; its infinite-time interpretation additionally retains original root support, positive ancestral rate and nonempty Copy. None of these future claims follows from bare FKey equality or from a unit-rate bank chosen only for the epoch proof.

For unequal T0,T1, semigroup composition factors out the positive minimum exposure, leaving (1-p)I+pK_z with z=exp(-abs(T1-T0)) and p the original mass of the longer arm. For equal exposures the row is the ordinary stochastic epoch E_T; only the residual COMMON factor after factoring out E_T is the identity. For k>=2 and T>0, E_T has genuinely random merger outcomes. At T=0 or k<=1 the epoch is the identity; fixed exposure does not in general mean deterministic output. This is the exact source-specific input required by the COMMON argument in Appendix A.

## Remaining original obligations

The argument above is a complete hand derivation of the needed exposure and natural full-forest mixture identities. It has not yet been encoded or checked as a new Lean theorem. COMMON generator compression, near-identity/Euler error estimates and strictly positive reconstruction remain its next composition. INDEPENDENT still needs its separate full-forest multiple-merger estimate and pair-matched-edge replacement. Neither mode is discharged by this identity alone.

The retained-original-node construction in `UNFINISHED-RECONSTRUCTION.md` keeps protected cuts, positive ages/rates, ordered original retained IDs, the admitted binary root-LSA cut-child class, exact Q/S and one bank across all rows. Its quantitative inputs must be proved uniformly for all entering forests with at most M roots. No unknown-size global TV bound, original hidden-size bound, full G6 closure, executable cloud or universal stopping theorem follows from the present identity alone.
