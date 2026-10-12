# Independent same-bank cross-arity source review

12 October 2026, 03:57 UTC. Reviewer: dot (OpenAI), existing G4 review lane.

**Scoped static HAND/SOURCE PASS. No blocking mathematical premise or definite API issue found. UNCOMPILED: actual elaboration and kernel acceptance remain required.**

## Exact reviewed candidate

- `G4ActualFirstMeetingExposureScaling.lean`: `e9555a94b8390fb52486b359ab274828f57296f0b0066131e4106060c0ee3074`.
- `DEPENDENCY-LEDGER.json`: `38ec16375b72f01704041fb7bf39dc279abc53a0d1df3944342489a967adde21`.
- Accepted 1,595 source graph: `63d52b9b906b85070470b6f6183bc5f0cb85a7e911d790cf6c16ee36e1bfbe1f`.

The companion import check independently rehashes all 307 accepted provider bodies, matches their comment-aware literal import lists to the accepted graph, and reconstructs exactly the recursive closure of the two direct imports. No compiler, builder or native object was invoked. The original scaling-only body is preserved; revision 1 adds the direct mass consumer and required namespace opens without altering the underlying scaling argument.

## Mathematical/source derivation

1. Every deterministic `fixedRegisterBoundary` changes only actual population positions and uses the stored register. Its live set is preserved; the accepted snapshot encoder/decoder copies the live field literally. The same property propagates through `fixedRegisterPrefix`, whose interval case is the no-merger reference identity. Natural initialization starts with the universal live set. These are deterministic reference facts, not a claim that the random source has no mergers.
2. On that reference state, validity makes each copy its own representative. The accepted `initial_reference_location_cross_carrier` theorem compares each A copy and the B copy with the same two-label reference carrier under the same original bank, program and parameters. Thus all A copies have one original location, B has the other, and the accepted minimality theorem makes those locations distinct before the pair-derived first-meeting index.
3. The finite population calculation is exact. At the A location the original live population is precisely the image of `Fin k` under `Sum.inl`; at the distinct B location it is the one `Sum.inr ()` label; every other location has no root. Choosing two roots consequently gives `choose(k,2)` at the A location and zero elsewhere. It includes k=0 and k=1.
4. `actual_rate_choose_two` is the existing actual ordered-choice-rate theorem. Substitution yields the original rate as `choose(k,2)` times the sum of the original population rates at the A location. The same formula at k=2 has factor one. This establishes the rate comparison without replacing the source clocks, postulating an independent-copy law or discarding register dependence. If a reference location is a node, it matches no original active population and contributes zero, consistently with the actual rate definition.
5. The generic exposure lemma is a finite-list induction on the actual referenceExposure recursion. Interval contributions use the original duration and the rate comparison at prefix zero; the tail uses prefix q+1. Boundary contributions apply the same actual fixed-register boundary on both carriers. No time rescaling or reordering occurs.
6. Truncating at the single pair-derived index uses the exact take-length and take-take identities. Every contributing prefix q is strictly below that same cut, so the separation theorem applies. This includes intermediate operations within a tied batch, with no new calendar abstraction or simultaneous-event assumption.
7. The final corollary rewrites the accepted original full-calendar specified-comb probability using this exposure equality. It retains the same fixed bank, rates, parameters, initialization, full labelled carrier and specified singleton-forest event. It does not replace the existing source law with a scalar model.

## Exact directly inspected providers

- `G5SafePrefixRouteBridge`, `46a8a090dcd67361eeebf32c0f0d5ddc78e14adc3c0499b6806451832d62a004`: `fixedRegisterBoundary`, `fixedRegisterPrefix` and their original register/location semantics.
- `FiniteSourceSnapshot`, `4628112bbbc69528748bbc93f8a3f8200bc802a6e72417fb90c39e7acd49f744`: exact live/ancestor/register encoding and decoding.
- `SourceBoundaryKernels`, `994b25e798e39889a56084b267c3e896580cd21e902764c3c6922d9bfdd6070d`: actual exit/ordinaryUSER_HOME/pulse code operations.
- `SourceForestKingmanPopulationProjection`, `e8733ab8e66c60f98cfcfcd56e703b55a5ad8674dc5361f4ac6cb0c35f80f6e4`: `populationRoots` as the filtered actual live set.
- `ActualPopulationRate`, `a44ab66a57e870c3b7b0379b44386b8b86a56361543d73e98eee0b46192eff2f`: `actual_rate_choose_two`, derived from the original ordered-choice denominator.
- `G4ActualBankFirstMeeting`, `d60df70028b5716dff3174999de070e2b1ee5a0f9a5796c2e9b82f497ffe5fc3`: the same-bank cross-carrier location theorem, pairReference, before-meeting separation and referenceExposure recursion.
- `G4ActualFirstMeetingCombMass`, `dd532edc685d41fa4352badac2c56f322950f7c58ea98c1a1542721712c06fa1`: the checked completed full-calendar specified-comb mass.

The exact Lean/Mathlib interfaces for `List.length_take_le`, `List.take_take`, `List.take_succ_cons` and `Finset.card_image_of_injective` were also checked. The candidate's local live/cardinality helpers are concrete deterministic compositions of inherited APIs, not new no-loss or rate principles. Wider historical/provider coverage remains the separately assigned reuse audit; no novelty is claimed here.

## Quantifiers and limitations

For each original bank the same meeting index is used for every arity. The theorem proves the actual k-copy exposure equals `choose(k,2)` times that bank's two-A/one-B exposure. It does not choose a new bank or meeting cut for each k. The pair reference defining the cut contains one A and one B; the exposure denominator uses two A copies and one B. Those two distinct carriers are intentionally linked by the accepted same-bank location theorem.

The rate and exposure identities retain k=0, k=1 and equal-taxon/immediate-meeting controls. The final comb mass corollary has the existing nonempty distinct complete A-list excluding B; it is one specified labelled child-swap-quotient comb rather than a union of comb shapes.

No strict positive exposure, positive bank weight, conditioned-prior substitution, natural-bank average or new observable is assumed. A fixed hidden-bank identity is not hidden-bank observability. Natural averaging, strict distinct-taxon exposure, larger-panel acquisition and general G4 forcing remain later bindings. This source ports the inherited arbitrary-k hand argument and does not claim a new mathematical theorem, INDEPENDENT-mode transfer or master closure. Any elaboration correction must preserve these exact premises and the frozen original history.
