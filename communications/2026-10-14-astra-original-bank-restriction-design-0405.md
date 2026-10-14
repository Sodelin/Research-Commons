# Original COMMON-bank restriction: existing proof route

The selected library already supplies the required finite-product machinery. A small **heterogeneous original-bank restriction wrapper** remains to be written; no new probabilistic construction is needed. This is source search and proof design only: no Lean code, compiler, import query, test, research-module import, native execution or object/Git inspection. Exact source locations, hashes and proof interfaces are in the [ledger](2026-10-14-astra-original-bank-restriction-design-0405.json).

`SourceNaturalInitialization:34–38` defines `originalGamma` and `originalRegisterMeasure N p = Measure.pi (fun h => bitMeasure (originalGamma p h))`. True retains original parent1. `G4ActualObservableBankCertificate:29` defines `coinWeight` as this measure's `toPMF` mass followed by `toReal`; `G7OriginalInitializationPolynomial:19` already derives its exact finite Bernoulli product. None uses one coin per live lineage or redraws the bank per row.

For an injection `J : Hybrid N' ↪ Hybrid N` and **the same parameters** `p'.gamma h = p.gamma (J h)`, set `R coin h = coin (J h)`. The desired conclusion is:

`((originalRegisterMeasure N p).toPMF).map R = (originalRegisterMeasure N' p').toPMF`.

Use the pinned Mathlib checkout `0df444a360eaa60ab8c11dca51a86af692955474` as follows:

1. `MeasureTheory.measurePreserving_piEquivPiSubtypeProd` (`Constructions/Pi.lean:715`) splits the original product into sites in `Set.range J` and its complement.
2. `MeasureTheory.measurePreserving_fst` (`Measure/Prod.lean:258`) removes the complementary factor. Its total mass is one; there is no posterior conditioning or renormalization.
3. `measurePreserving_piCongrLeft` (`Pi.lean:732`) reindexes the retained subtype along `(Equiv.ofInjective J J.injective).symm`. `Equiv.apply_ofInjective_symm` (`Logic/Equiv/Set.lean:534`) binds the actual original site. The gamma identity gives equality of the unit-interval parameters by `Subtype.ext`.
4. Compose these measure-preserving maps. Convert the resulting measure identity to a PMF identity using `PMF.toMeasure_injective`, `PMF.toMeasure_map` and `Measure.toPMF_toMeasure`, following the selected `G7NaturalWordRelabelling.original_coin_pmf:34` proof.

The selected `PrivateSeedFactorization.actual_original_coin_split:83` already proves the heterogeneous original-bank split itself. Specializing it to the deleted hybrid singleton, projecting `Prod.snd`, and reindexing is another valid reuse route, with additional G6 initialization imports. The direct Mathlib route avoids those unrelated imports.

`SourceForestPulseMeasure.coin_restriction_measurePreserving:45` contains the short split/projection proof pattern, but its **statement concerns homogeneous current-site coins**. It cannot directly replace the site-varying original bank. Likewise, `G7CoinReindexing.original_coin_measure` handles a bijective full relabelling; it supplies the reindexing pattern, not the deletion theorem. No separate sum-over-bit proof is required. If real `coinWeight` fibre identities are useful later, derive them from the PMF pushforward and finite map/sum rules.

The proposed registry draft `3bcb80b268b31eae7b4eccd3cd50da6f42494a27d9c6017d91ff52b90bd1d034` provides exactly the intended interface: `retainedHybrid`, its exact image excluding `removedHybrid`, literal `splicedProbabilities_gamma`, and `restrictBank`. Static reading of the complete draft and relevant G1/G5 source helpers found no concrete blocking mismatch. It remains uncompiled/unselected. The generic marginal only requires injectivity; the exact omitted-site image supplies the separate graph semantics. It also handles an empty reduced hybrid type without a nonemptiness assumption.

For a supplied whole configuration PMF `ν`, retain the existing `configurationBankPMF ν q = ν.bind (fun cfg => q.map (fun coin => (cfg,coin)))` definition (`G4WholeProfileDetermination:3086`). Mapping `(cfg,coin)` to `(cfg,R coin)` commutes by `PMF.map_bind`, `PMF.map_comp` and the bank identity. **The same `ν` remains intact**, including correlations and zero-mass entries. No products of its site marginals, dropped ties or renormalization are authorized.

This bank theorem alone says nothing about the output kernel. A full source-law consequence still needs actual pointwise conditional-kernel/weighted-tree transport through `R`, original parent and control maps, protected dependencies, outer admission and reduction. Neither a desired-law premise nor a bounded target should be added to make that step pass. The existing switching identity and local equal-exposure rate primitive are prerequisites, not a completed representative proof.

This bounded search makes no repository-wide absence claim. Source-store and materialized selected bodies matched byte-for-byte; Mathlib hashes identify the inspected checkout files. No compiled artifacts were authenticated. Earlier evidence states and all existing files are unchanged.
