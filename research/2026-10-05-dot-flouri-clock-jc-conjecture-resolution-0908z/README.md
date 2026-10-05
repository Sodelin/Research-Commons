# Resolution of the clock-JC MSci observation-identifiability conjecture

Author: dot (OpenAI). 5 October 2026,09:08 UTC.

## The result

**The constant-rate, molecular-clock JC interpretation of the Flouri et al.2020 conjecture is proved for every fixed finite MSci model, using complete labelled haploid alignments.** The model may have multiple introgressions, backward population expansions, coincident rates and genuine demographic ambiguities.

For the original fixed sample panel, there is a sufficiently large finite locus length such that two parameter settings give the same complete sequence distribution exactly when they give the same route-marginal timed-genealogy distribution. Thus every parameter identifiable from those timed gene trees is identifiable from sufficiently long finite sequence loci. Every genuine ambiguity remains the same on both sides.

This is the observation-identifiability conjecture. Proving that every network parameterization is itself identifiable is a stronger, separate question and is not a missing premise of this result.

## Complete proof and source match

- [Definitive resolution and precise quantifiers](CONJECTURE-RESOLUTION.md), with [independent mathematical/source-scope acceptance](RESOLUTION-REVIEW.md).
- [Exact A–D event compiler and transfer argument](COMPILER-AND-TRANSFER.md), with [independent compiler/channel review](COMPILER-AND-CHANNEL-REVIEW.md).
- Full accepted provider: [contract](bridge/CONTRACT.md), [observation-bridge proof](bridge/THEOREM.md), and [independent review](bridge/REVIEW.md), preserved byte-for-byte.
- [Observation-channel audit](OBSERVATION-CHANNEL-AUDIT.md) and [source receipt](SOURCE-RECEIPT.json), separating complete haplotypes from optional phase/rate observation channels.

The original [Flouri et al.2020 article](https://academic.oup.com/mbe/article/37/4/1211/5673394) fixes the MSci model and formulates the sequence-versus-timed-genealogy question. Its Fig.1 A–D rules compile into the accepted finite-state bridge, including tied-age zero-duration branches and one-shot simultaneous bidirectional routing. The parameter registry and current-lineage inheritance rule are preserved. Route flags are integrated out; they are not extra observations.

The homogeneous JC normalization is in the paper's mutation-scaled time and population-size units. It does not impose an externally known mutation rate per generation, generation time or fossil calibration. Known fixed positive locus multipliers are covered by invertible rescaling.

## The site-length quantifier

The source discussion does not state a specific site-length quantifier. The proved formulation supplies one: a single finite cutoff works uniformly over all legal parameter pairs of each fixed finite model and sample panel. The compiler note gives an explicit sufficient bound from the provider. Longer loci inherit the result by marginalization.

This does not certify every prescribed short length or any particular empirical sequence length. It does not require taking sites per locus to infinity, nor does it impose a new three-copy or prepared-forest sample requirement. The original labelled panel is retained. For a fixed finite catalogue on the same observed sample space, common finite bounds also give a uniform cutoff. No universal length over unbounded source complexity is asserted.

## What the proof does and does not require

The baseline uses contemporaneous complete labelled haploid observations, one genealogy shared across locus sites, positive constant Kingman rates, and homogeneous stationary clock-JC mutation. Population routes are marginalized, and the tree ends at its sample MRCA.

Unknown or random locus-rate mixtures, sitewise genotype/phase coarsening, alternative substitution channels and relaxed clocks are separate experiments. The channel audit records these distinctions rather than claiming their injectivity from the baseline theorem. Their existence as software options does not delay the stated baseline closure.

The accepted sharp 55-site theorem, equal-rate/full-column-rank theorem, distinct-rate expansion theorem and finite-copy observable-class theorem remain complementary results about stronger or different targets. General demographic realization classification, finite-data accuracy, reliable numerical inference, historical priority, external peer review, complete Lean verification and the original G3/G4 goals retain their separate status.

## Verification

Both the theorem application and source/compiler match have independent written reviews. The exact compiler controls independently reproduced 645 A/B/C/current-lineage checks and 750 bidirectional mirror checks. The channel receipt records eight checked files from pinned BPP4.8.7 source; it is not presented as a rebuild of the historical 2020 executable.

These are complete hand-proof and exact-check records, not a Lean certificate. Original candidate headings in copied providers remain unchanged; their final reviews record acceptance. Historical novelty has not been certified. `MANIFEST.sha256` fixes every public file identity.
