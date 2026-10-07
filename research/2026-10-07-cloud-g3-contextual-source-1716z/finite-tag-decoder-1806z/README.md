# Finite tags on the source's actual labelled binary tree

Contributor: Codex, delegated G3/source-bridge lane, 7 October 2026, 18:06 UTC. Resume baseline main `2a9af728e9c8e7ba0802e703ec1b51150c8370d0`. **New hand proposition pending independent review; Lean derivative UNCHECKED.** No compiler or source replay has run on this contribution.

The [hand proposition and proof](PROPOSITION-AND-PROOF.md) gives the exact bridge `decodeTags(bin ∘ pairAge)=mapBinDecoration` on an actual well-labelled tree. It uses the existing reviewed real-age decoder and exactly its genuine cross-child witnesses. Repeated bin tags retain every binary graft and original leaf label.

[FiniteTagDecoder.lean](FiniteTagDecoder.lean) is a separately owned standalone derivative with imports `G2FaithfulPairAgeDecoration` and `UnifiedLean.Source.UnrankedGenealogyObservation`. It defines fixed-tree finite tag decorations, pointwise binning, decoding, and explicit tagged-tree child-swap transport. Its module dependencies are pinned in [SOURCE-INPUTS.json](SOURCE-INPUTS.json). This packet is not a standalone build closure; the compiler owner must provide the authenticated imports in a separate pinned build.

The primary new statements are `CloudG3.FiniteTagDecoder.decodeTags_map_decode`, `decodeTags_bin_pairAge`, and `decodeTags_bin_of_pair_agreement`. The first is a structural identity for every matrix; the actual-tree statements use the existing PROVED age decoder inverse rather than assume tag correctness. The additional `underlying_toTaggedTree` and `underlying_mapTags` identities preserve exact binary topology. `mapTags_respects` transports arbitrary decorated child swaps; `actual_decoder_unordered` consumes actual age-decorated representatives.

For arbitrary tag matrices, `decodedTaggedTree_graft_swap` has the necessary selected-entry equality. An arbitrary symmetric matrix still fails under nested swaps when an ancestor's witness changes; the hand note gives a concrete counterexample. Actual pair-age agreement excludes it. No general arbitrary-matrix quotient theorem is claimed.

The derivative defines a finite product instance for each fixed tree when Tag is finite. Whole copy-capped tagged-tree/forest enumeration, selected-label pruning, measurable binning, actual source history attachment and final probability consumers remain separate. Original G3 exact recognition and the full connected G6 endpoint remain open. The parent owns the actual timed-bin history route, and the sole Lean lane owns any future bounded compilation.
