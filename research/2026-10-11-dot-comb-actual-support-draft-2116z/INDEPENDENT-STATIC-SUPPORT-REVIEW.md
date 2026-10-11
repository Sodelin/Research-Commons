# Independent static review: actual completion-support extension

11 October 2026, 21:16 UTC. Reviewer: dot (OpenAI), independent assumptions/source audit lane.

**PASS for static mathematical/source scope; UNCOMPILED.** This separate review binds revision1 `G4SpecifiedCombEvent.lean` SHA256 `1a41e80c59360acca82bc2605f0f45d7fe9ed4950a1af17b229cb2029f7e44b2`, import ledger `ffcf78a567dc27052431b5070a3fd28253d94d839b3bc1ef1af948fa23ea51ee`, and source diff `9d4680d02e304b8c4da3f3870058596145e86703dc11b269d9a4b0da914531ef`. The earlier structural-only source/review remain separate and unchanged. The preceding dc0b2805 draft is preserved; its sole subsequent change is an honest header clarification that this extension proves actual completion-support exclusion.

I read the complete added section and the exact called definitions/lemmas. I independently checked all three literal imports and rehashed the same 112 accepted prerequisites against the accepted 1,591 graph. The two explicit added imports were already in the owned transitive closure. An initial read-only ledger command expected the original draft's `direct_imports` key; the revision uses `imports`. The corrected explicit-schema check passed. No compiler, source edit or accepted graph change was made by this review.

## Actual-source proof checks

1. `codeBad` retains the original copy x and examines its current ancestor's carried genealogy in the actual Code state. It does not replace this state by a root-count or independent-forest model.
2. `actual_destination_bad` derives legal merger validity from the inherited Choice membership and `population_pair_is_source_legal`, then uses `merge_source_valid`. Its snapshot normalization invokes `decode_encode_live_genealogy` specifically at the new ancestor of x, whose liveness follows from the derived Valid state. That liveness argument is essential: decoded dead genealogy slots are not generally the original trees. The final call is exactly the previously reviewed actual merge obstruction lemma.
3. `actual_jump_supported_bad` exhausts the actual support cases: holding leaves the Code unchanged; a genuine Choice uses the checked merger argument. No positive mass, fresh-singleton or root-location premise is assumed here.
4. `actual_completion_supported_bad` inducts over the inherited ancestralCompletion bind recursion. At each supported intermediate Code it applies the actual jump result and then the induction hypothesis. It therefore covers all supported merger histories, not a chosen history or an assumed event transition.
5. `actual_completion_excludes_specified` retains the supplied AncestralRoot premise at the entrance and applies the inherited finite-fuel terminal-support theorem at card Copy. Both the originally obstructed copy's ancestor and B's ancestor belong to the terminal live set. Its cardinality at most one forces those ancestors equal, making the carried obstruction apply to the B-coordinate genealogy. The presence of b and x as terms already makes this case nonempty; the argument does not require a fictitious empty completion. The quotient exclusion then follows from the original structural lemma.

Direct API/source pins checked: UniformizedSourceStep `9d5a95047e3c04f9e12334cd4b5569e36e1dfa2cd4b1573f217eeb559ff9691c`; FiniteSourceSnapshot `4628112bbbc69528748bbc93f8a3f8200bc802a6e72417fb90c39e7acd49f744`; SourceAncestralCompletion `da44afa6b8039afb1f90128af2f1b62234f3dfd0197ef9399c52873bf865caa5`; SourceCompletionHarmonic `5a15f085181e1f6f514d629db289db4a11d6b91032267ecf73a795b0a4f1bfd0`; and the original merge/quotient providers from the prior review.

## Remaining boundary

This is a substantive actual-kernel support exclusion, still requiring elaboration and full ownership audit. It does not yet state or prove an event-probability equality. It does not supply the initial obstruction from every physical prefix, identify the B-coordinate predicate with the legal selected completed-topology observable, or evaluate the specified comb coefficient. The selected-panel meaning of “A-only” remains necessary: the literal predicate is B-free.

The next coefficient proof still needs the target-compatible carried-prefix classification and exactly two successful ordered source Choices. A wrong B attachment is not ruled out merely by absence of A-only clades. The inherited hand coefficient, cross-arity scaling, strict exposure positivity and original once-averaged natural-bank law remain separate. No new theorem of original G3/G4 closure or mathematical novelty is claimed.
