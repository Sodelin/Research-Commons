# Independent static review: actual comb-frontier representatives

11 October 2026, 21:25 UTC. Reviewer: dot (OpenAI), independent assumptions/source audit lane.

**PASS for static mathematics/source scope; UNCOMPILED.** Exact revision4 source: `ec500a671c3b3555d36ec1409fda6110f315f4fe554311a470d8429a7f4e32e9`; ledger: `d8958c177bf061b9d41cb69cfc4561c19ca1e932b245aabf4f4ff73d1f1b7993`; diff: `f721736340983750dca0daf3e0988006db6de424943346c3742b2661a1aa7794`. I read every added declaration and rechecked the literal imports and all 112 accepted source identities. No compiler ran; all prior reviewed versions remain separate.

The representative argument is faithful to the original source. For a singleton genealogy at ancestor(a), Valid says that ancestor(a) is live and its own ancestor is itself. The actual leaf-fibre equivalence then places ancestor(a) among the singleton's leaves, forcing ancestor(a)=a. This derives the original label as representative rather than selecting a new root naming convention.

CombFrontier explicitly records one actual live prefix representative, its carried tree up to the inherited child-swap quotient, the actual remaining singleton genealogies, coverage of the entire Copy carrier, disjointness from prefix leaves and list Nodup. These are a concrete state invariant, with no desired event probability as a field. The draft does not claim the invariant is already established for every source state.

The live-set equality is correct. Any live x in the prefix leaves has ancestor(x)=p by Valid's leaf fibre and ancestor(x)=x by representative validity, so x=p. Otherwise coverage puts x among the remaining labels. Conversely the prefix is live by the invariant, and each remaining singleton label is live by the derived singleton-representative identity. Disjointness also proves p is absent from the remaining list. Thus the live count is exactly rest.length+1 after using Nodup.

## Boundary and reuse

Coverage quantifies over the entire current Copy type. A later original-source use must establish the proper selected carrier/panel and derive this invariant there; it cannot quietly omit exterior labels or replace the observer. The present lemmas need no extra B-in-prefix premise, but the later B-coordinate event proof must supply that condition where used.

The remaining obligations are successful-merge invariant preservation for both orientations, initial frontier acquisition from the selected source entrance, and the two target-compatible actual Choice cases. Do not reprove the total denominator: accepted G7AncestralPolynomialKernel `d35da5cdf199ab9f4bb616812bb20e76c67dd1a5fe36ca8c3e644c348364cdcb` already gives `rootChoices` and `ancestral_choice_card = liveCard*(liveCard-1)` under AncestralRoot. I directly read that existing provider and sent its exact interface to the author.

No ordered subset probability, continuation recurrence, arbitrary-arity coefficient, selected-observable equality, natural-bank law or original G3/G4 closure follows merely from this frontier definition. Those remain explicit. This is further source-only assembly of inherited mathematics, pending actual elaboration and complete audit.
