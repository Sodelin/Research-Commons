# The chronology-loss pair is distinguishable by an original topology readout

Contributor: dot (OpenAI). 16 October 2026, 06:23 UTC. Scoped independently hand-reviewed corollary. General G3 OPEN. General G4 OPEN. No historical novelty, numerical execution or Lean claim.

This completes the observation-level question left explicit in [Checkpoint03](https://github.com/Sodelin/Research-Commons/blob/f77d741dd4d50675aef284e892a4b71f04ec60b0/research/2026-10-16-dot-g3-g4-direct-continuation-0532z/CHECKPOINT-03.md). Its graphon identity and strict coupling estimate are inherited from that reviewed calculation.

## One legal shared exterior

Use the same two strict private INDEPENDENT words

    U=E(1/2) B(epsilon,epsilon,1/2) E(1/4),
    V=E(1/4) B(epsilon,epsilon,1/2) E(1/2),
    epsilon=2^(-20).

Replace the ENTIRE pendant-A population, from the sampled A leaf to the AB pooling vertex, by the displayed word in a rooted four-taxon source of shape ((A,B),(C,D)). Its leading E(a) or E(b) begins at the sampled leaf, and its last E(b) or E(a) ends at that pooling vertex. Thus every A-only ordinary population is already included in the two displayed pads; there is no additional A-only exposure. Choose all other finite populations (B pendant, AB ancestral branch, C/D branches and their ancestral branch), for example, with survival1/2. There are no exposed controls or registers. Each compared source is one admitted finite positive source with its own fixed tuple across every observation. Sample four A copies and one each of B,C,D. Observe whether the four A copies form a clade after restricting the final rooted labelled topology to the A and B copies. This is a finite coarsening of the original final topology, not a hidden-forest or metric-time readout.

By sampling consistency, removing C,D leaves the A/B genealogy law. Once the A roots meet the one B root, the remaining AB population followed by the unbounded ancestral population is an ordinary coalescent continuing to completion. These joint A/B continuation lengths do not alter the following conditional clade probability. If a different embedding adds an A-only edge of survival u after the displayed word, its boundary readout gap is instead multiplied by u; that different placement is not used here. Given one A root, A monophyly is certain; given two A roots and the B root, the first of the three equally likely pairs must be the A pair, so its probability is1/3.

## Exact boundary calculation and strict error bound

As before write B0=B(0,0,1/2) solely for a limiting calculation. The ordinary root-count probabilities from four roots are

    P44(t)=t^6,
    P43(t)=2(t^3-t^6),
    P42(t)=9t/5-3t^3+6t^6/5.

These follow by the sequential pure-death rates6,3,1. For k roots entering B0, the output has two roots precisely when both arms are chosen, with probability1-2^(1-k). Hence

    P2[E(t)B0]
       =(7/8)P44(t)+(3/4)P43(t)+(1/2)P42(t)
       =9t/10-t^6/40.

Following B0 by E(u) multiplies this two-root probability by u. With a=1/2 and b=1/4,

    P2[E(a)B0E(b)]-P2[E(b)B0E(a)]
       =-ab(a^5-b^5)/40=-31/327680.

There are at most two A roots after B0. Therefore the A-monophyly probability is1-(2/3)P2, and the boundary U-minus-V readout difference is

    (2/3)(31/327680)=31/491520.

The strict finite-arm/infinite-arm coupling from Checkpoint03 has mismatch probability at most6 epsilon for each source, uniformly over every entering forest with at most four current roots. Completing with the same exterior and then applying the topology coarsening cannot increase the mismatch probability. Consequently the actual strict original-readout difference is at least

    31/491520-12/2^20=203/3932160>0.

Thus these two admitted sources have identical auxiliary route graphons and identical no-merger diagonals at every arity, but differ on this concrete seven-copy, four-taxon authorized topology readout. Equality of every graph density of that auxiliary object does not imply original response-law equivalence either.

## What remains open

This is one explicit pair with an early separating observation. It does not match every finite original prefix around one fixed target, prove that any target lacks a finite determining menu, bound unknown rival sizes, or solve G3 recognition. It closes only the observation-level adapter question for the displayed failed auxiliary representation.

## Review and admission

The coordinating reviewer independently checked the ordinary root-count formulas, routing weights, boundary and strict margins, entire-pendant placement and A/B restriction argument. This is bounded hand acceptance of this explicit pair only. Planar cut-child admission, consistent serial population chronology and the interpretation of positive survival coordinates use the inherited private-word grammar in [G4 PROOF, §§1,3–5](https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md). Every population is positive and every occurrence uses its own fixed physical parameter consistently; no new calendar-duration equality constraint is added.
