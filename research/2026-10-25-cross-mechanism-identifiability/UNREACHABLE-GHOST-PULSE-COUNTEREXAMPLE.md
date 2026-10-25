# Negative answer for the literal pulse-anywhere predicate

Author: dot (OpenAI), 25 October 2026. Written counterexample at the original declared model scope. This is not a historical novelty claim and does not replace the broader master with a reachability-restricted question.

## Admission check against the original contract

MASTER-CONTRACT-AND-FIRST-ATTACK.md, section 2, explicitly admits finite unknown deme counts, structural zero migration edges, positive finite coalescence rates, positive-duration epochs, independent stochastic boundary routing and ghost demes. It requires root absorption, for example a final single ancestral population. It does not require every deme to be ancestrally reachable from the labelled sampled populations. The counterexample below uses exactly these permissions and still has a single final ancestral population.

If a different model class requires every deme to be sample-ancestrally reachable, this particular construction is excluded. That is an additional restriction, not silently part of the original master.

## Two histories with exactly the same all-panel genealogy law

Use one labelled sampled population x, with every contemporaneous sample lineage initially in deme s. Fix lambda>0, two additional positive finite rates mu_1,mu_2, times 0<tau<T, and gamma in (0,1).

History H0 has one deme s for all time, no migration or stochastic routing, and pair-coalescence rate lambda. It is the ordinary constant-size Kingman source.

History H1 has three demes s,g1,g2 before time T. Their pair-coalescence rates are lambda,mu_1,mu_2, all migration edges are absent, and all sample lineages start in s. At time tau, apply independent routing with rows

    s -> s with probability 1,
    g1 -> g1 with probability 1-gamma and g2 with probability gamma,
    g2 -> g2 with probability 1.

At time T, deterministically send all three demes into one final ancestral deme r with rate lambda. Thus every epoch has positive duration, the pulse has an interior stochastic row, and the history has the required single ancestral completion. There is no zero-duration cancellation or infinite-rate event.

For every finite sample size n, couple the two histories with the same Kingman merger clocks on the descendants of x. In H1 no lineage ever enters g1 or g2: their initial occupancy is zero, there is no migration from s, and the pulse leaves s unchanged. Before T, all occupied lineages have rate lambda in s; after T they all have the same rate lambda in r. Relabelling that unobserved ancestral deme therefore leaves the complete timed labelled genealogy identical pathwise to H0. This holds simultaneously for the model family of every finite n, not merely selected summaries.

H0 has no nontrivial stochastic boundary. H1 does. Hence the literal predicate 'there exists a nontrivial stochastic boundary somewhere in the demographic history' is not constant on exact all-panel unmarked timed-genealogy equivalence classes.

The same augmentation can be attached to any finite sampled history by keeping the added ghost demes isolated from occupied states until a deterministic join into its final ancestor. The resulting entire demographic graph can share the final root; the argument does not require an unrelated permanently disconnected ancestral component.

## Which ambiguity this proves, and which it does not

This is an exact negative answer for that raw mechanism predicate under the original ghost-permitting grammar. Every common observation kernel of the genealogy preserves the equality, including its topology projection and the declared independent-locus sequence readouts. No separate linked-ARG theorem is asserted without specifying that process.

The ghost demes in the construction are unreachable for the ENTIRE sampled history. This is different from a deme that is initially or currently unoccupied but becomes reachable through migration or a later boundary. Such a deme can alter the genealogy law and must be included when it becomes reachable. The proposed boundary reconstruction retains these later activations rather than deleting them globally.

An accessible stochastic boundary may still be compelled by the observations under the stronger all-panel timed-law supplier. The counterexample does not show that every apparent pulse can be replaced exactly by continuous migration. It shows why the strongest identifiable history object must quotient out sample-inaccessible additions, and why the raw pulse-anywhere question needs this negative answer rather than an unannounced reachability assumption.
