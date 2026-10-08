# Actual infinite-iid deterministic stopping bridge

SOURCE/HAND candidate, compiler UNCHECKED and independent primary review pending. This packet is not part of the currently authorized 181-module run. No numerical, symbolic, SDK, API or compiler execution was used.

The prior countable-prefix theorem proves an obstruction for the operational real supremum of finite iid acceptance expectations. This packet connects that quantity to an actual probability measure and a measurable eventual decision event for deterministic rules on finite words.

Let A be a finite alphabet with measurable singletons, and p a PMF on A. The read stream has the constructed probability measure

  μp = Measure.infinitePi (n ↦ p.toMeasure)

on Nat → A. No source-dependent decision coefficients or desired marginal law are supplied as fields. Its finite prefix is the literal coordinate projection stream ↦ (i ↦ stream i.val).

For each n, the canonical equivalence between the subtype Finset.range n and Fin n reindexes the finite product. Mathlib's infinitePi_map_restrict and pi_map_piCongrLeft give the finite product marginal. Equality with the earlier iidPMF is proved on singleton words: both have mass equal to the product of p's masses. The earlier iidPMF_real theorem supplies the product of real masses; both ENNReal sides are finite, so equality of real values implies equality of masses. This also handles n = 0 and zero-mass symbols. The finite measure equality is derived rather than assumed.

A deterministic full-prefix rule assigns keepReading, positive or negative to every finite word. positiveWords n contains words whose FIRST stopping decision is positive at some k ≤ n, with every earlier decision keepReading. Earlier negative decisions cannot be overwritten by later positive outputs. positiveBy n is the literal prefix preimage of that finite word set; eventualPositive is their countable union. Arbitrary memory is allowed through the whole word argument. No stopping bound, expected stopping bound or almost-sure termination assumption is introduced.

Every finite word set is measurable. The prefix projection is measurable, so positiveBy is a measurable cylinder. The existing literal Fin.castLE prefix-extension theorem makes these cylinders nested. Thus eventualPositive is measurable and continuity from below gives

  μp(eventualPositive) = sup_n μp(positiveBy n).

The derived finite marginal identifies each cylinder mass with iidPMF's mass on positiveWords. The PMF integral-of-indicator formula turns its real value into the earlier finite polynomial expectedTest with the constructed 0/1 coefficients. Finiteness of μp permits conversion of the ENNReal supremum to the real supremum. The final identity is therefore

  μp(eventualPositive).toReal = eventualAcceptance p deterministicDecisions.

Substitution into the independently hand-accepted countable-prefix obstruction gives the actual-event deterministic stopping obstruction at or below the same two-radius wrong-closure boundary. The rule is the SAME for all laws. The correct-class eventual-positive lower bound, raw expanded wrong-class upper bound and wrong-closure boundary remain explicit. Those classification assumptions are not an algorithm construction or a biological source-image theorem.

The new proof has 11 written theorem bodies, one probability-instance proof, seven definitions and one abbreviation. The finite index equivalence also has two inverse proof fields. Full ownership, including generated declarations and all definitions, requires a future genuine dependency selection and complete audit; literal prints are not a complete inventory.

Scope limits:

- This bridge concerns a deterministic finite-prefix interpreter on an actual countable iid stream.
- The prior finite independent seed interpreter is preserved, but this packet does not yet identify its weighted supremum with a seed-times-stream product event. Arbitrary measurable independent random seeds remain a separate extension.
- The observer reads one fixed PMF independently at each step. Biology must supply an explicit source–observation contract and justify independence; no dependent or adaptive biological law is inferred.
- Uniform positive recovery, finite-data confidence, effective wrong-law representation/attainment, biological menu/pruning and the full G6 master remain open.
- All reused source drafts remain at their actual hand/source/unchecked status. The old finite-corruption module failed; the separately attributed two-direction derivative supplies only a pending source interface here.

The first decisive check is independent exhaustive source/API review. Compilation can follow only in a separately budgeted complete DAG with a fresh primary selection and root ONE gate, after the current attempt's terminal disposition. No longer job cap or automatic retry is proposed.
