# General independent-seed event obstruction

New HAND candidate, independent review pending. This is a separately attributed continuation of the deterministic infinite-iid source draft. No new Lean body, compiler verification or biological applicability is claimed for this addendum.

Fix a finite observation alphabet A. Let (R,Σ,ν) be ANY probability space used as one independent, once-drawn random seed. R need not be finite, countable or discrete; ν may be nonatomic. The same space and law are used for every observed source PMF. The rule

  rule(r,n,w) ∈ {keepReading,positive,negative}

depends on the full finite observed word w ∈ A^n and the seed, never on the source law. Assume, for each finite n,w, that r ↦ rule(r,n,w) is measurable into the discrete three-point signal space. This is an ordinary measurability condition on an interpreter; no conclusion law, acceptance probability, continuity property or desired source factorization is a premise.

Define P_n(w) to be the set of seeds for which the FIRST stopping decision on w is positive by n: there is k ≤ n with rule(r,k,w|k)=positive and all j<k have rule(r,j,w|j)=keepReading. All prefixes are literal initial coordinate restrictions. A prior negative signal prevents later positives from entering this event.

Each P_n(w) is measurable: it is a finite union over k ≤ n of one measurable positive-signal preimage intersected with finitely many measurable keepReading preimages. Put

  d_n(w)=ν(P_n(w)).toReal.

Then 0 ≤ d_n(w) ≤ 1, with the SAME coefficients for every source PMF. No observer law is supplied: these coefficients are constructed from the rule and its fixed independent seed.

For p a PMF on A, construct μp=Measure.infinitePi(i↦p.toMeasure), and use the actual product law ν.prod μp on R × (Nat→A). The deterministic bridge derives the finite prefix marginal of μp as the earlier iidPMF. Independence is the explicit seed/read-stream product construction; there is no re-sampling of the seed and no diploid, biological or dependent-read interpretation.

Let C_n(w) be the stream cylinder with prefix w. The event of a first-positive decision by n is the finite disjoint union

  J_n = union_(w∈A^n) P_n(w) × C_n(w).

The rectangles are disjoint because distinct finite words have disjoint cylinders, even when their seed sets overlap. Each rectangle is measurable. Product measure on rectangles, finite disjoint additivity and the derived iid word marginal give

  (ν.prod μp)(J_n)
    = sum_w ν(P_n(w)) * iidPMF(p,n)(w).

Every factor and summand is finite. Converting this finite sum to real values therefore yields exactly

  (ν.prod μp)(J_n).toReal
    = sum_w iidPMF(p,n)(w).toReal * d_n(w)
    = expectedTest p n d_n.

The order of multiplication changes only by scalar commutativity. This finite rectangle argument avoids assuming a Fubini identity, a regular conditional distribution or seed countability.

Literal prefix nesting proves J_m ⊆ J_n for m ≤ n. Set J=union_n J_n; this is the measurable event that the rule eventually stops positively. There is no bound on the number of reads and no assumption of almost-sure termination. Continuity from below and finiteness of the product probability measure give

  (ν.prod μp)(J).toReal
    = sup_n expectedTest p n d_n
    = eventualAcceptance p d.

Thus the actual-event obstruction holds for every such independent-seed interpreter. If 2α<1, β≥0, every β-corruption of the correct law p has eventual-positive probability at least 1−α, every raw β-corruption of every wrong law has eventual-positive probability at most α, and there exists a wrong-closure law q with TV(p,q)≤2β, a contradiction follows:

1. Pairwise midpoint geometry supplies z within β of p and q.
2. The accepted radial-expansion/closure identity puts z in the TV closure of the raw expanded wrong class.
3. For each n, the constructed source-independent coefficients d_n give the finite continuous polynomial expectation. The sound eventual upper bound implies a bound on every finite expectation on the raw wrong class; continuity extends each bound to z.
4. Taking the countable supremum leaves eventual-positive probability at z at most α.
5. The correct-class lower bound at the SAME z is at least 1−α, contradicting 2α<1.

The closure step acts on finite expectations, so it never assumes that eventual-positive probability is continuous in p. Countable supremums of these functions are lower semicontinuous; that weaker property is sufficient for extending an upper bound from the raw wrong class to its closure. No uniform stopping or expected-time bound is needed.

The SAME proof includes deterministic rules by a one-point seed law and finite-seed rules by their PMF measure. It also covers an infinite random-bit tape as one measurable seed, provided the rule's finite-word signal sections satisfy the stated measurability condition. Adaptive computation after a finite observed word is represented by the rule; the iid observation contract remains explicit.

This HAND result does not supply positive classification/recovery, a native wrong-source image, effective representations, biological read independence or a finished G6 endpoint. The general-seed Lean integration still needs actual measurable finite-section construction, finite disjoint rectangle summation, product finiteness and the source/interface dependency audit. The deterministic source candidate remains unchanged at SHA 03ffdafa53fbd83295362b7d44e5dae03626dba1f60b01d44a3fefdfd948ba06. No current compiler selection is enlarged.
