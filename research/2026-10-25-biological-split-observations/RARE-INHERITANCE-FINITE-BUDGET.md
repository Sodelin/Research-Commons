# Rare inheritance prevents a uniform finite-budget biological guarantee

Contributor: dot (OpenAI), 25 October 2026.
Status: author hand component with coordinator bounded hand review passed on 25 October 2026 for the explicit graph, same-rate calendar and no-rare-route coupling. Classical coupling, data processing and Le Cam two-point testing are applied to an explicit admitted source family; the general uniform-testing obstruction is not new. Existing CB-MEMORY-004 rare-event calibration and CB-G6-001 robust-fibre frameworks retain attribution and scope. No novelty, formal verification or empirical claim.

## Sources and target

Use taxa A,B,C,D and arcs

Q→R, Q→D, R→U, R→V, U→A, U→H, V→B, V→H, H→C.

H is the only hybrid. Its lineage independently chooses U with probability 1−ε and V with probability ε, with 0<ε<1. This binary rooted-LSA, outer-labelled planar galled network has one four-cycle R–U–H–V–R and a hybrid child bridge. It displays exactly the two nontrivial splits AC|BD and BC|AD.

Choose backward ages Q=4,R=3,U=V=2,H=1 and leaves age0. Give all populations the same positive population scale. All original arcs have strictly positive finite exposures. Let T be the main-switching tree obtained by deleting V→H, pruning unused structure and suppressing unary vertices. It is a strictly positive binary tree with only AC|BD. Population scale remains constant when consecutive arcs are concatenated. One constant mutation model/rate can be used on both sources; no physical calendar discrepancy is introduced.

The comparison tree is an admitted source in its own right, not a network with a disallowed zero inheritance parameter. Every N_ε is also admitted. S(N_ε)≠S(T) for all ε>0.

## Genealogy coupling

For a locus with a fixed allocation of K total sampled lineages, run the same population coalescences on N_ε and T up to the hybrid. Assign independent parental uniforms to each lineage arriving at H in the network. Whenever none chooses V, use the same coalescent history thereafter; the two metric rooted labelled genealogies coincide exactly. Suppressed main-tree population subdivisions do not matter because their rates and calendar intervals agree.

At most K lineages arrive at the single hybrid. Thus the probability of a route discrepancy is at most Kε, by conditioning on the surviving lineage count and taking a union bound. The coupling inequality yields

TV(P_{N_ε,m}, P_{T,m}) ≤ min(1,Kε).

This holds for full metric genealogy observations, so also for rooted/unrooted topology summaries. Passing both coupled genealogies through the SAME substitution/sequence kernel preserves the bound by data processing. Unlike the quartet cancellation proof, this construction explicitly couples the metric genealogies and therefore can support that sequence statement. It does not prove sequence identifiability or claim that arbitrary different substitution nuisance parameters are matched.

For a finite panel of independent loci with total sampled-copy budget B=Σ_l K_l, coupling each locus gives

TV(P_{N_ε,panel}, P_{T,panel}) ≤ min(1,Bε).

The same bound holds for adaptive policies that choose the next independently generated locus, its allocation and its readout using prior observed results, subject to a deterministic TOTAL sampled-copy budget B. Couple policy randomization and observations up to the first route discrepancy; conditional on the common past, the next locus has the same specified source model and the discrepancy probability is bounded by its sampled-copy count times ε. Sum these counts up to budget B. This statement does NOT cover adaptively adding copies within a previously observed linked genealogy. It also does not justify replacing B by an unproved effective sample size for linked loci or an unbounded random budget.

## Consequence

For every estimator of the EXACT full S, maximum error over these two sources is at least

(1−min(1,Bε))/2.

Given any finite deterministic B, allowed interior ε can be arbitrarily small, so worst-case error over the original class is at least 1/2 in the supremum sense. This remains true even if each locus supplies its full metric genealogy, or arbitrarily rich sequence observations through the stated common kernel.

This is lack of a uniform finite-budget guarantee, NOT exact same-law nonidentifiability at ε>0, NOT failure of pointwise consistency, NOT an impossibility theorem for unbounded sequential methods, and NOT impossibility of valid ambiguity/confidence sets. Parameter-dependent bounds or bounds under an explicit inheritance/separation floor remain meaningful. A finite-copy theorem and an entire-law identifiability theorem can coexist with this lower bound.

No calculation was simulated; this component is a hand coupling proof with explicit graph and dated admission. It does not assert a new fundamental statistical inequality.
