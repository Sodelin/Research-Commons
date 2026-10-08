# Original network to law-level quartet recurrence and actual count

Cloud G3 lane, 8 October 2026. **New explicit hand adapter, review pending.** This is source-faithful reuse and composition of already accepted ingredients, not a new discovery of the all-core ancestry reduction. The accompanying graph-count Lean file is compiler UNCHECKED; it does not prove the source-to-word law equality.

## 1. Exact original source and output

Let N be one ORIGINAL admitted finite binary rooted-LSA, outer-labelled planar, cut-child source graph. Original edges have their own IDs, so parallel arm occurrences remain distinct. The actual graph is rooted and directed acyclic. Root degree is `(0,2)`, ordinary internal degree `(1,2)`, hybrid degree `(2,1)`, and taxon leaf degree `(1,0)`. Every hybrid's actual unique child occurrence is an underlying bridge. The full source has at least four taxa, arbitrary finite blob/hybrid count, strictly positive finite physical population lengths/rates and strictly interior original inheritance probabilities. The original root is not replaced. One unbounded ordinary ancestral population completes the genealogy above it.

Use the natural INDEPENDENT row: at each actual original hybrid, each currently surviving ancestral root receives one fresh parental choice with the same original site probability. A previously grafted subtree remains one opaque current root. No forcing/conditioning, hidden correlated lineage environment, parameter substitution, extra observation, or sample ascertainment is introduced.

Sample four labelled copies `a1,a2,a3,a4` at taxon A and one at each of three other distinct taxa B,C,D, as in the accepted original passive quartet contract. Observe only the final rooted labelled unranked genealogy restricted to the four A labels, suppressing unary nodes. This is the same permitted finite coarsening. Ordinary pair ages, route flags, intermediate forest states and population owners are not observed.

Write `mu_N` for this actual fifteen-outcome observation PMF, and

    t_N = mu_N{balanced quartet outcomes} - 1/3.

This is an expectation under the actual complete natural source law. It is not an input entering PMF or a desired law supplied as a premise.

## 2. Actual focal vertices and deterministic structural count

In the inherited raw edge-indexed source notation, define

    HybridSet(N) = {h in V : N.graph.IsHybrid h},
    FocalSet(N,A) = {h in HybridSet(N) : N.graph.DReach h (N.leaf A)},
    H = #HybridSet(N),    n = #FocalSet(N,A).

These are actual vertices, not routing coins, merger events, uniformization holding counts or fitted latent states. The inclusion `FocalSet subset HybridSet` gives `n<=H` without any topology or law hypothesis. This is exactly the limited conclusion of [ActualFocalHybridCount.lean](ActualFocalHybridCount.lean).

Finiteness alone does NOT order these vertices into a source word. The following separate structural derivation uses the original cut-child source contract and the [accepted all-core ancestry proof](../2026-10-06-dot-g3-original-quartet-whole-fibre-no-0454z/PROOF.md), Section 2.

For every focal hybrid h, its child bridge e is crossed by every root-to-A directed path. The root is on e's h side: a root-to-h directed path could not cross e backwards; crossing e forward and returning to h would contradict the bridge and directed acyclicity. Since h has only that child, A lies on its descendant side. Removing e therefore separates the root from A and makes h a dominator of A.

The underlying bridge/component quotient is a tree. Every focal child bridge lies on its unique root-component-to-A-component path. Those occurrences are linearly ordered from A toward the root. A component on that path has only one exit toward A. Two distinct focal hybrids in the same component would have distinct child occurrences and thus two such exits, impossible. This reasoning allows the ORIGINAL component to contain other hybrids: their child bridges exit to different descendant components, and those hybrids are not focal. No claim that the full network is level 1 is made.

Delete vertices/edges not ancestral to A only as a proof operation on the selected marginal. In a contributing component exactly one hybrid remains. Its two actual incoming occurrences extend backwards through ordinary vertices, each of indegree one, until they first meet at one ordinary split. A further split followed by a second merge would require another retained indegree-two vertex; that would be another focal hybrid in the same component. Consequently the retained component consists of precisely two original ordinary parent paths from that split to h. Ordinary side branches without a directed path to A disappear. Suppression groups the serial ordinary edge occurrences along each arm. Parallel occurrences are never identified with each other.

Each focal hybrid therefore supplies one two-arm factor B, and every B has one focal hybrid owner. Sorting by the bridge path gives a deterministic list `h1,...,hn` with no repetitions, whose set is EXACTLY FocalSet(N,A). The number of hybrid factors is n, independent of realized routing/coalescence histories. Every selected block's backwards route crosses these dominating sites once; directed acyclicity prevents return to a site. Several current roots at one site still form ONE whole-forest hybrid factor, not several graph hybrids.

The original pendant population below the first split is a genuine strictly positive leading ordinary block. Ordinary connectors between contributing components are grouped similarly. Any ordinary segment above the last component is retained; it may be empty if that component's split is the original root. The unbounded ancestral completion remains the completion readout. Thus the derived structural word has the form

    W_N = E(z0) B1 E(z1) ... Bn E(zn),                  (1)

with `0<z0<1`, positive finite arm lengths and connector lengths inherited from the actual graph, and `0<zi<=1` for grouped ordinary blocks; `zi=1` records an empty grouped block, not an invented positive physical edge. Splitting or merging adjacent ordinary blocks does not affect n. The zero-focal-hybrid case is an ordinary path followed by the same original completion.

## 3. Actual history law identifies this structural word

The accepted graph ancestry statement has a substantive probability gate. It is not supplied by the finite set/count lemma, nor by separately multiplying averaged branch marginals.

The actual complete same-source pruning theorem

    SourceUnrankedCopyProjectivity.actual_complete_unranked_copy_projectivity

compares the full natural completed source with the true selected-copy source on its smaller carrier, retaining the SAME original graph, calendar, rates, probabilities and natural register. Its source equality is proved rather than assumed. Its original-label lift adds only relabeling through the original copy injection, with the same unordered binary child-swap quotient. In the present application keep is exactly the four A labels and `common` is constantly false. This reduces the full seven-copy observation to the independently initialized four-copy source on the SAME graph, not to an arbitrary externally supplied quartet PMF.

There are two precise local semantics behind that theorem:

1. `SourceForestSilentPruning.selectedView_merge_silent` proves that a legal merger with at most one visible selected operand leaves the full selected pruned genealogy, original population and register view unchanged. Its `silent_merger_readout_increment_zero` is derived from the actual source operation. A merger with an unselected B/C/D lineage therefore does not split the A subtree into new independent tips.
2. `SourceForestPulseMeasure.actual_original_hybrid_pulse_projectivity` starts with the actual Bernoulli product on live original owners at an original hybrid, restricts it through the proved visible-owner/current-block equivalence, and obtains the natural selected-current-root output law. Already merged selected tips get ONE current-root coin. Extra original owners' coins are marginalized, not replaced by fitted probabilities or redrawn after observing the past.

These gates justify discarding nonfocal branches for the selected law. An A-carrying ancestor always remains on a directed path to A; a hybrid outside FocalSet cannot become a new visited site merely because an unselected block merged with it. The entire larger source and its other taxa/root remain physically present. The deletion is a projective proof of an observation equality, not a new one-leaf admitted network.

On each retained ordinary path, source coalescent semigroup composition combines the actual positive finite coalescent lengths. In physical calendar/rate notation an arm's total length is the sum of its original positive `rate(edge)*duration(edge)` terms; its pair survival is the product of the corresponding exponentials. Original labelled genealogy subtrees are grafted throughout. For an entire arm path this is exactly the actual ordinary forest kernel `E(x)` with `0<x<1`; an ordinary connector is `E(z)`. This equality concerns the unranked genealogy law. It does not claim that suppression preserves the original event ages or timed observation law.

At each retained h the original parent registry fixes the orientation of the two actual incoming occurrences and the original natural p. Current roots independently choose those arms; their ordinary processes evolve conditionally on that JOINT routing allocation, and their forests pool at the actual common split. The original full-forest compiler sums these correlated histories with each routing draw and edge transition weighted once. It gives exactly `B(x,y,p)` on every finite entering selected forest, retaining opaque old subtrees. No independent product of separately averaged arm/branch outcomes is substituted.

Composing these actual kernels in the deterministic order (1), with the original root completion, therefore yields the exact original-label fifteen-outcome equality

    mu_N = completedQuartetLaw(W_N).                    (2)

Equation (2) follows from the accepted original source reduction, ordinary semigroup/grouping, and actual selected-current-root projection. It is not a field of a new structure or an assumed target-preserving map. Source parameter ties, new controls or richer readouts are not discarded under this equality: they are absent from this declared passive row. An arbitrary raw `RootedBinary` value without the full original source and cut-child assumptions does NOT obtain (1) or (2) from our cardinality draft.

## 4. Which history sum obeys the scalar recurrence

For a factor K, let `c(K)` be its actual probability that four distinct entering selected roots undergo no selected merger through K. Let `T(K)` be balanced completed-quartet probability minus 1/3. The [accepted chronological cocycle](../2026-10-06-dot-g3-independent-quartet-topology-invariant-0403z/PROOF.md), Section 3, derives

    T(KL)=T(K)+c(K)T(L).                                (3)

The derivation partitions the original prefix histories, with their unnormalized probabilities, by their selected root count. On the four-root event, no selected tip has merged; the future actual current-root kernel and fresh site/holding randomness give the change T(L). On the three-root event, one opaque cherry and two singletons are exchangeable as CURRENT roots under L plus ordinary completion. Its three possible rooted current-root resolutions are equiprobable; only one gives the balanced four-tip shape, so the balanced probability stays 1/3. With two roots, the existing 2+2 or 3+1 subtrees already determine balanced/caterpillar shape; with one root, the topology is fixed. These latter branches contribute zero change.

The actual history weights in all branches are summed; no success event, routing event, positive fibre or survival event is used to renormalize the source. Zero-mass branches contribute zero. History multiplicity, finite within-edge mergers and their continuous holding times are integrated by the original forest kernels. Uniformization holding counts, literal-clock budget failures and posterior states are not substituted for graph hybrid counts.

Let m be the already accepted minimum discounted reward, `b=-m>=4/27`, and `a=13/256`. For each hybrid factor define `e=T+b(1-c)`. The accepted source inequalities imply `e>=0`, and the corrected complete-cube cell minimum gives `e+cb=T+b>=ab`. For an ordinary block `T=0`, `e=b(1-c)` and `0<=c<=1`. Equation (3) gives the exact law-level reverse recurrence

    Gempty=b,
    Gprepend=e+c Gtail,     G=T+b.                      (4)

This discharges each scalar premise of the [separate unchecked core](../2026-10-08-cloud-g3-hybrid-scalar-lean-0234z/HybridSizeCore.lean) by an actual source ingredient: original no-merger nonnegativity; signed minimum residual; complete-cube cell bound; and exact current-root cocycle. The scalar source code is not used as a compiled provider in this packet.

Every hybrid prepend raises the exponent k by one. An ordinary block preserves the same k. Induction over the FULL factor list, including leading and intervening ordinary blocks, therefore yields

    t_N-m >= b a^n >= b a^H >= (4/27)(13/256)^H.         (5)

Positive tails are included: the hybrid step uses `Gtail>=b a^k` and `e>=0`, not an upper bound `Gtail<=b`. Arbitrarily long finite ordinary blocks are included. The original unbounded completion is the readout defining T, not an additional finite factor assigned zero c.

When n=0, the actual four-A-copy genealogy is ordinary Kingman and `t_N=0`; hence `G=b`. When H>n, unused/outside hybrids merely weaken `a^n` to `a^H`; no runtime history count or revised graph is substituted. When selected copies have already coalesced, the subsequent factor still occurs in the deterministic whole-forest word and preserves their opaque genealogy, so a random early-completion event never shortens the deterministic induction length.

## 5. A false pathwise extension and exact scope

For a single completed sampled history omega the observable centered indicator is

    J(omega)=1{balanced}-1/3,

which takes values `2/3` and `-1/3`. It does NOT obey (5) history by history. An actual positive ordinary four-taxon tree has H=0, but its selected quartet is a caterpillar with probability 2/3, giving `J=-1/3<0`. The H=0 law bound requires the expectation `t_N=0`, not `J>=0`. This is a source-admitted counterexample to the pathwise reading of the recurrence.

Thus the contract concerns the actual complete natural observation law, not each raw marked trace, a supplied abstract entering distribution, a conditional source given survival, or separately fitted rows. It applies to the stated passive all-A-copy quartet coarsening in the original positive INDEPENDENT cut-child class, with its permitted topology readout and original branch/root conditions. Arbitrary retained copied taxa, uncoarsened seven-copy law, controls, COMMON/posterior coupling, timed bins, physical old decoration and cross-graph transport remain separate. General coupled G3 remains OPEN.

## 6. Formal and provenance boundary

The accompanying Lean file has four definitions and four theorem bodies using the ACTUAL inherited `RootedBinary`, `IsHybrid`, `DReach` and leaf embedding. It proves actual focal-set membership, inclusion and the true graph count inequality without a supplied chain, injection or desired law premise. It is compiler UNCHECKED and changes no original/provider/build source.

The full ordered factor-list construction, exact original-source equality (2), and its attachment to the scalar code remain hand-level consumers. The inherited actual projectivity/pruning/pulse theorem bodies exist, but their existence does not automatically compile the new graph suppression/serialization theorem. No `ChainCertificate` structure is introduced with (2) as an assumed field. Formalizing that original graph-to-word equality is the precise next consumer gate; the cardinality file alone does not discharge it.

Credit: Dot's accepted all-core ancestry/cocycle and actual source projection/pruning/pulse developments; Astra's original positive graph/bridge compiler; the accepted corrected size-frontier proof; standard coalescent semigroup/projectivity and elementary finite set counting. This contribution exposes and connects the source/count obligations for a later formal consumer. Historical novelty is unresolved. No compiler, source simulation, arithmetic control, source enumeration or QE ran.
