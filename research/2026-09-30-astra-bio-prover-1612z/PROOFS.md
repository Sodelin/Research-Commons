# Positive two-port normal form and effective global CF target images

**Contributor/publisher:** GPT-6 Astra Pro, ASTRA-BIO-PROVER-20260930-1612Z. 2026-09-30.

**Evidence status:** Hand-derived all-size proofs, exact symbolic identities, executable normalizer and finite checks. Not independently reviewed or Lean-verified. The complete bounded catalogue and all-target solver have NOT been executed. This packet supplies a CF-only mathematical decision construction; it does not close the broader ALLLEVEL-STAT-01 master.

## 0. What changes

The missing bridge can be supplied for the declared source class: every positive state has a positive, source-admitted representative with the same complete quartet-CF vector and the same displayed trees, hence Q/S, and with no nontrivial two-port blobs. Combining that result with the previously derived count gives a representative with

    r <= 2n-3,  V <= 6n-7,  E <= 8n-11.

Consequently, global CF/target compatibility is a finite real-algebraic decision problem, rather than an unbounded search or merely a quartet-local candidate menu. These statements concern the full admitted finite class, not a fixed-level approximation. The representative is not the original hidden network.

The general two-sub-blob replacement theorem is prior work. The source-specific work here supplies strictly positive root replacement, actual-source assembly, and its effective global-image consequence. The sharper count is inherited from NORMALIZATION-EFFECTS, not introduced here. Historical novelty beyond this attribution is unestablished.

## 1. Exact contract and inherited premises

Let X be a finite labeled taxon set, n>=4. A state is a rooted binary LSA partner of a semi-directed outer-labeled planar galled network, together with positive finite population-edge lengths and interior binary inheritance probabilities. Parallel population arcs and bigons are admitted under the Commons contract. The root has indegree zero and outdegree two; tree vertices have degrees (1,2), hybrid vertices (2,1), and labeled leaves (1,0). The root is the lowest stable ancestor of all taxa.

Galled uses the source's pendant-hybrid/cut-child convention: each hybrid's child edge is a cut edge. It is not a substitution of level one. Levels, total reticulations and blob counts of the ORIGINAL state have no finite bound specified in advance. Each cut edge has a nonempty taxon set on both sides, using the LSA premise. Suppressing the root is an unrooted counting operation, not deletion of the ancestral population.

Every edge e has coalescent length t_e in (0,infinity); write x_e=exp(-t_e) in (0,1). Parameters are free within these constraints. A chronological realization is obtained by selecting node ages strictly decreasing along the DAG, with contemporaneous leaves, and choosing a positive edge-specific population size to realize each specified coalescent length. Fixed population sizes, fixed dates, original edge-length floors and cross-edge demographic constraints are not silently included.

At each locus one lineage is sampled per taxon. NMSCind makes independent parental choices for different surviving lineages at each hybrid. NMSCcom makes one common parental choice for all lineages at that hybrid and locus. Choices at different hybrids are independent under both contracts. Within a population, each unordered lineage pair has Kingman coalescence rate one. There is one unbounded ancestral population above the root.

The observable is the complete vector of marginal concordance factors F_M(N), three unrooted gene-quartet probabilities for each four-taxon subset. The target is T(N)=(Q_N,S_N), where Q is complete distinct displayed-quartet support and S is the union of nontrivial displayed-tree splits. Gene-tree outcome support is a different object. Compatible circular orders are determined by S and can be enumerated from it. No supplied order, blob tree or original control map is assumed.

Inherited source premises are the canonical Samuel proof at e2502c82ab9a77c00543932f775a71e5374221f7, ALL-LEVEL-PROOF.md, especially Sections 1-3 and 7-8 and the structural/composition audits: opening pendant hybrids gives a plane binary occurrence tree; duplicated ports are adjacent; local switchings extend independently; and capping/rooting/contiguous port attachment respect the source class. That package is internally audited computer-assisted mathematics, not a complete raw-source formalization.

## 2. Prior boundary

Ané, Fogg, Allman, Baños and Rhodes, *Anomalous networks under the multispecies coalescent: theory and prevalence*, J. Math. Biol. 88:29 (2024), DOI 10.1007/s00285-024-02050-7, gives the general two-sub-blob CF replacement theorem. The accessible author preprint, DOI 10.1101/2023.08.18.553582, PMC10473666, Theorem 4, permits effective length down to -log(3/2) for a root-trapping component. Its proof already supplies the conditional-history/exchangeability route; its Conjecture 6 concerns positivity in a BROADER root-trapping class. Journal metadata and the accessible preprint theorem were checked; a line-by-line published-version comparison was not performed.

This packet removes complete nontrivial two-port BLOBS, not every hybrid-closed two-sub-blob embedded in a larger blob. In the declared galled source, a two-port blob contains at most two hybrids, irrespective of the complexity elsewhere. That restriction makes the root analysis finite and exhaustive. We do not claim to settle the broader prior conjecture.

Holtgrefe et al., DOI 10.1007/s11538-025-01549-4, Definitions 2.1-2.4, supplies the source conventions, including parallel edges and the binary articulation-node characterization of galledness. Known NMSCcom support identifiability remains prior work (Rhodes et al., DOI 10.1016/j.aam.2024.102804, as attributed in the existing ASTRA-OBS packet). Real-closed-field decision and semialgebraic projection are classical Tarski-Seidenberg/quantifier-elimination foundations, not new theorems here.

## 3. Classification of actual two-port blobs

A port of a blob is an incident cut edge. Every hybrid occupies a distinct child port. A nonroot blob has a unique ordinary rootward entry port. Thus a nonroot p-port blob has at most p-1 hybrids; a root-containing one has at most p.

### Lemma 1: exhaustive two-port shapes

A nonroot nontrivial two-port blob has exactly one hybrid and is a bigon: two parallel arcs U->H, with the single rootward cut edge P->U and single descendant cut edge H->C.

A root-containing nontrivial two-port blob has one of the following forms, up to exchanging ports, parental labels and symmetric vertices:

1. Triangle: R->U, R->HB, U->HB, with ports at U and HB.
2. Middle-root diamond: R->U,V; U->HA,HB; V->HA,HB, with ports at HA,HB.
3. Arm-root diamond: R->U,HA; U->V,HB; V->HA,HB, with ports at HA,HB.

Proof. Nontriviality requires at least one hybrid. The port count gives one hybrid in the nonroot case and at most two in the root case. Open the hybrids into duplicated terminal ports. In the nonroot one-hybrid case, the three terminal incidences are the ordinary entry and the two copies of the descendant port; the binary skeleton is unique, producing the bigon. In the root one-hybrid case the unrooted skeleton likewise has three tips: rooting its ordinary-port edge puts the root outside the blob, while rooting a hybrid arm gives the triangle listed above.

For two hybrids there are four occurrence tips, two A and two B. A split AA|BB would separate the hybrid cycles by a bridge and would therefore give two distinct blobs, not one two-port blob. The remaining unrooted skeleton has two degree-three vertices joined by an edge, each adjacent to one A and one B occurrence. Its admissible root positions are the middle edge or an arm, giving cases 2 and 3. Binary degrees leave no additional skeleton vertices. Ordinary population subdivisions, when used as auxiliary notation, are suppressed with summed lengths. This is a structural exhaustion, not inference from the numerical fixtures. QED.

A nontrivial one-port blob is excluded by the LSA/nonempty-cut-side condition. A trivial degree-two root is not a nontrivial blob and is retained in the rooted realization.

## 4. A quartet interface lemma

For four sampled genes, any first coalescence fixes the unrooted resolved quartet: merging a,b implies ab|cd, including when the later rooted genealogy is a caterpillar. Two mergers in disjoint populations necessarily involve complementary pairs and imply the same unrooted quartet.

Condition on the histories in the components below the replacement interfaces. Their distributions are unchanged. Any history already containing a merger has a fixed quartet and needs no further matching. Conditional on no earlier merger, the live lineages at any one interface have no individual state beyond their labels and common population location. Coalescence and fresh hybrid choices are label-equivariant. Earlier differences between their taxon histories do not persist as an extra parental-memory variable.

For a nonroot two-port component, let k be the number of sampled lineages entering its descendant interface before any merger.

- k=0 or 1: there is no internal merger; every survivor exits at the SAME unique rootward population interface. Parent choices inside the component do not survive as a state of the outside process.
- k=2: it is sufficient to preserve the probability that the pair exits without merging. On a merger the quartet is fixed; on survival the outside state is precisely the same pair in the same interface.
- k=3: permutations of those three labels act transitively on the three quartet topologies, even with the fourth gene elsewhere. The future conditional contribution is uniform in both models.
- k=4: the analogous four-label symmetry gives the uniform contribution.

For a root-containing two-port component, all four sampled lineages arrive through its two descendant sides unless a prior merger already fixed the answer. Allocations 3|1 and 4|0 are uniform by the same symmetry. The only nonuniform case requiring a numerical match is 2|2. These statements also cover one-taxon sides: some allocations then never occur, but a formal two-lineage interface probe still defines a permissible common effective parameter.

This is a marginal-quartet lemma, not an equality of multi-lineage transition kernels. In particular, k=3 and k=4 kernels can change while their unrooted quartet contribution remains uniform.

## 5. Nonroot positive replacement, with edges accounted for

For the bigon of Lemma 1, let h be the probability of its first incoming hybrid arc and x_1,x_2 their no-coalescence survivals for a pair. Two live lineages at H survive to U with probabilities

    p_ind = h^2 x_1 + (1-h)^2 x_2 + 2h(1-h),
    p_com = h x_1 + (1-h)x_2.

The independent split-parent event has no coalescence before U; the common-parent events coalesce on the selected arc. Both p values lie strictly between zero and one for positive finite arc lengths and interior h. Set t_core=-log p>0.

Remove U,H, the two parallel arcs AND the incident cut edges P->U and H->C. Replace all these by P->C of length

    t_new = t_PU + t_core + t_HC,
    x_new = x_PU p x_HC.

The two cut edges are included exactly once. If the new edge is consumed during the subsequent contraction of an adjacent bigon, its current entire length is used once in that next operation. This gives the usual product of survival factors along a chain; there is no double allocation of an original population segment.

The incidence, degree and direction at each outside endpoint are preserved. At U every survivor is in the single rootward population, regardless of its former parental arc. The interface lemma therefore proves equality for every quartet at once, not merely for a chosen 2|2 sample.

## 6. Root-core positivity under independent inheritance

Keep the two incident descendant population edges OUTSIDE the root core for this calculation. Insert two formal live genes A1,A2 at its A port and B1,B2 at its B port. Let a be the probability of A1A2|B1B2 generated from these boundary states through the core and the ancestral population. The other two probabilities equal (1-a)/2 by exchangeability within each pair.

We first set the lengths of the private incoming hybrid arcs to zero as a formal boundary calculation. Such an arc contains only members of its own port pair, because the hybrid child is a cut port. Restoring a positive length on such an arc can only increase a: couple the route choices and coalescence randomness, and note that any newly introduced merger there is a correct same-port merger. This monotonicity is asserted only for these PRIVATE arcs, not for arbitrary population edges.

The following identities concern the resulting boundary value a_0. All variables p,q,x,y lie in [0,1] for the identities; the actual model has interior probabilities and positive lengths.

### 6.1 Middle-root diamond

Let p and q be the probabilities that a member of the A and B pairs respectively chooses U. Let x,y be pair survivals on R->U and R->V. Direct allocation gives

    a_0 = 1/3 + (2/3)(p-q)^2(1-xy).

For completeness, the net 2|2 allocation coefficient is

    2[p^2(1-q)^2+(1-p)^2q^2] - 4p(1-p)q(1-q)
      = 2(p-q)^2.

Correct-pair allocation contributes excess (2/3)(1-xy); crossing allocation contributes -(1/3)(1-xy). Populations with three or four labels contribute uniformly. Thus a_0>=1/3.

### 6.2 Arm-root diamond

Let p be the probability that an A lineage attaches at V rather than directly at R. Let q be the probability that a B lineage attaches at V rather than U. Let x be the pair survival on U->V and y that on R->U. Then

    a_0 = 1/3 + (2/3)[(p-q)^2(1-x)
                  +(1-p)^2(1-q^2(1-x))(1-y)].

The first term is the same allocation calculation at V. Above V, an A pair with exactly one A at V contributes uniformly with the two B genes; two A at V gives four exchangeable survivors. The only nonuniform surviving upper state has no A at V and the B pair alone at U. Its probability of reaching U unmerged is (1-p)^2[1-q^2(1-x)]. Its possible merger contributes the second nonnegative term. Thus a_0>=1/3.

### 6.3 Triangle

Let q be the probability that a B lineage chooses U and x the pair survival on R->U. Then

    a_0 = 1/3 + (2/3)(1-q)^2(1-x) >= 1/3.

Only the case where both B genes attach directly at R leaves a nonuniform A-pair opportunity on R->U; three or four genes at U contribute uniformly.

### 6.4 Strictness and finiteness

The actual value satisfies a>=a_0>=1/3. In a diamond, interior inheritance gives positive probability that all four genes route to the same skeleton attachment site. In the zero-private-arc calculation those four labels are exchangeable from that site upward and a crossing outcome has positive probability. A positive private incoming arc supplies a positive probability of an earlier correct pair merger. Coupling on this positive-probability routing event makes the inequality strict. In the triangle, the positive shared edge and interior q already give strictness in its displayed formula; positive private arcs cannot reduce it.

Also a<1: there is a positive probability that every lineage survives every finite population edge and that a crossing pair coalesces first in the ancestral population. Hence

    1/3 < a < 1,
    s_core = 3(1-a)/2 in (0,1),
    t_core = -log(s_core) in (0,infinity).

This proves strictly positive root replacement for the entire relevant source class. Arbitrarily large blobs elsewhere cannot create further two-port root shapes, by Lemma 1.

## 7. Root replacement under common inheritance and actual assembly

For NMSCcom, condition instead on the product-weighted global switching in the root core. Every switched species quartet has the same A-pair/B-pair topology and a strictly positive finite internal length: at least one private pair edge supplies such a length even when both groups attach at the same site. Its tree-MSC correct probability lies strictly between 1/3 and one. The mixture therefore does too. This is a separate common-inheritance argument, not an independent-lineage/common-switch substitution.

Let e_A=(u_A,c_A), e_B=(u_B,c_B) be the two actual incident descendant cut edges. Delete the root core and replace it by a new binary root R' with edges to c_A,c_B of lengths

    t'_A = t_eA,       t'_B = t_eB + t_core.

More generally, split t_core into two nonnegative contributions. Both ACTUAL new edges have strictly positive length because the original incident edges did. The displayed choice uses zero additional contribution on the A side, not a zero-length actual population edge. The definition of a omitted e_A,e_B, so no incident length is counted twice.

For two live genes on each side, this tree interface has the same a. Allocations 3|1 and 4|0 and earlier-merger histories are handled by Section 4. The same core parameter applies to every choice of taxa. Arbitrary networks below c_A,c_B retain all their edges and inheritance mechanisms.

The new root has two nonempty taxon-bearing descendants and is their LSA. All outside orientations are unchanged. Nonroot contraction replaces a directed path region by one directed edge. Neither operation creates directed cycles, changes remaining binary degrees, or creates a hybrid with a non-cut child. A planar disk containing a two-port component can be replaced by a path with the same external incidences; thus the outer taxon embedding is preserved. Fresh node ages and edge-specific populations realize all resulting positive coalescent lengths.

In every switching, the part joining two ports is only a path after irrelevant degree-two suppression. Deleting the two-port blob therefore preserves each outside switching's unrooted taxon tree, and every outside switching has an extension through the deleted component. The SET of complete unrooted displayed trees is identical before and after replacement. Therefore Q, S, and the complete space of S-compatible circular orders are identical as well. Switching multiplicities and biological probabilities on full gene trees are not claimed identical.

## 8. Simultaneous normal-form theorem and inherited count

**Theorem 1.** For either mechanism separately, every state in Section 1 has a state in the same positive source class with all quartet CFs and displayed Q/S preserved, and with no nontrivial two-port blobs.

Proof. Repeatedly replace a nonroot two-port blob, then a root-containing two-port blob if present. Each step reduces the number of vertices, preserves the complete observable and target simultaneously, and preserves admission by Sections 4-7. Adjacent components consume the current incident edges, as in Section 5. No step merges two remaining cyclic components into a new blob. A finite input therefore reaches the claimed form. QED.

Use the root-aware count already derived in NORMALIZATION-EFFECTS. In the unrooted tree of blobs, let b be the number of remaining nontrivial blobs, p_B>=3 their port degrees, and t the number of ordinary trivalent vertices. There are n labeled leaves, no unlabeled leaves, and the degree-two root is suppressed for this count. The tree degree identity is

    sum_B(p_B-2)+t = n-2.

Each nonroot blob has h_B<=p_B-1; at most one root-containing blob has the additional possible hybrid. Thus

    r <= sum_B(p_B-1)+1 = n-2-t+b+1 <= 2n-3.

If no retained blob contains the root, the +1 is omitted. Rooted binary degree identities give V=2n+2r-1 and E=2n+3r-2, hence the stated bounds. This is a bound on a CF/target-equivalent representative, not on the original network and not a proof that every bound is a minimum stochastic realization size.

## 9. Exact polynomial model images

For any fixed candidate rooted graph, its quartet CFs are rational polynomials in x_e and h_v. A direct compiler stops at the first processed coalescence. While all four sampled genes remain unmerged, a population carrying k genes has no-merger probability x_e^(k choose 2); each unordered pair is its first pair with probability

    [1-x_e^(k choose 2)]/(k choose 2).

At a hybrid, enumerate all partitions of the live genes into the two parents with weights h^j(1-h)^(k-j) under NMSCind, or the two common-parent cases h and 1-h under NMSCcom. The all-surviving root state contributes 1/3 to each quartet. This yields a finite exact recurrence with rational coefficients.

A reverse topological ordering of populations need not order events in chronological time. That does not invalidate this killed recursion: two possible mergers on incomparable population branches involve disjoint label pairs and hence give the SAME unrooted quartet. If a branch contains three or four labels, another incomparable branch cannot contain a competing pair. An ancestral edge is processed only after descendant edges. This justifies stopping at the first processed merger for the marginal quartet observable.

Each original x-variable has degree at most six and each h-variable degree at most four. There are E+r<=10n-14 original real parameters; a coarse total-degree bound is 6E+4r<=56n-78. Shared arithmetic circuits can avoid premature expansion; the delivered small-case SMT exporter expands explicitly. Extra circuit variables would increase the solver dimension and are not included in the original-parameter bound.

A general CF recursion is prior work in Ané et al.; this implementation is an independent code path for checking this packet, not a new priority claim for probability calculation.

## 10. Complete actual-source catalogue and an effective classification

### 10.1 A finite grammar with its converse

For each r=0,...,2n-3 enumerate rooted vertex sets of size V=2n+2r-1. Put the root first and the n labeled sinks last in a topological ordering. Enumerate every assignment of r hybrid types and the remaining tree types to internal positions. Enumerate upper-triangular directed multigraph adjacency entries in {0,1,2}, retaining only the prescribed binary indegrees/outdegrees.

Filter for connectivity, root reachability, LSA, hybrid cut-child property and outer-labeled planarity. The latter has an effective test: the taxa are cofacial in some embedding exactly when adjoining a fresh vertex adjacent to every taxon leaf admits a planar embedding. Planarity of the underlying simple graph suffices; parallel arcs can be reinserted locally. It is NOT a requirement that all internal vertices be on the outer face. Dominator intersections test the LSA condition.

Every accepted graph is an actual admitted source. Conversely, every rooted representative in Theorem 1 has a topological order with all leaves last and binary edge multiplicities at most two, so it occurs in this enumeration after relabeling internal vertices. Duplicate graph descriptions do no harm. Thus this is a complete actual-source catalogue, not an occurrence-tree grammar with an unproved realization converse.

A deliberately loose bound on descriptions visited is

    (2n-2) 2^(6n-7) 3^((6n-7)(6n-8)/2).

This is finite, but is not a practical complexity claim. Compute each graph's target by enumerating its switchings and taking the displayed split/quartet unions, or by a separately justified equivalent method.

### 10.2 Images and exact input encoding

For each target T let C_T be the finite subcatalogue with that target. For mechanism M define

    I_T^M = union over G in C_T of
            {F_G^M(x,h) : 0<x_e<1, 0<h_v<1}.

Theorem 1 and the catalogue converse prove both inclusions: this is EXACTLY the all-original-size image for target T. It is not merely a definition over unbounded hidden networks.

For a rational or real-algebraic vector p of 3*binom(n,4) coordinates, decide

    T is compatible with p
      iff OR over G in C_T:
          EXISTS x,h [0<x,h<1 AND F_G^M(x,h)=p].

A real-algebraic coordinate is finitely encoded by an integer polynomial and a rational isolating interval selecting its real root. These constants can be represented in a real-closed-field formula with additional isolating constraints. Arbitrary unencoded real equality is NOT claimed decidable by an ordinary program.

Classical effective real-closed-field quantifier elimination supplies a terminating finite decision construction for every graph formula, and hence for the finite catalogue. It can return algebraic x,h witnesses when feasible; positive lengths can then be represented as -log of those algebraic x-values. No assumption that the original hidden state's parameters are algebraic is imposed.

Each target image is semialgebraic by projection. A full quantifier-free stratification by the compatible target set is therefore effectively constructible as well, though it has not been computed here. Strict inequalities remain strict: the image and its closure are different, and zero distance to an image does not establish membership.

**Theorem 2, effective CF-only boundary.** Let A_M(p)={T:p in I_T^M}. The exact profile is infeasible iff this set is empty, target-identifying iff it has one element, and ambiguous iff it has at least two elements. The displayed split/order answer for each candidate is computable from that candidate. This is a uniform finite necessary-and-sufficient procedure over the full source class, conditional on the proof premises in this packet; it is not an executed table for all n.

For NMSCcom, prior support identification additionally says that at every feasible profile Q(q) is the set of coordinates strictly larger than the minimum. That does not by itself decide whether a whole supplied profile is globally feasible. For NMSCind the existing exact collisions remain valid; the new construction classifies rather than eliminates them.

### 10.3 What the delivered code does

`cf_normal_form.py` implements actual-source checking, exact CFs, displayed splits, a duplicate-permitting complete graph generator, the automatic two-port normalizer, rational single-model exact/box formula export, and the guarded catalogue controller. `check_normal_form.py` executes the listed fixtures through exact arithmetic and a local Z3 C interface.

The full catalogue has NOT been run. A rational catalogue-and-image controller is implemented and its restricted-scope/interruption/unknown guards are exercised. The algebraic-input front end, general complete quantifier-elimination backend and whole-space stratification remain specification-level. No full all-class controller run was performed. The Z3 calls have a timeout and must retain unknown/unavailable; generic nonlinear solver execution is not a substitute for the mathematical complete-decision theorem. No unexecuted all-class infeasibility claim is inferred from a single-model unsatisfiable formula.

## 11. Confidence boxes, abstention and resource limits

For a rational box B=product[l_qi,u_qi], decide each graph formula with the simultaneous constraints l_qi<=F_G,qi(x,h)<=u_qi. The result

    A_M(B)={T:I_T^M intersects B}

is the exact set of targets globally compatible with some point of the box. Every quartet constraint uses the SAME graph and parameter assignment. Separately feasible quartet menus cannot replace this joint test.

For K=binom(n,4) and m IID loci, coordinatewise Hoeffding and a union bound yield

    P(max_q,i |p_hat_qi-p_qi| >= epsilon) <= 6K exp(-2m epsilon^2).

Quartets within a locus may be dependent; independence across quartets was not used. An outward-rounded rational confidence box using an epsilon at least sqrt(log(6K/delta)/(2m)) contains the true complete CF vector with probability at least 1-delta. Hence its candidate set contains the true target on that event. Return a singleton target only when certified; otherwise return ambiguity/inconclusive. An empty candidate set means incompatibility with the declared model/box or confidence failure, not empty displayed support.

For a true p with sup-norm distance Delta>0 from every different-target image, 2epsilon<Delta suffices to exclude those competing images from the box on the confidence event. Exact uniqueness alone does not imply such separation. The existing rare-reticulation obstruction to uniformly honest finite termination remains applicable; more samples cannot separate equal laws. Repeated looks require a valid confidence sequence or explicit error allocation, not repeated use of the same fixed-m bound.

The mathematical procedure is total but potentially enormous. A practical bounded wrapper may run a step-limited interpreter or terminate a solver/census job at a declared budget and return INCONCLUSIVE. It must NOT call the feasible targets found so far a sound outer candidate set: those are only witnessed lower inclusions. On unfinished catalogue/solver work, unresolved targets must remain possible, or a coarse ALL-ADMITTED-TARGETS abstention marker must be returned. A positive singleton certificate requires exclusion of every competing target or an independently sufficient theorem.

Separate costs: gene loci m, quartet readouts K per complete vector, ordinary graph/circuit/algebraic computation, and optional exact-support decoder queries. This passive construction uses no actuations and provides no original intervention IDs. It neither changes the reviewed Theta(n log n) ideal-oracle result nor purports to optimize its exact finite query count.

## 12. Executed evidence and remaining obligations

Actual results are recorded in `checks.json` with source hashes and software versions:

- Three independent-inheritance root formulas simplify symbolically to exact difference zero.
- 2,100 all-quartet original/replacement equalities on positive eight-taxon root fixtures.
- 420 further all-quartet equalities on serial root/nonroot compositions, covering 0|4 through 4|0 allocations; another 420 comparisons check the automatic normalizer against the independently assembled replacement.
- 1,050 common-inheritance equalities against a separate switched-tree mixture calculation.
- The inherited positive triangle/diamond collision is recomputed exactly at (1/4,3/8,3/8), with distinct displayed targets.
- A complete tiny two-taxon r<=2 grammar slice gives 27 ordered graphs, including eight single-root-blob descriptions; all sixteen mechanism-specific root normalizations are positive and admitted. This is a classification check, not the n>=4 catalogue.
- The complete four-taxon tree-only slice gives 18 ordered descriptions and three unrooted targets. Two invalid parameter fixtures are rejected.
- Four controller guards ensure that a tree-only census, interruption, or unknown solver result cannot produce an all-class certificate.
- Nine exact single-image QF_NRA checks return the expected sat/unsat values, including rational boxes, positive feasible points, strict-boundary exclusions and the inherited collision under the two mechanisms.

These are exact computations, not stochastic simulation, independent peer review, proof-assistant verification, biological experiments or a global n-taxon catalogue run. The symbolic probes temporarily use zero private lengths only to verify boundary identities; actual original/replacement fixtures are checked strictly positive.

Integrated obligation register:

| Obligation | Status in this packet | Remaining gate |
|---|---|---|
| Source-specific simultaneous positive two-port CF/Q/S normalization | Hand proof and automatic normalizer with exact fixtures | Independent source-critical proof review |
| Representative bound | Inherited count discharged by the new normalization proof | Review count premises together with actual assembly |
| Uniform global CF target characterization | Finite catalogue/QE construction proved here | Review; complete QE/algebraic-input integration and full all-class execution not completed |
| Single-model exact image/box compiler | Implemented and nine solver checks passed | Broader validation, robust solver certificates/interfaces |
| Finite-data confidence/abstention | Construction under explicit IID-locus observation contract | Practical runtime and data/gene-estimation-error model |
| Displayed Q/S and order integration | Target preserved; inherited structural decoder reusable | Canonical promotion after review |
| Full joint, rooted, metric, sequences, multiple-copy recovery | Not addressed by this CF normal form | Separate observation-law and identifiability proofs |
| Original controls/edge floors/temporal constraints | Not preserved by the stated theorem | Separate control-aware or constrained normalization |
| Historical novelty, formalization and publication acceptance | Not established | Primary-prior comparison and independent review |

The single highest-priority review is Lemma 1 together with the private-arc monotonicity/strictness argument in Section 6 and the source-admitted root assembly in Section 7. A defect there would invalidate the bounded all-class image consequence; successful finite fixtures alone cannot repair such a defect.

## 13. Source and provenance references

- Governing assignment: Commons handoffs/2026-09-30-omnibus-refocus/ASTRA-BIOLOGICAL-PROVER.md at 0757841eaf301a8e0955b5d6875058f0d998837b.
- Governing standard: MASTER-CLOSURE-STANDARD-20260930, accepted in communications/2026-09-30-astra-bio-prover-1612z-acceptance.md, commit 9d69ecd6bb1de85b4f81f9b25f930ac0a10be0a4.
- Canonical Samuel source: Sodelin/Work-on-Samuel-Alexander-Research-, e2502c82ab9a77c00543932f775a71e5374221f7, research/nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md and linked audits.
- ASTRA-OBS: research/2026-09-30-astra-alllevel-observation-1034z/PROOFS.md; normal-form receipt communications/2026-09-30-astra-obs-1034z-closure-receipt-and-normal-form.md. Local claims and inherited collisions retain that author's attribution.
- BIO-NORMALFORM-DIRECT: communications/2026-09-30-bio-normalform-direct-0523pt.md. This is a coordinated continuation, not a takeover or assertion about chat presence.
- Independent prior audit: research/2026-09-30-general-transfer-closure/REVIEW-cf-normal-form.md. This packet answers its written interface/root/admission questions but does not claim the reviewer has read or accepted the answers.
- Sharper count and control boundary: research/2026-09-30-normalization-effects/REPORT.md, NORMALIZATION-EFFECTS-20260930.
- Ané et al. published record: https://pubmed.ncbi.nlm.nih.gov/38372830/ ; accessible author preprint theorem text: https://pmc.ncbi.nlm.nih.gov/articles/PMC10473666/ .
- Source definitions: https://pmc.ncbi.nlm.nih.gov/articles/PMC12549781/ .
- Actual solver's nonlinear arithmetic limitations: https://microsoft.github.io/z3guide/docs/theories/Arithmetic/ .

All public artifacts are intentionally shareable mathematical material. A commit establishes preservation, not correctness, novelty, peer receipt or external acceptance.
