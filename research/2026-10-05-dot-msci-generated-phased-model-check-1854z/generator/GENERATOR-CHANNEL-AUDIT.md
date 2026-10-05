# Official BPP simulation channel for the fixed six-copy pulse experiment

Author: dot (OpenAI), 5 October 2026. Read-only source/manual audit. No vendor executable, parser, generator, new installation or dataset was run for this audit.

## Finding

The already pinned official BPP 4.8.7 simulation code supports the required IDEAL event-driven model semantics: six phased haplotypes, one backward B-to-C current-lineage pulse, equal numeric population parameters on the two B segments and two C segments, one genealogy per independent simulated locus, and two homogeneous stationary JC sites on that genealogy. The proposed exact network/control spelling below still requires its separately reviewed execution and runtime structural receipt before generated records can enter an adapter.

This does not certify the finite PRNG/floating-point program as an exact iid draw from the continuous mathematical law. The appropriate next use is a model-generated semantic fixture, with that numerical limitation visible, rather than a biological admission or exact finite-program confidence theorem.

## Source identities

SOURCE-RECEIPT.json pins ten local primary-source/manual files at official commit da8caf3aa00cf275cc9a044e0d806e9bbb0e1460, release 4.8.7. The official source location is https://github.com/bpp/bpp/tree/da8caf3aa00cf275cc9a044e0d806e9bbb0e1460 . No source/binary/manual copies are redistributed in this audit.

The existing earlier observation-channel audit and prior simulation admission work are reused. Here the additional question is the exact MSci pulse graph and generation channel, not inference convergence or a new MCMC implementation.

## Coalescent rates, routing and graph

In src/gtree.c:2483-2510, the simulator sums k(k-1)/theta within each current population. Thus the per-unordered-pair rate in the theorem is r=2/theta. Use theta_A=2/rA, theta_B=2/rB, theta_C=2/rC, theta_AB=2/rAB and theta_R=2/rR. The B-tip and retained post-pulse B segment must have the SAME numeric theta_B. The C-tip and C-stem must have the SAME theta_C. These are explicit numeric generation ties, not an assertion that an unrestricted inference model automatically imposes those ties.

In src/gtree.c:755-859, replace_hybrid partitions the current surviving gene-tree nodes from the hybrid child, drawing separately for each current lineage. Already coalesced descendants move together as one lineage. Its hphi is the probability of remaining on the nonmirror/left parental route; the complementary route goes to the mirror node. This is current-block pulse routing, rather than independent routing of each original sampled copy after those copies have coalesced.

A graph representation for the desired backbone ((A,B),C) is:

    ((A,(B)H[&phi=1-g,&tau-parent=yes])AB,
     (H[&phi=g,&tau-parent=no],C)CS)R;

This is a mathematical annotation template, not literal executable syntax for the expression 1-g. H has child B and parent AB. Its mirror has parent CS. Assign H age h, AB age t1=h+u, CS age h and R age t0=h+u+v. The mirror's tau-parent=no forces its parent CS to the same pulse age. Consequently the mirror is an instantaneous horizontal route into the C population; the normal H route persists until AB. Set its normal-route phi to 1-g and mirror-route phi to g. Forward-time gene flow is C to B, matching BACKWARD B to C.

src/treeparse.c:1120-1190 resolves the duplicate labelled hybrid/mirror graph; the following metadata logic sets complementary phis. src/simulate.c:2403-2467 assigns thetas to only the hybrid segments with actual positive-duration parental populations. src/simulate.c:2469-2550 synchronizes tau-parent=no nodes, and 2620-2647 initializes simulation ages from parsed node lengths before validating them. The simulation mode therefore uses supplied node ages, unlike the earlier no-date inference initialization that overwrote starting ages. src/gtree.c:1366-1414 orders the hybrid, mirror and coincident parent epochs correctly.

The retained positive-duration populations should be:

- A: [0,t1), theta_A;
- B tip: [0,h), theta_B;
- normal H/B continuation: [h,t1), theta_B;
- C tip: [0,h), theta_C;
- CS/C continuation: [h,t0), theta_C;
- AB: [t1,t0), theta_AB;
- root R: [t0,infinity), theta_R.

The mirror edge has zero duration and no extra coalescent population. The intended runtime inspection must verify graph identities, both phis and the parent-existence flags. Important: src/stree.c:148-235 prints its field labelled tau from node->htau, a FLAG, not the numerical age; that table also does not expose every theta. Numeric ages/thetas must be bound through the exact frozen control and independently audited parsing/assignment path. Do not claim that the table alone is a numeric parameter receipt. A separately instrumented numerical readout would require another source/build gate and is not proposed here.

## Phasing, loci and JC channel

Use species&tree with exactly three species A B C and counts 2 2 2, together with phase=0 0 0. src/simulate.c:129-149 only doubles counts for diploid flags. With all flags zero there are six haploid rows and no diploid collapse. src/simulate.c:1935-2014 generates labels A^a1,A^a2,B^b1,B^b2,C^c1,C^c2 and an Imap; actual runtime labels/map must still be authenticated before an exact renaming to the adapter's A1,A2,B1,B2,C1,C2.

Use loci&length=M 2, model=0, clock=1, locusrate=0 and alpha_siterate=1 0. The last setting explicitly fixes zero among-site rate variation; src/cfile_sim.c:971-1029 accepts the fixed-zero form. Avoid dates, ancestral sampling, migration, read-depth/error simulation, gamma site/locus rates and relaxed clocks. Output ordinary alignment records, not site-pattern counts or concatenated loci.

src/simulate.c:1874 starts the locus loop, and line2030 generates a fresh gene tree for each locus. Lines2033-2050 set a unit locus multiplier and elapsed-time branch lengths under the constant global clock. Lines2121 and2190-2193 generate a root sequence and evolve both root subtrees on that SAME gene tree.

For JC, src/simulate.c:729-748 draws each root state uniformly over four bases. Lines601-652 use branch mutation count Poisson(length times number_of_sites), uniform assignment to sites when alpha is zero, and a uniform change to one of the other three bases. Under ideal randomness, Poisson thinning yields conditionally independent site processes with mean substitution rate one, branch eigenvalue exp(-4 length/3), and therefore pair-character factor exp(-8 T/3). This matches the theorem's normalized clock-JC units and shared-genealogy two-site dependence. The nine extracted coordinates are not separately simulated.

## A dyadic parameter illustration, not an executed control

The independently proposed later semantic design can avoid unnecessary decimal parameter mismatch by choosing h=u=v=1/16, g=1/4, and rates (rA,rB,rC,rAB,rR)=(1,2,4,1,2). All lie strictly inside the existing original broad domain; repeated rates are allowed by the theorem. Their theta values are (2,1,1/2,2,1), exactly representable in binary.

The corresponding proposed age/theta syntax is:

    ((A #2, (B #1)H[&phi=0.75,&tau-parent=yes]:0.0625 #1)AB:0.125 #2,
     (H[&phi=0.25,&tau-parent=no], C #0.5)CS:0.0625 #0.5)R:0.1875 #1;

This is an authored candidate mapping for independent review. No seed, locus count or execution budget is selected here, and the string has not been passed to BPP. The final simulation control must be frozen and reviewed separately, then admitted only after runtime source/structure/label/truth checks.

## Numerical/RNG and interpretation limits

src/random.c:104-121 uses the legacy finite-state integer uniform generator; waiting times and mutation counts use floating numerical routines. A fixed seed is reproducible, not a proof of exact continuous sampling or literal iid independence. Even dyadic input parameters do not remove those implementation approximations. The primary-source semantics support an ideal-source numerical smoke test, while a total-variation error or exact-sampler guarantee remains unproved.

A model-generated-fixture classification should carry this distinction through the existing count/confidence/inverse path. One realization may establish data-shape, literal feature, parameter-map and containment facts. Its truth falling inside or outside a supplied confidence cover is not a repeated coverage estimate. No seed retry or data-dependent choice may silently replace the declared realization. Real biological admission, exact finite-program-law confidence and repeated calibration need separate contracts.
