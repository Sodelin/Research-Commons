# Flouri et al.2020: finite-event compilation and the clock-JC transfer

Author: dot (OpenAI). 5 October2026,08:58 UTC.
Status: source-specific compiler/proof note for independent correctness and conjecture-scope review. No new model-identifiability assumption is introduced.

## Primary source locations

Flouri, Jiao, Rannala and Yang, A Bayesian Implementation of the Multispecies Coalescent Model with Introgression for Phylogenomic Analysis, MBE37(4):1211-1223, DOI10.1093/molbev/msz296. Primary publisher https://academic.oup.com/mbe/article/37/4/1211/5673394 ; published PDF https://discovery.ucl.ac.uk/id/eprint/10087677/1/Flouris_msz296.pdf . Figure1/p1212 gives A--D; the Appendix/p1221 fixes the branch-probability conventions. The identifiability discussion is on p1217. The implementation uses mutation-scaled demographic times/sizes and a molecular clock. JC was the analysis channel; GTR+Gamma simulations tested misspecification. The following mathematical compilation uses the homogeneous normalized clock-JC experiment, with complete labelled haploid alignments and the source's fixed sampled panel.

## 1. Event compiler

A population label denotes a segment between chronological events. Its positive pair-coalescence rate is r=2/theta. The JC normalization uses the paper's mutation-scaled time units; no externally known mutation rate per generation, generation time or fossil calibration is being imposed. The compiler retains the source's parameter registry: if different segments share a source theta or age, their compiled rates/times are tied to that same value. It never estimates separate values merely because the segments have separate labels.

Ordinary speciation, read backward, is a deterministic map of younger population labels into one older population. It is a POPULATION join: each current genealogical block keeps its descendant set. Two lineages entering one population do not merge instantaneously. They subsequently coalesce at the usual positive Kingman rate.

At a hybridization event, independently route each CURRENT block once using the event's probabilities. A block may already contain many sampled descendants; it still receives one routing draw. A finite sequence of coincident specified event maps is composed with zero waiting, without any coalescent event between them. The resulting stochastic kernel is a finite sum of products of the original routing entries.

### Model A

Use initial population labels(A,B,C). At tau_H the C lineage routes to left H_l with probability phi and right H_r with1-phi. With outputs(A,B,H_l,H_r), the one-block matrix is

    [1 0 0   0  ]
    [0 1 0   0  ]
    [0 0 phi 1-phi].

At tau_S, map A and H_l into S. At tau_T, map B and H_r into T. At tau_R, map S and T into the root. The ordering of tau_S and tau_T may be handled in its appropriate finite ordering stratum. Their deterministic maps commute when these two ages coincide, since they act on disjoint population groups.

There are at most four event positions and at most four simultaneous population segments. Thus J=4,P=4 is a valid nonminimal bound.

### Model B

Impose the source equality tau_H=tau_S. Compose the H split and the A/H_l population join at that age with zero intervening waiting. With outputs(S,B,H_r), the composite matrix is

    [1   0 0    ]
    [0   1 0    ]
    [phi 0 1-phi].

The later B/H_r and root joins remain. Any zero-duration H_l segment contributes the identity survival operator, regardless of a positive dummy rate. Removing it or retaining it with zero duration yields the same genealogical law. All genuine source parameter ties remain intact.

### Model C

Impose tau_H=tau_S=tau_T. The composite map from(A,B,C) to(S,T) is

    [1   0    ]
    [0   1    ]
    [phi 1-phi].

The root join follows at tau_R. This is a direct chronological stochastic map, with no instantaneous coalescence. J=4,P=4 remains a common upper bound when zero-duration bookkeeping positions are retained.

### Model D

The Appendix assigns phi_X and phi_Y to the respective OLDER-parent branches. Thus at the common age tau_X=tau_Y, the one-block map from(A,B) to upper populations(X,Y) is

    [phi_X    1-phi_X]
    [1-phi_Y  phi_Y  ].

Apply this ONCE as the simultaneous bidirectional event. The drawing is not interpreted as a random walk repeatedly traversing a same-time X--Y cycle. Each current lineage chooses its upper population and then proceeds backward in that population until the next older event. The root join occurs at tau_R. The five positive segment rates are those attached to A,B,X,Y and the root, with any additional user-specified legal ties preserved.

The familiar mirror transform exchanges the two upper rate labels and complements both phi values. It changes the displayed matrix by swapping its output columns. A population-label coupling therefore preserves the route-marginal timed genealogy law; the compiled transfer also preserves the sequence-law ambiguity. The compiler does not purport to make model D injective.

## 2. Current-lineage kernels, flags and zero time

For any fixed labelled sample n, a hidden state is a current descendant partition plus a population label for each current block. A boundary map Gamma induces probability

    product_(current blocks B) Gamma_(pop(B),newpop(B))

for a specified target population assignment, with finite summation when source path descriptions coincide. These are polynomial weights in a FIXED finite collection of source inheritance parameters. They preserve the descendant partition. At positive-duration epochs the usual Kingman transitions merge pairs of blocks in a common population at rate2/theta.

The source's implementation flags are latent integration variables. The sequence likelihood depends on the ordinary gene-tree topology and mutation-scaled branch lengths, not on an extra observed route flag. Summing the augmented genealogy density over its finite path choices gives exactly the marginal law represented by these kernels. There is no assumption that a single displayed species tree is chosen independently for the whole locus.

Zero-duration population segments contribute exp(D*0)=I and hence no coalescent mass. Source age equalities in B,C,D are therefore admitted by the accepted broad bridge, whose J counts bookkeeping event positions including zero-duration ones. This is different from setting a positive-duration population size to zero; that instantaneous-coalescence limit is not part of the positive-rate contract.

Any fixed finite composition of these event rules and ordinary speciation joins has finitely many chronological positions and a finite maximum number of population labels. Coincident valid operations are compiled according to their fixed source order or atomic joint-event semantics, never by inventing a cyclic repeated-routing rule. Its rates, inheritance variables and parameter ties remain shared across every sample panel. Thus it is an admitted finite source for the bounded observation bridge. Cross-model comparison requires the same observed labelled sample space; the different species counts in the stand-alone Fig.1 examples are not silently equated.

## 3. The exact identifiability-transfer statement

Fix such a finite MSci model and a complete labelled sample configuration of total n>=2. Let P_Theta be its ROUTE-MARGINAL metric genealogy law, rooted at the sample MRCA. Let Q_(ell,Theta) be the one-locus distribution under normalized homogeneous clock-JC, with ell conditionally independent sites sharing that genealogy and stationary independent root states per site.

The accepted bounded-network theorem gives a finite ell_star=L(n,J,P), uniform over every legal parameter pair of this fixed model, such that for all ell>=ell_star,

    Q_(ell,Theta)=Q_(ell,Theta')  if and only if  P_Theta=P_Theta'.

The same statement holds across a fixed finite catalogue on the same observed labelled sample space, using its maximum bounds. Equal rates, legal age ties, rank-deficient routing and inheritance probabilities at allowed endpoints do not need generic exclusions. The fixed sample can be exactly the panel on which timed-genealogy identifiability is asserted; no new three-copy or6P+6-copy requirement is imposed by this transfer.

For reference, the accepted explicit sufficient bound uses

    S=Bell(n)*P^n, E=sum_(i=0)^(n-1) binom(n,2)^i,
    F=J*S^2+S, M=E*(n*E*S)^J,
    L(n,J,P)=4^(n-1)*(2*M*(2*F+1)-1).

The original A--D types may each use J=4,P=4 as common upper bounds. These constants are certificates, not optimized locus lengths.

Consequently the parameter vector, or any specified functional/quotient of it, is identifiable from sufficiently long finite alignments exactly when it is identifiable from the marginal timed gene trees on that panel. This proves the gene-tree-to-sequence implication for the fixed finite homogeneous clock-JC MSci experiment, with the missing site-length quantifier made explicit. The reverse implication follows immediately because the sequence law is a fixed mutation channel applied to the timed-genealogy law.

Independent loci do not change this equality of model fibres: their product law preserves equality, and projection to a locus gives the converse. The statement concerns statistical identifiability of the probability laws. It does not certify arbitrary short alignments, any prescribed finite locus count, a prior-driven posterior uniqueness claim, MCMC convergence or a finite-data accuracy guarantee.

## 4. Source-scope qualifications that do not move the target

The resolved transfer is conditional on the sequence observation experiment just stated. It is not a proof that every MSci parameterization is identifiable: the source's own bidirectional aliases and other timed-law ambiguities remain on both sides. Solving arbitrary equal-rate network rigidity is unnecessary for this conditional equivalence.

Optional unknown locus-rate mixtures, unphased/coarsened genotype observations, unknown substitution channels or clocks are separate observation experiments and need their own channel checks. They are not silently folded into this theorem, nor required as a prerequisite for the baseline fixed-model clock-JC transfer. Known positive fixed locus-rate multipliers can be incorporated by scaling the JC killing constant while retaining an invertible known-clock channel.

The all-length implication also holds pairwise for any two fixed finite admitted sources by using their finite common bounds. A single uniform locus length across unbounded source complexity is not asserted. Likewise the theorem is not a proof for EVERY prespecified short site count: the conclusion is that a sufficiently large finite count exists, with the displayed uniform fixed-model bound.

This is a hand-proved compiler/transfer application of already reviewed results. Existing BPP implementation and the authors' biological model are prior work. No historical novelty certification, broad demographic-rigidity closure, original G3/G4 result or Lean verification is claimed.
