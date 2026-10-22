# A complete finite source registry when selection is absent

Author: dot (OpenAI). Date: 22 October 2026 UTC.
Status: Scoped independent coordinating-context hand-review PASS received 22 October 2026; historical-priority review remains open. See HAND-REVIEW-2026-10-22.md.
Formal status: No runtime execution or Lean verification.
Attribution: A direct synthesis of standard latent-projection ADMG theory with the preceding query certificate, not a claim of new latent-projection theory or historical priority.

## 1. Declared target and theorem

Assume **selection is known absent in the entire source class**, not merely absent in the particular true graph. Unknown latent variables remain unrestricted in number and topology. Work at the HPL SIS level after its permitted context reduction. Retain all observed variables X=T disjoint-union U, exact faithful CI/invariance responses, and the same named single-target soft interventions as in LATENT-SELECTION-IMEC-CERTIFICATE.md.

The target in this companion is explicitly

TCMclass_0(D)={TCM(D',T): D' approximately_T D and D' has no selection nodes}.

This is the no-selection restriction of the broader HPL TCM class. It is not silently substituted for the selected class. The broader manuscript remains a lossless shared-source certificate even when selection is allowed; this companion supplies a stronger explicit output only in the declared no-selection class.

**Theorem.** After at most the B(n,k,u)=O(n^2 2^u) elementary queries in the certificate manuscript, there is a terminating finite algorithm that lists exactly TCMclass_0(D), with no supplied latent-node bound. A complete graph-signature registry consists of ADMGs on X with bows allowed, at most 6^choose(n,2) candidates. Each has a canonical DAG witness with at most choose(n,2) latent roots. No polynomial total-runtime or full-law/statistical claim is made.

The rest of this note proves completeness, named-intervention compatibility, preservation of the actual marked MAGs, source realization, and exact listing.

## 2. The correct mixed graph retains bows

An acyclic directed mixed graph (ADMG) here has directed and bidirected edges, no self-edges, and no directed cycle. A pair may have both a directed and a bidirected edge. This differs from a MAG, which cannot retain such a bow.

For a finite DAG D on X union L, its latent projection H=LP_X(D) has:

- a -> b if D has a directed a-to-b path with all internal vertices latent;
- a <-> b if D has a collider-free path entering both endpoints, with all internal vertices latent.

The directed part is acyclic: a directed cycle in H would expand into a directed closed walk in D and hence contain a directed cycle, contradicting acyclicity.

The standard latent-projection theorem states, for disjoint observed A,B,Z, that d-separation of A,B by Z in D is equivalent to m-separation in H. We use the exact statement and proof in Richardson–Evans–Robins–Shpitser (2023), Proposition 1 and Supplement A.3–A.4, with the operation attributed there to Verma–Pearl (1990). This is a graphical separation theorem, not equivalence of every latent-variable distributional model or every non-CI constraint.

## 3. Projection commutes with the specified root augmentation

### Lemma 1

For each observed t, adding a fresh root I_t with its only edge I_t -> t satisfies

LP_(X union {I_t})(Aug_t(D)) = Aug_t(LP_X(D)).                 (1)

#### Proof

The fresh degree-one root cannot be internal on a path between old vertices. Thus every latent-only path contributing an old-old directed or bidirected projection edge is unchanged.

There is the direct new edge I_t -> t. A path from I_t to a different observed x must immediately visit t. Since t is observed and is then an internal vertex, such a path cannot produce a latent-projection edge. No edge can point into I_t because it is a root. Therefore the only new projected edge is I_t -> t. QED.

Combining (1) with the standard separation theorem proves simultaneous preservation of every control CI and every separate named-indicator conditional separation. The same H serves every t; we do not choose unrelated canonical sources by regime. This point is stronger than separately representing the observational MAGs.

### Lemma 2. Observed ancestry is preserved

For distinct a,b in X, a is a directed ancestor of b in D iff it is a directed ancestor of b in H. The same holds on X union {I_t} for each augmentation.

#### Proof

Split a directed path in D at all observed vertices. Every segment has only latent internal nodes and projects to a directed edge, producing a directed path in H. Conversely, expand each directed edge of an H-path into its latent directed witness in D. The resulting directed walk cannot repeat a vertex, since D is acyclic; it is a directed path. Apply this argument to Aug_t(D) and (1) for the last assertion. QED.

## 4. One common canonical source for each ADMG

For an ADMG H on X, construct C(H) by keeping all its directed edges and replacing each bidirected edge a<->b by a new distinct latent root l_ab with l_ab->a and l_ab->b. The original bidirected edge itself is removed from this DAG. There are at most choose(n,2) new roots.

### Lemma 3

C(H) is a DAG and LP_X(C(H))=H.

#### Proof

New roots have no incoming arrows, so no directed cycle can use them. The old directed graph is acyclic. Hence C(H) is a DAG.

An old-to-old directed path with latent internal vertices cannot enter a new root; therefore its only possible projected directed edge is an existing old directed edge. Conversely each such edge is present. A collider-free, into-both-endpoints path with only latent internal vertices can use only one new root, because the roots have no edges between them and any transition between roots would pass an old observed vertex internally. It therefore has form a<-l_ab->b. These are exactly H's bidirected edges. QED.

By Lemma 1, LP(Aug_t(C(H)))=Aug_t(H) for every t. Consequently C(H) realizes the full named-intervention graphical signature of H with one shared underlying source.

### Lemma 4. Exact marked-MAG and TCM preservation

If H=LP_X(D), then M_0(D)=M_0(C(H)) and M_t(D)=M_t(C(H)) for every t, as labeled marked graphs, not merely as equivalence classes. Thus their TCMs are identical.

#### Proof

By the separation theorem and Lemmas 1 and 3, both DAGs have identical separations on the relevant observed vertex set. In the maximal ancestral projection, adjacency is precisely inseparability by every observed conditioning set, so their MAG skeletons agree.

With no selection, the mark on an adjacent pair is a tail at a precisely when a is an ancestor of the other endpoint in the original DAG; otherwise it is an arrowhead. Lemma 2 gives identical observed ancestry in D and C(H), also after every augmentation. Hence all corresponding endpoint marks agree. Trimming the same own-target edges yields identical TCMs. QED.

It is essential here to retain the ADMG, rather than replacing it by its observational MAG before augmentation. The MAG may discard a confounding component hidden behind a directed edge, which a soft-intervention indicator can expose. The bow-preserving projection avoids that loss.

## 5. Actual fixed-mechanism representatives

The registry can be represented graphically, since the oracle assumptions equate responses with separations. If a registry of actual probability sources is demanded, each C(H) admits one fixed strictly positive rational binary model with all named soft replacements simultaneously faithful.

To see this, parameterize every base conditional table on C(H), every target's replacement conditional table using the same parent set, and each separate indicator's mixing probability. For each fixed t, the common parameter space maps onto the full positive binary DAG parameter space of Aug_t(C(H)): its target table has freely chosen base and replacement slices, all other tables are free base tables. The analogous projections to the base and each intervention regime are also onto.

By Meek's discrete faithfulness result and polynomial proof, each unwanted extra independence lies in a proper algebraic zero set. There are finitely many graphs, regimes and CI statements in this fixed construction. Avoiding their finite union leaves a nonempty open set containing rational points. Choose one such point, with no numerical tables asserted to have been computed. The replacements change only the named target; latent-root and nontarget kernels remain fixed across all regimes.

An effective representative specification is to enumerate positive rational tables and reject those whose finitely many exact CI signatures disagree with the base, regime, or augmented graph. The nonempty-open-set argument proves termination. This is a mathematical algorithm, not an executed computation.

We claim equality of the elementary oracle signatures and the graph targets, not equality of the original source's numerical distributions, Verma constraints, latent state spaces, or all interventional functionals. This distinction is necessary for faithful target preservation.

## 6. Complete finite enumeration of the restricted TCM class

Enumerate all labeled ADMGs H on X as follows. For each unordered pair, choose no directed edge, the forward directed edge, or the reverse directed edge, independently choose presence/absence of its bidirected edge, then reject directed cycles. There are at most 6^choose(n,2) choices before rejection. This is a complete finite registry of bow-permitting ADMGs, not an unproved bound on arbitrary latent DAG topologies.

For each H:
1. Form C(H).
2. Compute its base MAG and each separate augmented MAG by finite graph operations.
3. Check the certificate membership predicates from Theorem 3 of LATENT-SELECTION-IMEC-CERTIFICATE.md.
4. If all pass, collect TCM(C(H),T). Deduplicate identical finite labeled graphs.

### Theorem 5. Soundness and completeness of the list

The algorithm terminates and returns exactly TCMclass_0(D).

#### Proof

Termination follows from finite ADMG enumeration and finite separation/projection/certificate checks. Each accepted canonical source C(H) is an admissible no-selection graph; by the certificate's bidirectional decoder it is interventionally equivalent to D. Its collected TCM therefore belongs to TCMclass_0(D), proving soundness.

For completeness, let D' be any no-selection source interventionally equivalent to D, with any finite number of latent nodes. Set H'=LP_X(D'). That ADMG occurs in the registry. Lemma 4 proves that C(H') and D' have exactly the same base and augmented MAGs and exactly the same TCM. Since D' passes the certificate, C(H') passes too. Its collected graph is therefore precisely the requested TCM of D'. Every target member is collected. QED.

Thus no latent cardinality supplied by the user is needed in this no-selection class: the finite canonical bound is proved from projection, simultaneously for the named interventions. The exponential postprocessing is not hidden in the O(n^2 2^u) query notation.

## 7. G7 transfer and the remaining selection boundary

For the declared no-selection class, the map D -> LP_X(D) -> C(LP_X(D)) preserves every admitted elementary response and the actual marked TCM. Section 5 provides actual fixed-mechanism representatives if needed. Therefore the finite registry is complete **for the source signatures and target being studied**, despite not reproducing numerical laws. A policy correct for this finite registry is correct for the original no-selection source class by this proved adapter. Budget/reset/shared-source limitations are exactly those in the certificate manuscript.

This is a genuine carrier/observation/target mapping for the abstract finite G7 game. It is not an instance of the original biological polynomial observation compiler, and it does not settle G4 or introduce arbitrary continuous query actions.

Selection is the precise boundary: projecting out hidden nodes and then conditioning arbitrary unobserved sinks is not justified by the no-selection ADMG construction above. Independently canonicalizing selected MAG slices can change their common intervention source. A valid extension must prove a joint selection-compatible projection and realization theorem preserving every named augmentation. This note does not impose the no-selection target on the broader selected theorem.

Subsequent development: SELECTION-FINITE-REALIZATION.md proves such a full selected common-source hand theorem using selection-boundary marked pairs and ancestry flags. It has its own scoped hand-review pass and is not assumed in this no-selection theorem.

## Sources

Richardson, Thomas S.; Evans, Robin J.; Robins, James M.; Shpitser, Ilya. Nested Markov Properties for Acyclic Directed Mixed Graphs. Annals of Statistics 51(1), 334–361, 2023. Proposition 1, Supplement A.3–A.4. Latent projection is attributed there to Verma and Pearl (1990). Only its ordinary separation-preservation theorem is used here, not an identification or nested-model result.
https://arxiv.org/pdf/1701.06686v6

Meek, Christopher. Strong Completeness and Faithfulness in Bayesian Networks. UAI 1995, 411–418. Theorems 5 and 7 and exceptional-polynomial proof.
https://arxiv.org/pdf/1302.4973

Hou, Xiaotian; Park, Kwangmoon; Li, Hongzhe. Statistical Inference for Causal Discovery under Selection and Latent Variables via Single-Target Interventions. arXiv:2609.28856v1. MAG endpoint definition and separate-indicator target.
https://arxiv.org/html/2609.28856v1

Kocaoglu, Murat; Jaber, Amin; Shanmugam, Karthikeyan; Bareinboim, Elias. Characterization and Learning of Causal Graphs with Latent Variables from Soft Interventions. NeurIPS 2019. Prior provider of soft/latent augmented equivalence theory.
https://proceedings.neurips.cc/paper/2019/file/c3d96fbd5b1b45096ff04c04038fff5d-Paper.pdf

Zhou, Zihan; Kocaoglu, Murat. Towards Completeness in Causal Discovery from Soft Interventions with Known Targets. ICML 2026. The full primary PDF and relevant appendices have now been read. Lemmas 5.3/5.5 and Theorem 5.7 give common-source no-selection ADMG realizability, and Theorem 5.8 gives exhaustive I-MAG completion. Thus this companion is not the first latent soft-intervention realization/listing theorem. Its elementary classical-projection proof remains independent, and its separate HPL target must not be silently equated with their joint-augmentation target. See [the exact-claim reconciliation](PRIOR-WORK-EXACT-CLAIM-RECONCILIATION.md); no novelty is asserted.
https://proceedings.mlr.press/v306/zhou26s.html
https://raw.githubusercontent.com/mlresearch/v306/main/assets/zhou26s/zhou26s.pdf

[General selected certificate](LATENT-SELECTION-IMEC-CERTIFICATE.md)
[Lower barrier and finite-family game](RESTRICTED-INTERVENTION-BARRIER.md)
