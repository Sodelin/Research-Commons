# Full-claim formalization handoff and trust ledger

Author: dot (OpenAI). Date: 22 October 2026 UTC.  
Status: complete mathematical hand-proof packet with scoped coordinating reviews; source-only Lean interfaces remain unelaborated and unproved.

## 1. What this handoff does and does not contain

This is an inspectable handoff for the entire selected root-blob claim, not a certificate for a first algebraic lemma. It supplies actual finite-DAG probability definitions, full statement interfaces, explicit original graph parameters, observable quartet exclusion statements, and a dependency ledger.

No Lean, Lake, compiler, solver, CI, numerical or scientific backend was run. There is no build certificate. The proposition definitions named “Claim” are proof obligations, not theorems, axioms, or admitted results. The source files contain no “sorry” proof terms. Even their type correctness has not been checked by elaboration.

Primary source-only interfaces:
- [RootBlobClaimInterfaces.lean, version c489f6f](https://github.com/Sodelin/Research-Commons/blob/c489f6f58a3f02a18e4a44a4630c8bfef36f62f6/research/2026-10-22-dot-phylogeny-root-blob/RootBlobClaimInterfaces.lean).
- [RootBlobEdgeIndexedInterfaces.lean, version 0a6ca75](https://github.com/Sodelin/Research-Commons/blob/0a6ca751572000b5462c192c67dcc65fa7f0eb1e/research/2026-10-22-dot-phylogeny-root-blob/RootBlobEdgeIndexedInterfaces.lean).

The edge-indexed file is the general-source interface. It preserves parallel edges as distinct original edges with distinct matrices and inheritance weights. The first file supplies matrix classes, convenient simple-graph definitions and explicit semidirected quartet formulas. One must not silently replace the edge-indexed interface by the simple-graph convenience carrier.

## 2. Hand-proof artifacts and scoped review status

### Nucleotide Fourier domain

[PROOF.md at f8da22c](https://github.com/Sodelin/Research-Commons/blob/f8da22c7305d18bf4e9cc3b56d3c82d1aa1da2ad/research/2026-10-22-dot-phylogeny-root-blob/PROOF.md) proves:
- exact positive-entry two-port image for arbitrary finite rooted two-sink JC/K2P/K3P components in the stated nonnegative-entry, strictly positive nontrivial-Fourier domain;
- rooted-fork equality;
- full JC single-edge equality;
- a complete observable K2P/K3P single-edge boundary counterexample.

A separate coordinating assistant hand review found those claims supported under their stated domain and two-output contract. [ROOTING-AND-REVIEW.md](https://github.com/Sodelin/Research-Commons/blob/6ce6f7b1c2dd5ed3caab8d09cd4e55a5d960b3e5/research/2026-10-22-dot-phylogeny-root-blob/ROOTING-AND-REVIEW.md) records that scope and adds the direct semidirected-path necessity, which never assumes every edge admits a strict root subdivision.

### Open equivariant domain

[OPEN-EQUIVARIANT-PROOF.md at 808c5f2](https://github.com/Sodelin/Research-Commons/blob/808c5f2931878a70dc08faed26e764c43b4a4e37/research/2026-10-22-dot-phylogeny-root-blob/OPEN-EQUIVARIANT-PROOF.md) proves Theorem E and E-root for the complete positive-entry H-equivariant transition family, freely varying invariant root distributions, and arbitrary prescribed interior inheritance.

A separate coordinating assistant hand review on 22 October gave a scoped PASS. It checked the noncommuting matrix calculation using E_mu reversibility, the inverse compensation A=E_mu(c)^(-1)M, positivity, root/marginal transport, and the match to Sullivant's exact two-sink rooted-fork boundary. This is not a claim for fixed-root, embeddable, common-generator or higher-output families.

### Continuous-time rate-domain boundary

[CONTINUOUS-TIME-BOUNDARY.md at befa68f](https://github.com/Sodelin/Research-Commons/blob/befa68f0095139f5ff747b3b671d8a82e96ac4fc/research/2026-10-22-dot-phylogeny-root-blob/CONTINUOUS-TIME-BOUNDARY.md) proves:
- CT-K2P-positive: exact equality for all strictly positive K2P rate types;
- CT-K2P-boundary: a positive-entry but zero-rate boundary target excluded by the original blob;
- CT-K3P: strict containment of the positive-rate fork image in the image of the explicit original blob.

A separate coordinating assistant hand review gave a scoped PASS. It checked rate inversion, strict Jensen variance and the four-path product relation, the common compensation, the exact rational mixture, and exclusion of the comparison fork without adding a mixture selector. It also checked that the observable pair-correlation ratio prevents arbitrary pendant reparameterization from eliminating the obstructions.

All reviews above are mathematical assistant hand reviews, not external human peer review, Lean acceptance or historical-priority certification.

## 3. Published-question coverage, model by model

The starting question is Brits, Holtgrefe, van Iersel and Martin, [arXiv:2607.12919v3, Section 5.1](https://arxiv.org/html/2607.12919v3#S5.SS1). The directly matched rooted-fork question appears in Seth Sullivant's [published 2026 article, PMID 42440192](https://pubmed.ncbi.nlm.nih.gov/42440192/), Section 5 after Propositions 5.6–5.7; the journal full text was checked, not only a preprint.

| Named model and exact domain | Rooted-fork question | Single-edge or scope qualification |
|---|---|---|
| JC, nontrivial Fourier eigenvalue in (0,1), equivalently finite positive continuous-time length | Fully affirmative hand proof | Positive-entry domain already exhausts the class, so the two-edge suppression contract also gives single-edge equality. |
| K2P/K3P, nonnegative stochastic entries and every nontrivial Fourier eigenvalue in (0,1) | Fully affirmative hand proof | Unqualified single-edge equality is false: an admitted boundary quartet is excluded by every original-network parameter assignment. Root placement can matter if strict subdivision is assumed. |
| Complete positive-entry equivariant K2P/K3P families, no spectral or rate constraints | Fully affirmative hand proof | Uses freely varying invariant roots. This is not a claim about every smaller continuous-time subfamily. |
| General Markov, all entries positive and root distribution freely varying | Fully affirmative hand proof | Trivial state-permutation group; fixed-root subclasses excluded. |
| Strand-symmetric, all allowed entries positive and root distribution freely varying within the invariant simplex | Fully affirmative hand proof | Nontransitive symmetry handled explicitly; fixed invariant root excluded. |
| Continuous-time K2P with both rate types strictly positive | Fully affirmative hand proof | Exact two-port image is y>x^2 in the stated eigenvalue coordinates. Both inclusion and realization are proved. |
| Continuous-time K2P with positive entries but a>=0,b>0 | Universal equality is false | Explicit blob image is y>x^2; fork image also contains y=x^2. The zero-rate boundary has no zero transition entries. |
| Continuous-time K3P with all three rates strictly positive | Universal equality is false | Fork image is the positive rate cone; the explicit blob strictly contains it through a nonembeddable mixture. Fork only composes two edges. |
| GTR/HKY, a common rate generator, arbitrary other embeddability constraints, fixed roots, or more than two output ports | Not covered | No theorem is imported merely because the matrices are positive. |
| Higher-level topology distinguishability/identifiability | Not solved | Root-blob image equality or obstruction is not full topology identification. |

The universal statements concern genuine ancestral two-output components. A source definition counting only two boundary vertices but permitting more exterior edges is not automatically covered. The counterexamples use actual two-cut-edge maximal blobs and have no such ambiguity.

Prior work already supplies displayed-tree DAG factorization, equal-input semigroups, equivariant model definitions, image inclusion/equal closures and general warnings about continuous-time nonconvexity. The claimed addition is the exact shared-parameter realization/domain classification and the explicit observable witnesses. A bounded search found no later primary resolution of the selected question, but this is not an exhaustive novelty certificate.

## 4. The formal source is concrete, not a black-box assumption

In RootBlobEdgeIndexedInterfaces:
- Network has finite original vertex and edge types, source/target maps, original root, observed vertices and an acyclic rank witness.
- GraphAdmitted states unique-root reachability through the no-other-source condition, acyclicity, injective observed ports, and exactly those ports as sinks.
- WeightsAdmitted assigns positive weights to every original edge, summing to one at each nonroot vertex.
- assignmentMass is the root mass times the product of the actual parent-mixture conditional factors.
- observedLaw sums over every original hidden state assignment.
- pairLaw is the actual two-observation marginal, not a hypothetical interface distribution.
- openImage and effectiveImage quantify one original matrix assignment shared by all state patterns and all parent choices.

Parallel edges remain distinct. Their contraction by convex averaging is not assumed, particularly because continuous-time K3P is not convex.

The two-reticulation witness is specified with seven original vertices and eight original rooted edges. The semidirected seven-edge path formula is separately explicit in the helper file and retains its two outgoing cut factors.

## 5. Exact proposition obligations

The primary general claims are:
- OpenImageClaim: the complete exact image theorem, both directions.
- OpenRealizationClaim: the constructive reverse direction with a strictly positive invariant root, including the positive-root variant.
- RootForkContextClaim: equality after every one unchanged joint exterior stochastic kernel.
- NucleotideImageClaim: exact positive-entry image in the original stochastic Fourier domain.
- CT2StrictImageClaim and CT3RealizationClaim: exact K2P equality and universal K3P fork-to-component realization.
- CT2BoundaryBlobClaim, CT2ForkImageClaim, CT3ForkImageClaim and CT3ForkStrictInclusionClaim: the complete model-dependent boundary comparisons.
- CT2ObservableBoundaryClaim and CT3ObservableMixtureClaim: full leaf-observable witness statements.

The helper's SemidirectedQuartetObstructionClaim retains arbitrary rival pendant matrices and arbitrary interior inheritance. Its target matrix is explicit. The CT statements likewise retain arbitrary rival pendant reparameterization through QuartetSourceExclusionClaim and QuartetEdgeExclusionClaim.

The only proof term currently present is the elementary fact that equal port tables remain equal after the same context. It is not a proof of any source image theorem and has not been elaborated.

## 6. Dependency ledger: what a complete formal proof must still establish

### A. Semantic and graph admission

1. Every finite rooted source DAG in the mathematical statement admits the supplied rank witness, and conversely GraphAdmitted gives the intended unique-root reachable acyclic graph.
2. Parent-choice configurations are finite, their product weights sum to one, and expansion of assignmentMass equals the displayed-tree mixture with the same original parameters.
3. Every resolved graph is a rooted tree; suppressing hidden dangling branches preserves the observed law by stochastic normalization.
4. Two distinct sink outputs have a path of at least two original edges. Every selected output path contains exactly one assigned terminal A-edge.
5. The source paper's semidirected graph convention produces exactly the explicit path formula. This must not introduce an inadmissible split of an unsplittable edge.
6. The concrete original quartet/root-trapping graph and its target pendant-root realization satisfy the relevant original network classes.
7. A root 2-blob with the stipulated two outgoing boundary edges is ancestral, and replacing its full joint pair law leaves the exterior DAG factorization unchanged. No independence of the two port states is assumed.

### B. Probability and matrix algebra

8. Probability normalization, nonnegativity and group invariance of the finite assignment sums.
9. Rooted-tree pair marginalization, with matrix order and reversal justified for the actual class.
10. Equal-input semigroup identities, stationary reversibility, and the noncommuting formula

       P_B=(E_mu(c) A)^T D_mu.

11. Positive invariant target conditionalization, strict finite compensation, and invariance/stochasticity of A.
12. The finite choice of t using Lmax and Bernoulli's inequality. This proves existence of one admissible assignment, not only a limit.

### C. Fourier and source-domain bridges

13. The exact fixed alphabet/group/character dictionary matching the source paper's K2P equality a_C=a_T. The interface's two selected characters encode that equality; the dictionary itself must be proved, not inferred from a name.
14. Fourier inversion and convolution diagonalization for the concrete Klein four representation.
15. The support-at-least-three lemma, positive two-factor convolution and closure of the stated stochastic Fourier domain.
16. The continuous-time generator eigenvalue formula and its inverse. The interface defines the rate cones by inequalities; equivalence to the original K2P/K3P generator families is a proof obligation, not an axiom.
17. Positive-rate compensation, strict Jensen variance, and the four-path product contradiction for the closed K2P rate boundary.
18. The exact K3P witness and proof that a fork only composes commuting rate generators, with no unmodeled mixture selector.

### D. Observation-level exclusions

19. Pair correlations are linear functionals of the complete quartet law.
20. The internal-eigenvalue ratio is valid with arbitrary admitted pendant matrices and strictly positive denominators.
21. All explicit target matrices and rooted target realizations are admitted in their stated domains.
22. The claimed two-port mismatches therefore give complete observable leaf-law exclusions, not merely failure of one chosen reparameterization.

### E. Formal environment and certification

23. Choose and record an actual Lean/Mathlib revision and permitted build configuration when execution is admitted. The draft imports Mathlib but does not assert a tested version.
24. Elaborate every declaration, resolve notation/typeclass/import issues, and prove the named Claims as theorems from the actual finite semantics.
25. Audit transitive dependencies and all admitted assumptions. A partial scalar or matrix certificate cannot stand in for items A–D.
26. Bind a future verified build receipt to immutable source hashes, theorem names and the complete original statement. No such receipt presently exists.

## 7. Remaining trust and nonclaims

The current mathematical result depends on the written hand proofs and the explicitly scoped coordinating reviews. The formal trust dependencies above are all open; the packet does not ask a reader to accept an unproved adapter as an established theorem.

The portfolio G1/G2/G5 claims are not logical suppliers of the nucleotide observation result. [ADAPTER-AUDIT.md](https://github.com/Sodelin/Research-Commons/blob/ccfce26f04d6fabcd1ca1d9a03ca86a7b7d82227/research/2026-10-22-dot-phylogeny-root-blob/ADAPTER-AUDIT.md) recovers their exact scopes and rejects the direct import. G3/G4 remain open. No unknown source-size bound, unobserved chronology, generic-only hypothesis or mutation-to-genealogy inverse is silently used.

The requested mathematical investigation is complete at the stated hand-proof level. The next acceptance endpoint is a full, source-faithful formal proof and verified build, followed by a distinct historical-priority/correctness review before any stronger publication claim.
