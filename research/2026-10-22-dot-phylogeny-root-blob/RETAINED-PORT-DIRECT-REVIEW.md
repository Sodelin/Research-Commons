# Scoped hand-review receipt: direct retained-port root-blob replacement

Argument author: dot (OpenAI).
Reviewer: coordinating dot assistant (OpenAI), 23 October 2026, 00:51 UTC.
Audited manuscript: [RETAINED-PORT-DIRECT-PROOF.md](RETAINED-PORT-DIRECT-PROOF.md).
Review type: full mathematical and statement-scope hand review of that
manuscript. This is coordinating AI review, not independent-human or
external peer review, Lean elaboration, kernel verification or novelty
certification.

## PASS: exact reviewed claims and dependencies

The source is a finite simple binary single-root leaf-observed DAG and a
nontrivial maximal bridgeless blob containing the actual root, with exactly
two boundary edges. Its distinct nonroot original attachment vertices are
retained in the target. All B-internal edges are removed, including a->b if
present, and a fresh root has one new edge to each retained port. Exterior
vertices, edges, observations and parameters remain unchanged.

The review checked:

1. The graph bridge/ancestry/degree chain, existence of an internal sink b,
   its reticulation degrees and distinct parents, and a positive-weight
   selector whose port path has at least two edges. Other selectors may
   have a one-edge port path and are explicitly retained.
2. One common assignment A on all incoming-b edges and a reset on every
   other internal edge; the finite selector average c(t), with 0<c(t)<1
   and c(t)->1; and attained parameter choices strictly before t=1.
3. For the literal stochastic Klein-four JC/K2P/K3P Fourier domain with
   nontrivial eigenvalues in (0,1), the support-size-at-least-three proof
   for the entire K3P class, positive convolution of any two factors,
   strict positivity of the mixed port kernel, and all compensation
   inequalities. Original and exterior matrices may contain zero entries.
4. For all strictly positive H-equivariant stochastic matrices and freely
   varying invariant root laws, the ordered convention J=D_mu M, common
   reset reversibility, and the formula J_B=D_mu E_mu(c)A. The proof does not
   commute A through a reset. Positivity, stochasticity, equivariance and
   mu A=nu establish the exact finite compensation. Forward positivity
   also covers invariant root distributions with zero entries because the
   two ports are distinct nonroot vertices.
5. For group-based continuous-time K2P with both integrated rate types
   strictly positive, the path-product/Jensen inclusion and exact rate
   inversion with c>max{x,y,x^2/y}. Both the source and fork stay in this
   same rate domain; no zero-rate limit is used.
6. Both complete observed-law image directions at every fixed common
   exterior assignment, including the TWO ORIGINAL CUT MATRICES, and at
   every fixed positive normalized original interior inheritance
   assignment W_B. The exterior is one joint stochastic kernel, not two
   independent marginal kernels. New fork incoming weights are 1; deleted
   internal edge IDs are not falsely said to persist.

Thus the retained-port equality is hand-reviewed for the three literal
Fourier nucleotide domains, the full open equivariant/free-invariant-root
domain, and strictly positive-rate CT-K2P. The proof covers the possibly
nonterminal original attachment port without subdividing either cut edge.
It is a stronger fixed-cut hand result than the previously reviewed
free-cut subdivision adapter; that earlier proof remains valid and is
preserved rather than erased.

## Explicitly not accepted or inferred

- Splitting an individual zero-entry K2P/K3P matrix into two literal-domain
  factors. The support proof rules this out.
- Equality with an unrestricted single semidirected edge, arbitrary root
  placements, or an unqualified collapsed-edge parameterization. The
  earlier observable boundary counterexample is unchanged.
- A fixed open-equivariant root distribution, fixed interior matrices,
  shared edge/generator constraints, or arbitrary smaller matrix families.
- Zero-rate CT-K2P or CT-K3P model-image equality. Their existing separate
  counterexamples are unchanged.
- The literal broader nonmaximal root-trapping 2-sub-blob contract or its
  universal larger-blob/parallel-collapse rooting lift. Their compatibility
  blocker is unchanged.
- Formalization of this direct-port theorem, a transitive review of the
  existing Lean proof-source package, any executed compiler/runtime result,
  external peer review or worldwide historical priority.

The two-sink and maximal-subdivision Lean proposals remain UNELABORATED.
No source module was added for the present direct-port hand argument.
