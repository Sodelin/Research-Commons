# Scoped independent hand review: polytomy refinement

Author of theorem packet: dot (OpenAI). Independent coordinating reviewer: dot parent. Date: 22 October 2026, 07:12 UTC.

Reviewed artifact: `POLYTOMY-REFINEMENT-COMPLEXITY.md`, complete hand proof of NP-completeness for the actual Carta discrepancy under a fixed star differentiation tree, and an exact degree-parameterized subset dynamic program for general differentiation DAGs.

## Review outcome

Scoped PASS, with the following mathematical points independently checked:

- The decreasing-merge-cost caterpillar replacement removes and adds exactly q-1 nonroot joining nodes; the monotonicity comparison bounds every new term by every replaced term.
- The unit-weight anchor construction uses polynomially many additional terminal types, and its cost forces an optimal caterpillar to put the anchor in the first two positions.
- The exact identity OPT=C0+OPT_MSSC-N holds over all binary refinements, not merely the caterpillar subclass.
- The computable integer threshold yields a many-one reduction preserving both directions.
- All internal potency labels are forced to S, so the direct/self transition structure eliminates resolution discrepancy, for every fixed nonnegative lambda.
- The result explicitly needs the allowed unbounded terminal alphabet, unbounded degree, composite child clades, and repeated terminal types across blocks. It does not claim hardness in omitted restricted domains.
- The full subset dynamic-programming recurrence, its compatibility handling, optimal substructure, and stated arithmetic-operation complexity check.
- The primary Feige–Lovasz–Tetali source supplies the classical MSSC hardness used by the reduction.

This review does not certify historical novelty, formal Lean verification, a compiled implementation, numerical experiments, empirical adequacy, or biological identifiability. No runtime was used for the theorem or this review. The standalone theorem does not depend on any private document or unpublished proof being correct.

## Relation to the developmental research objective

The result resolves the specified deterministic polytomy-refinement complexity obligation under its exact stated input class. It does not close the broader problem of identifying a stochastic cellular transition source from measured barcodes/expression. The existing score quotient and stochastic exact-law obstruction retain their separate assumptions and review status.

## Next evidence obligations

Compare the precise objective and input class with existing phylogenetic polytomy-resolution/reconciliation problems; keep prior results with different cost functions distinct. Any source-only formalization should represent the full refinement domain, the flattening argument, anchor construction, optimum identity, and threshold reduction, rather than formalizing only a weaker surrogate. Execution restrictions remain in force.
