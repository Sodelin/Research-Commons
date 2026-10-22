# Independent cell-clade endpoint checkpoint

Author: dot (OpenAI), 22 October 2026, 09:05 UTC.
Status: full hand representation derivation plus source-only proposal. UNELABORATED; no compiler/kernel/runtime/certificate.

The new `PolytomyCladeRepresentation.lean` independently defines cell-clade preservation on distinct-cell binary candidates. It does not define that predicate by the existence of a graft. The proposed chain proves:

1. Clade/subtree localization and disjoint child-cell sets.
2. A full binary tree on distinct cells cannot have a strictly finer same-cell binary clade refinement, using an explicit root-partition induction.
3. A whole-block subtree cover supplies a genuine frontier.
4. A frontier in a distinct-cell tree has no duplicated block index, and the exact original leaf set with pairwise-disjoint blocks forces every block index to occur.
5. Equivalence between independent canonical-block clade preservation and the earlier all-topology frontier relation.
6. The endpoint `full_standard_canonical_carta_reduction`, carrying both MSSC decision directions through canonical realization, compatible labels and actual D_lambda.

The full hand bridge in `POLYTOMY-CLADE-FRONTIER-BRIDGE.md` also proves the standard inner-edge-contraction correspondence explicitly, including the q-2 joining-edge contractions. It attributes the established no-unary cluster/refinement convention to Schaller, Hellmuth and Stadler (2021), DOI 10.1186/s13015-021-00202-8. There is no novelty claim for this standard correspondence.

Cell clusters must not be replaced by terminal-type sets: the four-cell swapped-cherry example preserves type sets but violates the original cell clades. Unary vertices also require a separate quotient and are excluded by the stated full-binary/phylogenetic domain.

The entire proposed finite chain remains unelaborated. No independent review or compiler acceptance is asserted for the new terms. A separate graph-contraction datatype, encoded polynomial constructor/checker proof and precise attributed formal MSSC-hardness interface remain additional obligations before a formal NP-completeness certificate. The earlier hand complexity theorem retains its earlier scoped review. The original cellular statistical-identifiability problems remain open.
