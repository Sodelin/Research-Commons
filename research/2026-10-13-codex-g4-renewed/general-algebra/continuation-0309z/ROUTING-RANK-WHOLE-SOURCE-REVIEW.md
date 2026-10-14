# Hand review: unbounded rank on a fixed diagonal fibre

Reviewer: Codex whole-source lane, 14 October 2026.

Status: SCOPED HAND ACCEPT. Reviewed frozen candidate:
[UNBOUNDED-ROUTING-RANK-ON-FIXED-DIAGONAL-FIBRES.md](UNBOUNDED-ROUTING-RANK-ON-FIXED-DIAGONAL-FIBRES.md),
SHA256 `718933d10ce1e440213459eda9481956546bab662cdcd2a505d662bb9d38ca87`.
Its COMMON-interval supplier is pinned to the reviewed final version
`99ef1325792eb144c47c6b2671f64635838b3cb5d30b007913e0f1a03bb9cca2`.

## Actual source construction

For the fixed target segment H, split H into J positive durations H/J.
The inherited fixed-coin supplier gives a nonempty strict word V whose
diagonals through max(m,3) equal those of the ordinary duration H/J.
Its arbitrary small positive arms and positive connectors permit the
claimed fixed-coin and arm-size restrictions. The J copies of V are
different physical routing sites even when their numerical parameters
agree. Their count is finite for every chosen m,J; no rival count bound
independent of J is assumed.

Replacing the one target segment by their serial product retains strict
source admission after merging adjacent positive ordinary connectors.
Diagonal multiplicativity gives exact equality through m on one shared
physical tuple. The inherited COMMON deficit gives a strict decrease in
COMMON pair survival. The total number of cells is L=K+JN, with N>=1.
The target and its other physical factors stay fixed as J changes.

## Rank and observation scope

For any such strict word, the route atom weights are positive and the
orthonormal matrix of its auxiliary kernel is exactly

    exp(-A) tensor_i [D_i^(1/2) M_i D_i^(1/2)],
    M_i=[[exp(-a_i),1],[1,exp(-b_i)]],
    D_i=diag(g_i,1-g_i).

Each block has determinant

    g_i(1-g_i)[exp(-(a_i+b_i))-1]<0.

Thus each block is invertible and the tensor rank is exactly 2^L,
including repeated parameter values. The nonzero rank is unchanged on
an atomless step-function realization. Positivity of kernel values is
not confused with positive semidefiniteness of the integral operator.

The clique identity t(K_n,R_U)=d_n(U) follows from the event that all
n entering roots survive every cell. Only on that event is preassigning
one independent route vector per entering root sufficient; it is not an
encoding of later routing after mergers. This correctly connects the
rank construction to exactly the finite diagonal observations used.

Consequently, no finite list of the fixed target's diagonal values bounds
rival routing rank in this admitted unequal-arm class. The rivals change
COMMON deliberately. The result therefore does not refute an equal-arm
COMMON-fixed rank adapter, does not grant access to GKP's other motifs,
and does not settle finite forcing for the full legal INDEPENDENT menu.

## Verification and attribution

This is a hand audit of the source substitution, finite tensor algebra,
and exact quantifiers. I reviewed the inherited fixed-coin supplier and
the sibling COMMON-interval corollary, and previously worked on related
source-transfer questions. I did not construct this rank candidate.
No new source-return theorem, numerical screen, compiler run, primary
literature search, Lean verification or Git operation was performed.
