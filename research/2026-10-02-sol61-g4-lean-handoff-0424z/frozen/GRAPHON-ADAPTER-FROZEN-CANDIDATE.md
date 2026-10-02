# Frozen G4 graphon-adapter candidate

Contributor: GPT-6.1 Sol, 2026-10-02. Hand candidate awaiting independent review and Lean. Frozen at the user's Lean-first direction; no unrestricted stopping theorem is asserted.

## Prior-art check and motivation

Pinpoint primary-source screen, 2026-10-02, not an exhaustive literature review. [Lovász and Sós, Generalized quasirandom graphs, JCTB 98 (2008) 146–163](https://users.renyi.hu/~sos/2006_Generalized_quasirandom_graphs.pdf), Theorems 2.1–2.3 and Section 4.6, proves finite forcing for finite weighted graph models. The basic constant case uses edge and four-cycle densities. [Lovász and Szegedy, Finitely forcible graphons](https://arxiv.org/pdf/0901.0929), Sections 1–2 and Claim 2.4, describes the graphon/positive-moment formulation and attributes step-function forcing to the earlier result. The primary [EuroComb 2023 paper, Forcing Generalized Quasirandom Graphs Efficiently](https://journals.muni.cz/eurocomb/article/download/35604/31481/58994), Theorem 1, improves the forcing graph-size bound to 4q²-q for q-step kernels, q>=2. The journal HTML retrieval failed, so only the accessible primary proceedings theorem was read, not its full journal proof.

These results require general simple-graph densities. The G4 private source needs a faithful original-response adapter before invoking them. The candidate below checks that missing premise.

## Supplied-chain hidden graphon and its useful rank

For a supplied chain with L private independent bigons and ordinary survival product Z, give color c in {1,2}^L the product weight p_c of its original routing probabilities. Set

    W_cd=Z product_i [x_i if c_i=d_i=1;
                     y_i if c_i=d_i=2;
                     1 otherwise].

On the NO-MERGER event, current roots stay distinct, so their color vectors are independently drawn and the no-merger probability is exactly t(K_n,W). This is the existing hidden-color diagnostic presentation in graphon language. It does not turn hidden colors into available observations.

Each factor matrix [[x_i,1],[1,y_i]] has nonzero determinant x_i y_i-1. Their tensor product is invertible, and all color weights are positive. Consequently the positive-weight integral operator has rank exactly 2^L. A correct finite forcing adapter could therefore force L against unknown longer rivals; the accepted bounded-length normal-form/QE procedure would then handle serial order.

W itself forgets serial order and ordinary-pad placement. The published positive pair E(1/3) B_* E(1/2) and E(1/2) B_* E(1/3), B_*=(2/3,1/3,1/2), has the same W but different complete forest kernels at five roots. Thus graphon forcing alone would not replace ordered-law recovery.

## Candidate linear-adapter obstruction

Scope: a fixed finite linear combination of original passive legal response coordinates, with coefficients and known exterior parameters independent of the unknown source parameters. The typed source occurs once. No repeated unknown box, tied copy of an unknown arm parameter in the exterior, hidden routing observation, or data-dependent nonlinear reconstruction is included.

For a single private bare bigon, every finite full forest coordinate is a polynomial in x and y with each separate exponent in

    Lambda={0,1,3,6,10,...}, lambda_j=j(j-1)/2.

Reason: the physical ordinary population on each arm is used once, and its finite Kingman transition expansion contains only x^lambda_j, respectively y^lambda_j. Routing and known exterior compilation do not change these original-variable exponent sets. Any fixed finite legal completion and any finite linear combination preserve this property, regardless of the copy cap. Fix the two positive normalized ordinary pads and g=1/2.

For any simple graph F, its hidden-graphon density on that padded one-bigon source is

    t(F,W)=Z^|E(F)| sum_(S subset V(F))
             2^(-|V(F)|) x^|E(F[S])| y^|E(F[V(F)\S])|.

All coefficients are positive. If F is not one clique plus isolated vertices, it has an induced subgraph with exactly two edges: an induced three-vertex path if a nontrivial component is not complete, or two disjoint edges if two components contain edges. Hence t(F,W) has a nonzero monomial with x exponent TWO, which is not in Lambda. Polynomial equality on the open positive (x,y) square is therefore impossible with the preceding legal linear span.

Conversely a clique plus isolated vertices has density t(K_n,W)=s_n, available through the inherited legal finite tomography. Subject to the source/compiler dependency above, this characterizes precisely which simple-graph homomorphism densities have a universal finite LINEAR original-response synthesis over this source class: cliques plus isolated vertices.

In particular the four-cycle density needed in basic graphon forcing has no such source-faithful finite linear compiler at ANY cap. Adding known exterior populations, allowing more copies, or applying an invertible linear recoding does not supply it.

## What this candidate does not establish

It does not exclude a nonlinear or data-adaptive finite adapter. Recovering a supplied bare triple and then computing a graph moment uses its shape promise; it does not provide a rival-wide unknown-length compiler. Products of different exact response values also fall outside the linear claim and need separate analysis.

This is a route-specific source-adapter obstruction, not one fixed source with exact replicas after every finite response prefix, not undecidability, and not unrestricted G4 completion. Its candidate proof still needs independent source-critical review and formalization of the full response-polynomial support statement. At the freeze, no additional graphon experiments or theorem transfer were undertaken.
