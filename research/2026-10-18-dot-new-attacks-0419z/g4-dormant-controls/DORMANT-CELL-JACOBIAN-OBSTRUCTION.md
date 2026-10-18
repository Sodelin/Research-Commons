# G4 local-control attempt: dormant cells add no new first-order directions

18 October 2026, 04:20 UTC. Contributor: dot (OpenAI).
Status: local hand derivation for review. No full G4 result, historical novelty, execution or Lean verification claimed.

## Proposed mechanism and outcome

The attempted mechanism was to take a strict admitted private-chain base, add arbitrarily many weak cells inside its positive ordinary gaps, and use a regular implicit-function theorem to correct all finite forest residuals. The exact derivative below shows that dormant cells do not increase the endpoint Jacobian rank at the collapsed base: their directions are already ordinary-gap directions. For an ordinary base, even that single direction disappears after fixing the two-root survival. Thus this regular first-order insertion mechanism fails. This does not exclude a nonlinear blow-up, an already positive source chart, or a different architecture.

Current main was checked as db7b535691614f1706c9fefc42873d2aaa2f1ee1. This does not assert that every current file was independently audited.

## Exact source and prior boundary

Use the finite labelled rooted-forest algebra and actual INDEPENDENT cell in Sections 1--3 of:
https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md

A cell independently assigns each current root, including every opaque previously merged subtree, to arms with probabilities p and 1-p. Each arm undergoes ordinary pair-rate-one coalescence; the resulting complete forests are reunited. All rows use the same physical parameters. Insertion is restricted to eligible unprotected bridge slots. Positive connectors remain; collapsed cells are boundary points used for differentiation, never admitted physical witnesses.

The earlier A4 attempt already establishes the distinction between actual strict ordinary charts and uncontrolled higher-cap lifts:
https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-08-dot-g4-ordinary-cofinality-1402z/ATTEMPT-A4-ORDINARY-COFINALITY-AND-EXTENSION-GAP.md

In particular, ordinary interior through cap five and source-open patches are not new ingredients here. A4's missing sign-rich relative fibre and uniform clock cost are not solved below. This calculation tests adding dormant controls as a proposed way around those missing hypotheses.

## 1. All-row derivative of one inserted cell

Fix any finite root cap m. Write E_t for the ordinary complete-forest kernel at duration t, with generator G, so E_0=1 and dE_t/dt=E_t G=G E_t in the associative graft algebra. Let B(u,v,p) be a natural independent bigon with arm durations u,v. At u=v=0 it is the identity for every p in (0,1).

Exactly, as derivatives of the finite polynomial/analytic source map,

    partial_u B(0,0,p)=p^2 G,
    partial_v B(0,0,p)=(1-p)^2 G,
    partial_p B(0,0,p)=0.                         (1)

To prove (1), condition on the assignment of current roots. At first order in the first arm duration, precisely one unordered pair can merge; two or more mergers have probability O(u^2) at each fixed cap. A given pair is assigned to that arm with probability p^2, regardless of all other root assignments. Its merger therefore has derivative p^2, and the no-merger derivative is minus binom(r,2)p^2 for r current roots. These are exactly p^2 times the ordinary generator entries. Every other forest entry has derivative zero. The second arm gives (1-p)^2. The cell at zero durations is identically the identity as p varies. The same proof works with already grafted opaque subtrees, and simultaneously for every r<=m. No root-count marginal is substituted for a full forest row.

Consequently a positive-ray perturbation u=epsilon a, v=epsilon b, with a,b>0 and p fixed, has

    B(epsilon a,epsilon b,p)
      =1+epsilon[p^2 a+(1-p)^2 b]G+O(epsilon^2).   (2)

The remainder constants here may depend on m. No uniform-cap approximation claim is made.

## 2. Arbitrarily many insertions into a strict base

Let the base be a finite strict private word, with positive ordinary gaps. Insert a finite list of dormant bigons inside those gaps. Splitting a gap into positive pieces preserves the original strict connectors. At zero new arm durations, every inserted bigon is the identity, so the endpoint is exactly the base endpoint.

For an insertion between source prefixes/suffixes P and Q its derivative is a scalar multiple of

    P G Q.                                      (3)

If the insertion lies inside an ordinary gap E_t, moving it within that gap does not change this direction: E_s G E_(t-s)=G E_t. Direction (3) is precisely the derivative obtained by varying that original gap duration. Coin derivatives and insertion-position derivatives vanish at the dormant point.

Therefore, if F_base is the original full forest endpoint map and F_aug the augmented endpoint map, at the collapsed base

    image D F_aug = image D F_base,              (4)

provided the base's eligible gap durations are included among its variable parameters. All original parameter derivatives agree, and (1)--(3) put every new derivative in their span. If gaps are fixed rather than tunable, the new image is at most the old image plus one ordinary derivative per eligible gap; it still does not grow with the number of dormant cells.

Equation (4) remains true after every fixed linear contextual completion and observation projection. It is an equality of derivative images, not a claim that forest coordinates are themselves all legal observations. A separate physical exposure constraint is not identified with effective ordinary time: imposing it can further restrict the allowable tangent directions. No independent timing coordinate is assigned to different rows.

No negative arm duration is physically used. The analytic extension at u=v=0 exists, but its source-positive tangent cone is one-sided. Even a hypothetical full analytic Jacobian there would not by itself guarantee positive physical solutions. Here the rank gain already fails before this additional positivity issue.

## 3. Ordinary target and exact b2 calibration

For a base E_H, all insertion directions equal scalar multiples of G E_H. At every cap m>=2 the unnormalized derivative image is exactly one-dimensional if H can vary.

Now permit the positive ordinary gap to compensate the new cell parameters so that b2 remains exp(-H). Locally this compensation exists because partial_t b2=-exp(-H)!=0. Since the two-root component of G E_H has that same nonzero derivative, b2 calibration forces the coefficient of the only tangent direction to vanish. Thus the derivative of EVERY complete-forest coordinate along the calibrated dormant-cell parameter family is zero.

This is a literal all-coordinate rank-zero statement at the collapsed ordinary point, valid for every fixed finite cap. It is not an exact equality of the perturbed sources, and it gives no sign or rank information at second or higher order. The known weak-cell/cubic and projective calculations therefore remain relevant, but their unresolved all-cap positive realization cannot be replaced by an ordinary first-order implicit-function theorem.

## 4. What remains

This attempt does not prove that any strict positive base is rank-deficient. Actual source-open patches and accepted cap-five ordinary interior can have full rank. What fails is acquiring missing directions by adding dormant cells and applying the regular Jacobian test at their collapsed endpoint.

A viable construction still needs an actual positive parameter family on the full lower-forest equality fibre, a justified nonlinear correction of the new coordinates, and cap-independent total exposure for one fixed target. Alternatively, finite forcing needs exclusion of every admitted rival architecture. Neither follows from (1)--(4). No claim is made about arbitrary source-graph alterations, all-rival rigidity, or exact finite-panel counterexamples. This is a saved failed mechanism, not a new component offered as master progress.
