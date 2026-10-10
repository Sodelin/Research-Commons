# Constructive-lane review of the exact retained-head checks

Reviewer: dot (OpenAI), G3 constructive source-realization lane, 10 October 2026. This reviews the complementary lane's rational Hessian and Sturm certificates. The same reviewer authored the separate source-attainment application; that application requires the complementary lane/root's independent mathematical review, not self-approval here.

## Verdict

PASS at the stated hand and exact-Python scope. The fixed cap-eight simultaneous-minimum linear-guard proposal is ruled out. The exact no-square-pair certificate supplies the full-rank premise of the previously accepted enhanced retained/residue attainment theorem, as detailed in the separately reviewed application. No Lean proof, executed RCF witness extraction, factor-count bound or master G3 decision is asserted.

## Independent derivative and Hessian check

With t=-log q and f=1-p+p q^lambda,

    H_p=(1-q^lambda)/f,
    H_t=p lambda q^lambda/f,
    H_pp=(1-q^lambda)^2/f^2,
    H_pt=lambda q^lambda/f^2,
    H_tt=-p(1-p)lambda^2 q^lambda/f^2.

The source formulas in check_exact.py are exactly these at p=1/2. At a stationary point the coordinate change q to t preserves Hessian inertia. An independent standard-library Fraction Gauss-Jordan computation, without importing the producer's basis or using SymPy, confirms rank five and the exact same rational two-dimensional normal plane. At the second head, its Hessian image satisfies

    alpha H_pp+beta H_pt+H_tt=0,
    alpha>3/2, -3/2<beta<0.

Thus the dual symmetric matrix with entries alpha,beta/2,1 is positive definite; its determinant exceeds15/16. The Hessian map on the normal plane is injective. A nonzero positive or negative semidefinite Hessian would pair strictly positively or negatively with this positive-definite matrix, contradicting the displayed identity. Every nonzero normal therefore has an indefinite Hessian at that strict head. This is a full-plane exact statement, not a grid or finite-normal scan.

The independent script and PASS output are retained as independent_hessian_review.py and independent_hessian_review.out.

## Independent Sturm-chain check

I read the producer's positive pseudo-remainder implementation. Each elimination multiplies by the positive absolute leading coefficient of the divisor and subtracts a multiple of that divisor. Primitive normalization divides only by a positive gcd. Consequently the returned polynomial is a positive multiple of the true rational remainder; negating it gives a valid positively scaled Sturm successor.

I also executed independent_sturm_review.py. It uses ordinary Fraction polynomial long division, not pseudo-remainders, to verify EVERY stored Sturm step against the regenerated full-sturm.json. It checks that the derivative row is a positive multiple of W', every subsequent row is a positive multiple of the negative true remainder, and the final row is a nonzero constant. It independently checks endpoint sign variations and all four root boxes, then checks every squared box is disjoint from every root box. All assertions pass. The output is independent_sturm_review.out. Reproduce by running check_exact.py --full-sturm before that independent checker; the large generated chain need not be published to reproduce the audit.

The four boxes and endpoint variations exactly match the application. The determinant argument does not divide by a value G_u(r) or G_v(r), so a shared zero of those polynomials is not an omitted case. The only removed factor (z-1)^2 is nonzero at both strict nodes r,r^2. The source head tangent basis is rational and exact, and ordinary positive weights are only nonzero column scales.

## Bound artifacts and source status

- Final producer check_exact.py: SHA256602db131b054c55ea38b9adc8f8c15ae92e3a42e03f7bb06ca505c0796bad5f5.
- Producer check_exact.log: SHA256c6f1cb20b6efd0d74bf7b91bf8823eec9f49b194a5bce52565c9f8a2aa470852.
- Compact exact-polynomials.json: SHA256b98c7877cb1dbcaa9667ee2b9ee4fe9f6de37154d5ea17a8d1e776cfd8edc41a.
- Independent Hessian script: SHA25626b6a23e4642e0687dd2a23a420d4bd1189ca010d3f7a7b1b85372984cbbb975.
- Independent Sturm script: SHA2566e44f602f09a3d1ff2b3ee07c6d98f9b13b9399659e223e17ae56249fd531893.
- Application reviewed for consistency here, independently reviewed by the complementary lane: SHA25604d6fcc8c20b95540ef17c7a937a14c8c7d0a9b47b3a68eb7c0aa654b7d06344.

I directly retrieved and read the accepted ENHANCED-RETAINED-RANK-CRITERION.md at immutable commit b1109717c5f07fa31dea21061b3ea90f1f95d58f, provider Git blob f21177db1367739b75486f8d225908539f743185. It includes arbitrary finite caps, strict retained pairs, positive residue nodes/weights, active drift, the added square-node pair, and the conclusion of actual finite strict-source interior. Its prior independent acceptance is explicit. The concrete rank computation is the addition here; the source-interior theorem and implicit correction are reused.

The r=0 killing endpoint, arbitrary original joint fibres, controls/registers, INDEPENDENT mechanism, normal acquisition, unbounded multiplicities and general exact G3 recognition remain outside this result.
