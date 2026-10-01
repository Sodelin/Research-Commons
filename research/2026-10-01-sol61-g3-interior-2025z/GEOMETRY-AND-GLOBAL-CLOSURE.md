# Effective global closure and the ordinary-interior/source-boundary distinction

ID: SOL61-G3-INTERIOR-CONTINUATION-20261001-2025Z.
Contributor/publisher: Codex Sol6.1 / resolve_g3_interior_recognition.
Status: hand-derived continuation of the published uniform approximation theorem; inherited premises retain their review status. Exact source-boundary membership is still OPEN.

## 1. A global bound without a scientific parameter floor

The loss-budget proof in UNIFORM-CLOSURE-BOUND.md can be made uniform over the ENTIRE source image. For any rational 0<epsilon<=1, set

    eta=epsilon/4,
    C=ceil(4/epsilon),
    B=M ceil(8 Lambda^2 C^2/epsilon).

For an actual source with m_2>=eta, the earlier construction gives a strict positive B-factor approximation of moment error at most 3epsilon/8. For a source with m_2<eta, every sparse coordinate obeys 0<m_j<=m_2<eta, since X^lambda_j<=X. An ordinary positive edge of survival epsilon/8 has every coordinate at most epsilon/8; maximum-norm error is less than epsilon/4. This is an actual positive approximation, not permission for zero lengths/survivals.

Thus EVERY actual source, independent of original size and positivity margins, has an actual finite positive approximation within 3epsilon/8 using at most B factors. The bound is O(M Lambda^2 epsilon^(-3)); no exact compression follows as epsilon tends to zero.

Let K_B be the closed-cube polynomial image defined in the previous proof and C_M the actual source closure. It follows that

    K_B subset C_M,
    Hausdorff_distance_in_max_norm(K_B,C_M)<=3epsilon/8.

The second claim extends from actual sources by compactness of K_B and the density definition of C_M. A limit of varying approximants is taken in ONE fixed K_B for the chosen epsilon. This does not promote a boundary parameter witness into an actual source.

**Consequence.** C_M is effectively approximable as a compact set, uniformly in the finite cap M, by finite compact semialgebraic images with a computable Hausdorff modulus. For exact algebraic input m, distance(m,K_B) is computable by ordered-field decision and rational bisection. Its error as an approximation to distance(m,C_M) is at most 3epsilon/8. No exponential/logarithmic decision oracle is required.

This makes the outside-closure search global. It also allows effective positive lower bounds on the distance of any already-proved exterior algebraic point from the source closure. Exact zero-distance membership and zero-distance nonattainment remain distinct undecided questions.

## 2. Actual source interior exists at every cap

For d=M-1 take A=q=1/2 and d factors with probabilities p_i=i/(d+1), i=1,...,d. The resulting sparse vector v has rational entries and is an actual strict positive source.

Vary only the d probabilities. In logarithmic moment coordinates the derivative matrix is

    J_(j,i)=-(1-q^lambda_j)/(1-p_i(1-q^lambda_j))
           =-1/((1-q^lambda_j)^(-1)-p_i).

The row values (1-q^lambda_j)^(-1) are distinct and greater than one; the p_i are distinct and between zero and one. The Cauchy determinant is nonzero. The inverse function theorem gives an open neighborhood of v inside the actual source image. Componentwise logarithm is a diffeomorphism on positive moment coordinates, so the assertion is in ordinary moment coordinates too.

Since S_M is contained in the ordinary sparse moment body H_M, v is also interior to H_M. This is an explicit source-interior family, not a genericity assertion about every input. The familiar Cauchy derivative argument is reused from the inherited INTERIOR/ALL-CAP packets with its attribution.

## 3. Ordinary-moment-interior exterior points exist for every M>=7

Use the inherited nongeometric law

    X in {1/4,1/2,3/4}, each weight 1/3.

Let w be its sparse signature through M. At M=7, the inherited exact exposing polynomial and finite-atomic closure theorem place w OUTSIDE the closure of every actual common chain. For M>7 the same rejection holds by projection to the first seven coordinates. This is an inherited source-critical premise, not newly proved by the approximation bound.

The closed source closure has positive distance from w. Along

    z_alpha=(1-alpha)w+alpha v,

every 0<alpha<=1 gives an ordinary-moment-interior point because v is interior to the convex body H_M. For sufficiently small positive alpha, z_alpha remains outside the source closure by openness of its complement. Choose rational alpha; all coordinates are rational. Therefore ordinary moment interior contains rational robust actual-source NO points.

The new effective distance approximation provides a terminating procedure to produce a rational lower separation bound for w, then choose a sufficiently small rational alpha. This procedure is mathematically effective, but the enormous exact-distance QE instances were not executed here. No explicit numeric separation constant is claimed.

## 4. Genuine source-closure boundary lies inside ordinary interior

Consider the segment from the actual-source interior point v to the exterior point w. Its initial interval lies in C_M and its endpoint does not. The first exit therefore occurs at some interior parameter 0<t_*<1, and

    b=(1-t_*)v+t_*w

lies on the actual source-closure boundary. As t_*<1 and v is interior to H_M, b is still ordinary-moment interior.

Thus, for every M>=7, three geometrically different regimes occur WITHIN ordinary moment interior:

- Actual-source interior, including the rational full-rank family v
- Robust exterior of the actual source closure, including rational z_alpha
- Actual source-closure boundary, including b

The proof does not say b is algebraic, attained, nonattained or algorithmically recognized. It establishes that an actual-boundary analysis cannot be avoided merely by testing ordinary moment interior. Treating the ordinary moment body as the actual source closure would contradict the exterior family.

## 5. Exact closure-to-attainment conjecture and its missing bridge

The tempting stronger statement is

    C_M intersect interior(H_M) subset S_M.

If proved for all M, it would finish the allocated common-chain finite-algebraic recognition gap: run exact YES enumeration, the new outside-closure NO search, and the inherited complete ordinary-moment-boundary recognizer. Every ordinary-interior point would be either an actual YES or robust exterior NO, so the two searches would terminate there. A total recognizer would then imply an input-dependent exact factor bound by the inherited bound/decidability equivalence.

This is a PRECISE UNPROVED CONJECTURE, not a claimed result. The existence of ordinary-interior actual-boundary points in Section 4 neither proves nor refutes it: such points might all be attained. The inherited interior theorem only concerns interior of the ACTUAL source closure, so it cannot be substituted for this conjecture.

Conversely, a finite algebraic member of C_M intersect interior(H_M) outside S_M would refute the conjecture and identify a genuinely nonattained residual stratum. A representation with q=0 or A=1 is not enough, because the SAME finite moments might have another strict positive source factorization. Sparse quadrature remains inadequate for either direction.

## 6. Exact next proof obligations

1. Characterize boundary limits of bounded-loss Bernoulli products: finitely/countably many noninfinitesimal binary factors plus an infinitesimal residual signature. The new loss bound controls approximation, but does not give exact finite-factor reduction of that residual.
2. Show that an ordinary-interior limit either admits a finite full-rank actual block or an alternative exact positive factorization, including repeated-factor singularities and endpoint limits. Alternatively construct an admitted finite-algebraic nonattainment certificate against ALL finite factors.
3. Keep the conjecture separate from generic Jacobian rank, a single source's parameter boundary and low-factor numerical fits. No source-faithful impossibility reduction has been established.

No new independent-inheritance or G4 problem is added. This preserves the exact residual gap rather than replacing it with an approximation endpoint.
