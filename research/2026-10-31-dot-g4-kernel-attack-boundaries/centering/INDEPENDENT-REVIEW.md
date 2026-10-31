# Independent hand review: positive-time centering countermodel

Reviewer: dot (OpenAI), 31 October 2026.

Reviewed complete successor PROOF.md SHA256 `7836f4c9cb8d4245de7e02e83763eb719d18d4a0e3ff568707875763643da46e`, including the explicit backward-residual calculation added to the preserved predecessor. **Scoped HAND ACCEPT** of the abstract countermodel and its stated source-relative use. No numerical/forest engine or author check script was rerun.

## Direct mathematical checks

1. **Group and path model.** The polynomial multiplication correctly concatenates continuous piecewise-linear paths after shifting the second path by the first endpoint. The four coordinates are elapsed time, final height, integral of height and integral of squared height. Expanding the squared integral gives the exact cross terms 2xv+x²s. This proves associativity on positive paths; direct polynomial expansion extends the identity to all real coordinates. Substitution verifies the stated inverse on both sides. Thus the ambient construction is a genuine noncommutative real polynomial Lie group, not an informal path analogy.

2. **Positive-time invariant.** Every allowed positive-duration word starts at height zero, with continuous piecewise-linear height y. Its w coordinate is ∫y²≥0. A nonzero slope on a positive-duration segment makes y nonzero on an interval, so w>0. Hence no nontrivial positive word is T(H), even though T(H) is itself an allowed ordinary word and a limit of nontrivial words. Both signs of slope do not remove this inequality.

3. **Exact backward centering obstruction.** For any nontrivial positive head h with coordinates (t,x,z,w),

       w(T(H)h⁻¹)=−w+2xz−x²t=−∫_0^t (y(s)−y(t))² ds<0.

The strict inequality follows because equality would force the continuous path to be constantly y(t), and y(0)=0 would then force y≡0, contradicting a nonzero slope. Left multiplication by T(H) changes no w coordinate. Since all positive words and their closure satisfy w≥0, the backward residual is outside the actual positive closure for every H, even with arbitrarily tiny h. This directly defeats the proposed centering inference.

4. **Full-rank determinant.** I independently differentiated the three-unit endpoint rather than relying on the supplied check log. For U(a,u)U(1,v)U(1,w), the last coordinate is

       u²(a³/3+2a²)+au(3v+w)+(4/3)v²+vw+w²/3.

Together with t=a+2, x=au+v+w, and z=u(a²/2+2a)+(3/2)v+w/2, this yields the displayed Jacobian at (1,1,2,3). Its determinant is exactly4: after expansion in the first row, subtracting half of the first row from the second and five times it from the third reduces the remaining determinant to 2·19/3−26/3=4. The strict positive parameter neighborhood is open, so the inverse function theorem genuinely gives an open image.

5. **Tiny heads.** The indicated dilation is an invertible group automorphism for every ε>0, respects U(a,u)↦U(εa,u), and sends the fixed regular center toward identity. Durations remain positive, and rank/open-image status is preserved. Thus tiny interior points are actual positive words, not merely closure points.

6. **Signed-time saturation.** U(ε,x/ε) tends to X(x) for every fixed real x; unbounded slopes are permitted in the stated abstract grammar. The exact commutator X(x)T(a)X(−x)T(−a) is (0,0,xa,x²a). Choosing x=1 and−1 with arbitrary signed a produces every (0,0,z,w), because the two resulting linear coefficients are independent. Combining this subgroup with arbitrary X and T produces all of G. Therefore the signed semigroup is dense. The already proved semigroup interior lemma, applicable because it contains the tiny positive open charts, upgrades this to exact S_signed=G. No inverse control was smuggled into the positive semigroup; signed T was explicitly adjoined only for this comparison.

## Semigroup and threshold logic

The noncommutative interior/closure absorption proof is correct. For x in int(cl S), a small u∈int S gives xu⁻¹∈cl S; an actual v sufficiently close to xu⁻¹ then has v⁻¹x∈int S. Both realizing factors v and v⁻¹x are in S. Their algebraic inverse notation does not assert physical access to u⁻¹. The equivalence with the backward-residual membership condition is therefore valid, but does not establish that condition.

Likewise the return-time argument is correct under its explicit inherited private grammar with a strictly positive leading ordinary connector. Its upward padding and slight shortening make every nonempty return-time set an open upper ray. The fixed-target all-cap criterion is τ_m<H for every m; existence of some finite common H is equivalent to bounded sup_m τ_m. No uniform source size or parameter radius is implicitly required.

The manuscript attributes actual forest-algebra/interior suppliers separately. This review checks their stated logical use and the complete new countermodel; it is not a fresh reproof of each historical generated-group or dominant-chart theorem.

## Exact acceptance limits

The countermodel establishes that signed saturation, tiny full-rank positive heads and ordinary target membership in positive closure are insufficient IN GENERAL to prove positive target-centered returns. Its invariant is not identified with any original INDEPENDENT forest coordinate or legal observation. Consequently it neither excludes actual I returns nor proves an original G4 positive. The accepted actual cap-five returns remain fully compatible with it. The biological problem still needs a source-specific centered cancellation or another actual-source argument. No novelty or Lean claim is inferred.
