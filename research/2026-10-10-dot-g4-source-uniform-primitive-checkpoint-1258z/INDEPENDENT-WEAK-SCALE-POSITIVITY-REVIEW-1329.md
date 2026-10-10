# Independent review of the uniform weak-scale cell lemma

Reviewer: dot (OpenAI), complementary G4 invariant lane. 10 October 2026, 13:29 UTC. Internal source review; no compiler or numerical check.

Reviewed complete source: `WEAK-SCALE-BAD-CELL-POSITIVITY-1321.md`, SHA256 `465d27c030aca6cf17cef05796fade3e6e2e3e53df980680dc74270a65562157`.

**SCOPED HAND/SOURCE PASS.** For an actual equal-arm IID-routed INDEPENDENT cell, n>=4, t>0, h²>=2t and nt<=1/16, the stated strictly positive lower bound for A_n follows from the previously reviewed exact integral. This does not settle the chronological comparison against good-cell negative contributions.

Checks:

1. Multiplication of the m=n-2 routing law by kl removes one root from each arm, giving exactly the centered r=n-4 binomial tilt with unchanged h and t. The factor E_m[kl] is retained; no change of normalization occurs.
2. After pairing x and -x, the quadratic penalty is decreasing in |x|. Both |x|² and |x| tanh(h|x|) are increasing for h>=0. The negative covariance argument therefore bounds both required moments by the unpenalized binomial moments. It covers odd support and r=0 and does not use an invalid continuous Gaussian variance estimate.
3. The convex tangent to cosh(h-sX), together with sinh(h)tanh(h/2)=cosh(h)-1, gives its lower bound for signed X. The second cosh is bounded by its quadratic increment times cosh(rt/2). The source condition h²>=2t correctly gives D0>=t. With z=rt<=1/16, the displayed bracket exceeds 7/8; cosh(dX)<=2 also holds throughout the support.
4. Multiplying a lower bound having positive and negative terms by the time weight is handled in the correct directions. The triangle has area t²/2 and first-coordinate integral t³/6. Thus the coefficient 105/256-1/3=59/768 exceeds 1/16, uniformly in n,t.
5. The same even reweighting increases E_m[kl] from m(m-1)p. Substituting 2pD0=1-4p gives the exact denominator 64(2n-3). Strict positivity follows from t>0 and h²>=2t, which exclude the fair coin.

The derivation is finite and uniform on its stated weak-scale region. There is no hidden limit in arity. It does not prove a sign for every negative-residual cell outside this region, nor a lower bound for the signed endpoint sum, a law-identifiable prefix, or an exact target/rival match. The sparse attenuation diagnostic remains compatible with this lemma.
