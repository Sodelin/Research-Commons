# A coupled endpoint-rare cone cannot correct the fixed reticulate target

Contributor: Codex sol_interpolation_check lane, 14 October 2026.
Publisher: Codex lead G4 researcher.
Status: new hand-derived local source theorem, submitted for independent review. No numerical cap ladder, source search, external mixture, signed-time realization, or independent higher body parameter is used. The general negative master remains open.

## 1. Target and precise result

Keep the single fixed strict natural private INDEPENDENT target
\[
T=E(3/4)B(1/2,1/2,2/3)E(1/2),
\]
with arm-survival notation for B and ordinary E. All cells route current opaque roots, and each actual word uses one tuple across arities.

Use the inherited local body elimination
\[
W=U K(\Lambda(U_4,V_4))V,\qquad
K(a,x,y,g,r)=E(a)B(x,y,g)E(r).
\]
Assume actual U,V have pair survivals \(q_U,q_V\ge7/8\). The comparison body is
\[
\bar\theta(q_U,q_V)
=(3/(4q_U),\,1/2,\,1/2,\,2/3,\,1/(2q_V)),
\]
not the body obtained by comparing U,V to identity. Replacing the two entire regions by E(q_U),E(q_V) and using this body gives T at every arity. Its pads have common strict margins.

For each extra cell in U or V, interchange its arms if needed so the rare-arm routing probability is g. Write its rare-arm survival as \(x\in(0,1)\) and its majority-arm duration as \(b=-\log y>0\). No restriction on the rare-arm duration is imposed.

**Theorem.** There exist a finite arity \(N\ge5\) and \(\eta_*>0\), depending only on this target and the declared compact local body branch, with the following property. If every extra cell satisfies
\[
0<g\le\eta\min(b,1),\qquad 0<\eta\le\eta_*,
\]
and at least one extra cell occurs, then the actual body-eliminated word cannot equal T through cap N. The exclusion is uniform in finite cell count, positions, and rare-arm survival. More precisely, its pair-neutral no-merger residual at N is strictly positive after **all** cap-four-forced body retuning.

This gives a source-coupled restriction on the negative route, not a construction of the required all-cap zero and not a theorem excluding other weak-stage cones or distant body presentations.

## 2. Pinned inherited facts

Read first:
- [Full-shot nonordinary route audit](../../whole-source/continuation-2110z/FULL-SHOT-NONORDINARY-NEGATIVE-ROUTE-AUDIT.md), SHA256 b4246bdfa9dab782e2726736297db821b801884e9555abe9ab9e2129e2a71846.
- [Exact full-body elimination](../../../2026-10-08-codex-g3-g4-full-shot-1253z/g4-fixed-target/attempt-7/FIXED-TARGET-ALL-ORDER-BODY-ELIMINATION.md), SHA256 6764d83683319797c86cbb51a06f4176c4db5d3c93295053a9fddc72389a5db4. Its genuine five-coordinate cap-four Jacobian is nonzero, and its actual inverse has uniform local strict margins over \(q_U,q_V\in[7/8,1]\).
- [Balanced rare local-fibre theorem](../../../2026-10-08-codex-g3-g4-full-shot-1253z/g4-fixed-target/attempt-5/BALANCED-RARE-LOCAL-FIBRE-OBSTRUCTION.md), SHA256 655e354b85a207620f256c2865a7a53fe9e06cb7d9e63978250e1269b98e712d. Its theorem and coefficients are inherited, not rederived here.
- [Original source contract](../../../2026-10-01-g4-admitted-testers-0819z/PROOF.md), SHA256 661696b322c1ee2f57ffeb45ada556808f945d698ef0187c1a32ec0d881e40a1.

The new theorem uses a different cone from exact loss balance. Under loss balance with a finite rare arm, majority duration is comparable to the rare probability; here the rare probability is uniformly much smaller than that duration. The new proof uses the full cap-four operator norm for the body response and a large-arity bound, rather than transplanting the prior cap-five covector.

## 3. Uniform physical clock bounds

For a cell \(B(x,e^{-b},g)\),
\[
p_2=(1-g)^2e^{-b}+2g(1-g)+g^2x\le e^{-b}+2g.
\]
Each factor in a region has pair survival at least that region's product, hence p_2>=7/8. For eta<=1/16 the hypothesis gives g<=eta, so
\[
e^{-b}\ge3/4,\qquad 0<b\le B:=\log(4/3).
\]
It also gives g<=eta b. Since
\[
e^{-b/2}-e^{-b}\ge(b/2)e^{-B}=3b/8,
\]
we have \(p_2\le e^{-b}+2\eta b\le e^{-b/2}\). Thus each cell's actual pair hazard is at least b/2.

Define
\[
S=\sum_{\text{extra cells}}g b^2,\qquad
H_0=-\log(7/8).
\]
Pair hazards add in each actual region, and ordinary gaps have positive hazards. Therefore
\[
\sum b\le4H_0,\qquad
0<S\le4\eta B^2H_0
\]
when an extra cell occurs. This is uniform in word count. Only the pair-hazard budget is bounded; a rare arm may have any finite duration.

## 4. A full-kernel estimate that fixes the body displacement

Let
\[
A_4(g,b,x)=B(x,e^{-b},g)_4-E(p_2)_4.
\]
This is the difference of two genuine full cap-four kernels, sharing their exact pair survival. The comparison E(p_2) is used in the proof, not as a hidden observer or a randomized physical implementation.

Finite source probabilities and ordinary probabilities are polynomial in survival variables, hence analytic in g,b and continuous with uniformly bounded finite derivatives for \(x\in[0,1]\), \(b\in[0,B]\), \(g\in[0,1/16]\).

The actual routing semantics supplies three cancellations:
1. At g=0, every root takes the majority arm, so A_4=0 for every b.
2. The first g coefficient is independent of x: precisely one rare current root is isolated, while the others undergo ordinary majority-arm coalescence. As b->0,
   \[
   \partial_g B|_{g=0}=-2bQ+O(b^2).
   \]
   Each specified pair is excluded by exactly two of the possible isolated roots. The pair-matched ordinary derivative has the same -2bQ term. Thus
   \[
   \partial_g A_4|_{g=0}=O(b^2).
   \]
3. At b=0, the only order-g-squared event is a specified rare pair merging, with probability coefficient 1-x. Hence
   \[
   B(x,1,g)=I+(1-x)g^2Q+O(g^3).
   \]
   Its pair-matched ordinary kernel has exactly the same coefficient, so \(A_4(g,0,x)=O(g^3)\).

These are full current-root/graft coefficient identities, not only diagonal identities. By a Taylor expansion in g, with its second coefficient expanded at b=g=0, they imply the uniform finite-cap estimate
\[
\|A_4(g,b,x)\|
\le C_4[gb^2+g^2b+g^3].
\]
Here and below the norm can be maximum row total variation, with constant factors absorbed. Uniformity in the closed survival interval includes arbitrarily short or long rare arms; the realizing arms remain strict.

Under the cone condition,
\[
g^2b\le\eta gb^2,\qquad g^3\le\eta^2gb^2.
\]
Stochastic telescoping of the actual finite words, replacing each cell by its pair-matched ordinary kernel, therefore gives
\[
\|U_4-E(q_U)_4\|+\|V_4-E(q_V)_4\|\le C S.
\]
Every actual connector remains in this calculation. There is no chronological cancellation assumption or bound depending on the number of factors.

The genuine cap-four inverse and the compact ordinary baseline now give
\[
\|\Lambda(U_4,V_4)-\bar\theta(q_U,q_V)\|\le C_{\rm inv}S.
\]
This follows from its nonzero physical Jacobian and a uniform local inverse on the compact baseline family, not from a general parameter-identification assumption. For eta sufficiently small, the bound on S places every declared U,V in that inverse domain and keeps the returned body strict. All five body variables are spent by this inverse; every higher-order body correction is already included in this exact estimate.

## 5. The actual diagonal coefficient and its uniform remainder

For any kernel set
\[
\mathcal L_n(K)=\log b_n(K)-\lambda_n\log b_2(K),
\qquad \lambda_n=\binom n2.
\]
It adds exactly under source composition and vanishes on ordinary factors.

The bare no-merger formula is
\[
p_n=\sum_{j=0}^n\binom nj g^j(1-g)^{n-j}
       x^{\binom j2}e^{-b\binom{n-j}2}.
\]
Its first g derivative at g=0, after the exact pair normalization, is
\[
r_n(b)=n\left[e^{(n-1)b}-1-(n-1)(e^b-1)\right].
\]
For n>=3, the exponential series gives
\[
r_n(b)\ge\kappa_n b^2,\qquad
\kappa_n=\frac{n(n-1)(n-2)}2.
\]
All coefficients of order at least two in the bracket are nonnegative. The coefficient is independent of the rare-arm survival.

For each fixed n, positivity of the all-majority contribution bounds p_n away from zero on the above compact box. Thus its logarithm is analytic there with finite derivative bounds. At b=0,
\[
p_n=1-\lambda_n(1-x)g^2+O(g^3),
\]
so its pair-neutral logarithm has no g-squared term there. The same Taylor argument as in Section 4 yields
\[
\mathcal L_n(B)=g r_n(b)+R_n,\qquad
|R_n|\le C_n[g^2b+g^3].
\]
No uniform bound on C_n as n->infinity is assumed. For the single arity selected below, C_n is simply finite. Consequently
\[
\sum_{\rm extra}\mathcal L_n(B_i)
\ge[\kappa_n-C_n(\eta+\eta^2)]S.                      \tag{*}
\]

## 6. Why the retuned body cannot cancel this cone

For the retuned one-cell body, ordinary pads cancel exactly in \(\mathcal L_n\). Its arm survivals and inheritance parameter remain in one fixed compact strict box around (1/2,1/2,2/3).

The positive terms in the no-merger formula give
\[
|\partial_x\log p_n|\le\lambda_n/x,\qquad
|\partial_y\log p_n|\le\lambda_n/y,\qquad
|\partial_g\log p_n|\le n/\min(g,1-g).
\]
Applying the same bounds to p_2 proves
\[
\|\nabla_{x,y,g}\mathcal L_n(B)\|\le A n^2
\]
for every n, with A independent of n on that strict box. The apparent smallness of p_n at large arity causes no loss: each derivative is a weighted average of the displayed bounded log derivatives.

Combining this bound with the **actual cap-four-forced displacement** gives
\[
|\mathcal L_n(K(\Lambda))-\mathcal L_n(T)|
\le M n^2 S,
\]
with M independent of n and of the extra word count. No higher body coefficient is chosen separately.

Choose one finite N>=5 with
\[
\kappa_N>2MN^2.
\]
Then choose eta_*>0 small enough for all prior local-domain requirements and
\[
C_N(\eta_*+\eta_*^2)<\kappa_N/4.
\]
This order of choices is essential: C_N may grow rapidly with N. Exact diagonal multiplication, (*) and the body bound imply
\[
\mathcal L_N(W)-\mathcal L_N(T)
\ge[\kappa_N-MN^2-C_N(\eta+\eta^2)]S
>\frac{\kappa_N}{4}S>0.
\]
Therefore the complete body-eliminated equation cannot vanish through N.

Cap-four equality already fixes b_2(W)=b_2(T)=13/48. Thus the strict inequality also implies \(b_N(W)>b_N(T)\), not merely a difference after an arbitrary clock normalization. The actual total pair hazard equals the fixed target's pair hazard. In a fixed eligible exterior, the inherited full-kernel/topology observer supplies finite original labelled topology events detecting this difference; no hidden no-merger statistic is added to the menu.

## 7. New result and residual gap

The new result is a count-uniform, genuinely source-coupled local exclusion for an unbalanced endpoint-rare cone **after complete cap-four body elimination**. It is stronger than observing a positive bare-stage tangent: the full lower-forest displacement bound controls all five physical body corrections, and the conclusion is an exact finite-amplitude inequality on this declared cone.

It does not construct an all-cap rival and does not exclude arbitrary weak stages. The condition g/b small is substantive. When majority duration is comparable to g, the competing g^2b and g^3 terms are of the same order as gb^2 and their signs can matter. Fair/parabolic stages and the previously explored all-ratio rare constructions are not globally covered. A mixed collection containing such uncovered stages can also offset the positive cone; no sum is discarded merely because its members are weak.

Thus an all-cap solution of the fixed-target negative route cannot consist solely of the declared majority-duration-dominant rare stages on this body branch. Other relative scalings, mixtures of stage types, or a distant presentation remain possible. Neither signed saturation nor generic target interior was used to replace the missing actual common zero. General original INDEPENDENT-only G4 remains open.

Evidence: hand proof only. Constants and N are existential; no numerical source evaluation, new finite-cap ladder, QE, compiler, Git operation, or effective observation-only stopping rule is claimed.
