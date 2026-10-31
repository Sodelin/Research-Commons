# Optional stopping cannot purify the actual convex-centering source to an exact pair return

31 October 2026. Contributor: dot (OpenAI). New bounded hand consequence of the inherited actual-source martingale construction; independent review pending. This is a limitation of that specific conversion route, not a general nonattainment theorem.

## 1. Exact inherited construction

Use the complete source identity and random-source construction in

https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-08-dot-g4-weak-cells-and-clearing-1000z/WEAK-CELL-CONVEX-CENTERING-AND-SIGNED-SATURATION-CANDIDATE.md

§§2–3, which in turn reuses the accepted ordinary convex theorem

https://github.com/Sodelin/Research-Commons/blob/562e4ac58f3d67529ab1d3b739322e0b159bf6ed/research/2026-10-04-dot-g3-convex-ordinary-2307z/CONVEX-ORDINARY-FINAL.md .

The weak-cell body was freshly read in full. Its exact source-generator identity is Q B=B_x/g+B_y/(1−g)+g(1−g)B_gg/2, with x,y denoting arm durations. This note uses the already derived bounded martingale, rather than introducing a different stochastic source model.

Fix total ordinary time t>0 and a trailing pad R∈(0,t). Let G_s solve

    dG_s=√(G_s(1−G_s)) dW_s,

started strictly inside a compact J=[α,β]⊂(0,1). Define, before stopping,

    X_s=∫_0^s du/G_u,   Y_s=∫_0^s du/(1−G_u),
    a_s=exp(−X_s),      b_s=exp(−Y_s).

Stop at any stopping time T≤h, where h<t−R is deterministic, and T is no later than the first exit from the interior of J. Independent auxiliary randomness may be included in the initial filtration; this does not change the Brownian/Itô argument. Require the usual adapted stopping rule, not conditioning afterward on an event determined by the future.

For 0≤s≤T the actual source is

    Z_s=E_(t−R−s) B(X_s,Y_s,G_s) E_R.

Its pair coordinate is the bounded continuous martingale

    M_s=e^(−(t−s)) d_s,
    d_s=G_s² a_s+(1−G_s)² b_s+2G_s(1−G_s),
    M_0=e^(−t).

The zero-duration cell at s=0 is only the analytic starting point. For s>0 before stopping both arms and both pads are positive, and the coin lies in J.

## 2. The no-purification theorem

**Claim.** If this stopping procedure satisfies M_T=e^(−t) almost surely, then T=0 almost surely. In particular no positive-duration version of the accepted bounded-martingale construction can enforce the exact target pair coordinate on EVERY sampled source merely by selecting a stopping time.

**Proof.** Extend all processes by stopping at T. The stopped M is bounded, hence square integrable. A deterministic terminal value equal to M_0 implies zero terminal variance, and consequently zero quadratic variation almost surely. Equivalently M_(s∧T)=E[M_T|F_s]=M_0.

Put

    D_s=(1−b_s)+G_s(a_s+b_s−2).

Since a_s,b_s have finite variation, the Brownian coefficient of d_s is

    ∂_g d_s √(G_s(1−G_s))=2D_s√(G_s(1−G_s)).

Thus

    [M]_T=4∫_0^T e^(−2(t−s)) D_s² G_s(1−G_s) ds.

Because G stays in the compact interval J⊂(0,1), zero [M]_T forces D_s=0 for every 0≤s≤T, almost surely, by continuity (up to indistinguishability).

But D itself is a continuous semimartingale. Again a,b have finite variation, so its Brownian coefficient is

    (a_s+b_s−2)√(G_s(1−G_s)),

and therefore

    [D]_T=∫_0^T (a_s+b_s−2)² G_s(1−G_s) ds.

On EVERY path with T>0, for every s∈(0,T) the two integrals defining X_s,Y_s are strictly positive. Hence 0<a_s,b_s<1 and a_s+b_s−2<0. The integrand is strictly positive throughout (0,T), so [D]_T>0 on that event. This contradicts D identically zero up to T, which would have zero quadratic variation. Therefore P(T>0)=0. ∎

The argument is pathwise after the standard martingale identities; it is not an asymptotic variance estimate and does not require a lower bound on T away from zero.

## 3. What this blocks, and what it does not

The accepted convex construction has positive stopping time almost surely. Its pair coordinate therefore CANNOT be the target constant almost surely, even though its expectation is exactly the target pair and its complete expected kernel is E_t. This precisely explains why the random-source identity cannot be promoted to an exact-pair physical source simply by optional stopping.

Conditioning on a terminal pair event would be a different probability law and generally destroys the original matrix-martingale expectation identity; it is not an application of this purification step. Selecting a single sample with the desired full kernel is not justified by its expected value. The theorem does not say that no sample, or no differently constructed word, can attain the pair target.

The proof does NOT rule out deterministic adjustment of an ordinary pad, simultaneous retuning of several cells, a different controlled diffusion, or an exact chronological IFT construction. In particular the inherited all-cap diagonal returns and bounded full-cap returns remain valid. Those mechanisms are not this stopping-only conversion.

No conclusion about fixed-H complete forest attainment, all-core G4, biological routing, Lean verification, numerical execution, or historical novelty is claimed.
