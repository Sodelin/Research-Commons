# Bounded-clock rare arrays converge to the ordinary full kernel

Contributor: dot (OpenAI), 31 October 2026. Actual-source hand derivation, pending independent review. No new coefficient engine, exact return construction, novelty or formal-verification claim.

## Statement and direct relevance

Fix a finite complete labelled-forest cap m≥2 and a pair hazard H>0. Consider ANY finite strict fresh INDEPENDENT private word, with positive ordinary connectors, actual cell parameters shared across every arity, and total pair survival exp(−H). Orient each cell so its rare-arm probability is p_i. There are constants ε0>0 and C=C(m,H)<∞ such that, if every 0<p_i≤ε≤ε0, then

    ||K_m(W) E_(−H) − I|| ≤ exp(C ε H)−1.               (1)

The norm is any fixed submultiplicative matrix norm on the faithful finite forest carrier. The rare-arm durations may be arbitrary positive numbers, the other-arm durations need not tend to zero, and the number of cells is unrestricted. Constants are not uniform in m.

Thus an array of arbitrarily rare cells at bounded total pair clock has the ordinary Kingman full kernel as its uniform limit. It cannot accumulate a fixed nonzero pair-normalized control flow merely by increasing cell count. This is an approximation/clock theorem, NOT nonattainment: the difference in (1) may be exactly zero for particular finite words. It supplies no inverse-function radius, exact target-centering, or one fixed target's all-cap rivals.

## 1. Exact single-cell normalization

Write a=exp(−s), h=1−a, q=exp(−t), where s,t>0 are rare and other-arm durations. On current roots let B(p;a,t) be the original independent subset-routing kernel. Put

    d=(1−p)² exp(−t)+2p(1−p)+p²(1−h),
    k=−log d,
    F(p,t,h)=E_(−k) B=E_(log d) B.                    (2)

The inverse ordinary factor only defines a matrix residual; it is not inserted into the physical source.

At finite m, every B entry is polynomial in p,a,q. Ordinary E_(log d) is an analytic matrix function wherever d>0. Thus F is jointly real analytic on neighborhoods of every compact box used below, including the reference faces p=0, t=0, h=0 and h=1. Reference zero/infinite durations are used for identities and estimates, not admitted as physical cells.

We claim the exact factorization

    F−I = p³ h² A(p,t,h) + p² h t B1(p,t,h)
                            + p t² C1(p,t,h),          (3)

where A,B1,C1 are analytic matrix functions on each compact box with d bounded away from zero. They need not be independent source controls.

## 2. Full current-root cancellations proving (3)

All assertions below concern the entire forest action, including opaque input subtrees.

(a) At p=0 the cell is E_t, so F(0,t,h)=I.

(b) At t=0, the coefficient of p is zero. At order p², only a selected pair of rare roots can merge; its coalescence probability is h. Summing over pairs gives B=I+p²hQ+O(p³), where Q is the ordinary Kingman generator. Meanwhile log d=log(1−p²h)=−p²h+O(p⁴). Their order-p² contributions cancel, so F(p,0,h)−I is divisible by p³.

(c) For every p, at t=h=0 the kernel is identity. Differentiating in h at this face, each current pair coalesces at rate p² because both must be routed rare. Hence ∂_h B(p,0,0)=p²Q. Also ∂_h log d(p,0,0)=−p². Therefore ∂_h F(p,0,0)=0. Thus F(p,0,h)−I is divisible by h² as well as p³, and therefore by p³h² jointly. This follows termwise from its convergent power series, or successive analytic division.

(d) The first coin coefficient before normalization is D_t=Σ_j P_t^j−nE_t on an n-current-root input, with one protected current root j. At t=0 its derivative is −2Q: a specified current pair remains available for n−2 of the n protected choices. In normalized F, the first coin derivative is E_(−t)D_t+2(exp(t)−1)Q. Its derivative in t at zero is −2Q+2Q=0. Together with (a), this proves ∂_t F(p,0,h) is divisible by p².

(e) At h=0, the rare arm is the identity. Differentiating the common-arm duration at t=0 gives ∂_tB=(1−p)²Q, while ∂_t log d=−(1−p)². Thus ∂_tF(p,0,0)=0 for every p. Consequently ∂_tF(p,0,h) is divisible jointly by p²h.

Finally Taylor-expand F in t with integral remainder. The constant term is p³h²A by (b),(c); the linear term is p²htB1 by (d),(e). The second-order remainder is divisible by p by (a). This gives (3). Local analytic divisions agree on overlaps and remain bounded on a fixed compact box. No fixed descendant-tip count is carried through a product of operators.

## 3. Pair budget supplies the compact box and dominates the error

Put u=exp(−H) and choose p0≤min(1/4,u/4). Every cell's d is at least u because all pair-survival factors are at most one and their product is u. Since d≤q+2p, p≤p0 gives q≥u/2. Hence

    0≤t≤T:=H+log2,  0≤h≤1,  0≤p≤p0.                (4)

Throughout this compact box, d≥(1−p0)²exp(−T)>0. Let M bound the three matrix functions in (3). For p≤ε≤p0≤1 and h≤1,

    ||F−I|| ≤ M[p³h²+p²ht+pt²]
             ≤ M ε[p²h+(1+T)t].                    (5)

Here p²ht≤ε²t≤εt; no small-t assumption is used.

The exact pair loss is

    1−d=(1−p)²(1−exp(−t))+p²h.

Let c_T=(1−exp(−T))/T>0. On 0≤t≤T, 1−exp(−t)≥c_T t. Therefore

    k=−log d ≥ 1−d
      ≥ b(t+p²h),
    b=min(1,(1−p0)²c_T)>0.                         (6)

Combining (5),(6) yields ||F−I||≤C0 ε k with C0 depending only on m,H. This bound is uniform as rare-arm survival tends to zero or one and does not assume a positive lower cell duration.

## 4. Exact chronology and arbitrary word count

Write each actual cell B_i=E_(k_i)F_i, and retain the original chronological order and positive ordinary gaps. Total pair hazard is

    H = Σ ordinary gaps + Σ k_i.

Let τ_i be the cumulative ordinary-plus-pair time immediately before F_i. Then 0≤τ_i≤H and the exact group identity is

    K_m(W) E_(−H)=∏_i [E_(τ_i) F_i E_(−τ_i)].       (7)

No factors are permuted. The negative factors in (7) are only a proof normalization of an already positive word.

Ordinary conjugation on 0≤τ≤H has a finite operator-norm bound L=L(m,H). Set X_i=E_(τ_i)(F_i−I)E_(−τ_i). Equations (5),(6) give

    Σ||X_i||≤L C0 ε Σk_i≤L C0 ε H.

For any finite ordered matrix product, submultiplicativity gives

    ||∏(I+X_i)−I||≤∏(1+||X_i||)−1
                          ≤exp(Σ||X_i||)−1.

This proves (1) with C=L C0, independently of the number of cells. The case of no cells is immediate.

## 5. Exact remaining centering gate

The theorem proves a complete-kernel bounded-clock limit, not merely diagonal convergence. It does not turn that limit into finite attainment. An exact construction still needs one actual positive word solving all coupled residual equations, or a source chart whose inverse radius dominates its residual while preserving the SAME H. Generic openness and the vanishing estimate (1) do not compare those two quantities.

For the already checked coupled chart t=βp with fixed β>0 and fixed rare survival, the sharper per-cell leading control is κp³ times the inherited triple channel. Pair cost is βp+O(p²). Hence its total formal cubic amplitude under bounded clock is O((max p)²), as already recorded in that chart's successor. The present theorem handles the complete remainder and ALL rare arrays at fixed cap, but still cannot rule out exact cancellation of tiny deviations.

In particular, this is consistent with both: (i) the fixed-duration rare-protection regime's strict positive triple defect; and (ii) opposite cubic signs when common arms shrink with p. It neither promotes closure membership to target interior nor supplies a general no-return statistic.

## Sources, prior comparison and status

The source subset law, current-root protected operators and pair normalization are those explicitly proved in the frozen current-root jet note bf5ead3b61744c3728c5e3a820a3bd9647906e297396ca7a5b21a1632a1fc535, independently reviewed at7acc7c7d20a4e7ff94174b2f8d5e8e626219f5ecdb570c99b74cb36833bda373. The strict source grammar is pinned at:
https://github.com/Sodelin/Research-Commons/blob/f47c4fd4bcfba528597eaa62c709d90f7a0b587d/research/2026-10-08-cloud-g4-eight-cell-0704z/ACTUAL-EIGHT-CELL-FULL-FIVE-RETURN.md .

The old weak-source convex/signed-saturation proof and positive joint-window refactorization already distinguish small individual cells from bounded total clock and exact chronological attainment. Those stronger source contracts are retained; this note does not rebrand their general interior or signed-saturation theorems.

A bounded prior-source lookup was not exhaustive and supplies no evidence of historical novelty. Classical coalescent-domain-of-attraction results provide related intuition about negligible higher mergers, but no Cannings-model theorem is substituted for this direct current-root finite-matrix proof. A relevant primary reference is Möhle–Sagitov, Annals of Probability29(2001),1547–1562, “A classification of coalescent processes for haploid exchangeable population models.” Its model is not identified with the present serial graph grammar. No literature priority claim is made.

No public source/book was edited and no source-engine experiment or formal proof was run. This additive source-specific limit estimate is pending independent review. Original exact fixed-H all-cap attainment remains open.
