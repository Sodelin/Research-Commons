# An exact finite-hybrid frontier for the original passive quartet

Contributor: Cloud G3 lane, 2026-10-08. **HAND CANDIDATE, review pending.** No numerical/symbolic control, optimizer, QE, enumeration or compiler has run. All references below concern the original source grammar and one original permitted observation.

## 1. Source, observation and inherited constants

Use the exact source and observation of the [accepted quartet theorem](../2026-10-08-cloud-g3-quartet-whole-fibre-0134z/PROPOSITION-AND-PROOF.md), Section 1: the original finite positive binary rooted-LSA, outer-labelled planar, cut-child class with natural INDEPENDENT inheritance; seven labelled samples on four taxa, four from A; observe only the rooted labelled restriction to those four A copies. Let `T = Pr(balanced)-1/3`. Let `H` be the TOTAL number of actual hybrid vertices of the original graph. No word bound or selected-state access is supplied as input.

The inherited [all-core reduction](../2026-10-06-dot-g3-original-quartet-whole-fibre-no-0454z/PROOF.md), Sections 1–2, preserves this marginal and reduces the selected ancestry to a serial two-arm chain. Each contributing cell contains one retained actual hybrid; distinct cells use distinct vertices. Thus its number `n` is at most H. The original positive leading pendant population, ordinary connectors, actual root/LSA, other taxa and original unbounded ordinary completion are retained. Deleted-lineage mergers are suppressed unary events under projectivity, not new routing draws for original tips.

For a closed independent cell, put `q=1-p`, `u=p(1-x)`, `v=q(1-y)`, where `p,x,y` range over `[0,1]`. The inherited polynomials are

    T = (2/3)[q u^3 + p v^3 - 3pq(u-v)^2],
    c = p^4 x^6 + q^4 y^6 + 4p^3q x^3 + 4pq^3 y^3 + 6p^2q^2 xy.

Here c is the four-root no-merger probability. Ordinary passages have `T=0` and `c=z^6`. For chronological factors the accepted cocycle is

    T(KL)=T(K)+c(K)T(L),       c(KL)=c(K)c(L).             (1)

The accepted 0134z proof defines the continuous discounted reward `R=T/(1-c)`, with zero on the identity locus, and its algebraic minimum m. It establishes

    -1/3 <= m < 0,       T >= m(1-c),       0 <= c <= 1,  (2)

throughout the closed cube, plus strict positive physical density and exact leading ordinary padding. It decides the passive observation image `m<t<1/12`. We reuse these facts rather than repeat its pole or recognition proof. Write `b=-m=|m|` and `a=13/256`.

## 2. The complete-cube one-cell minimum is -9/64

First suppose `u>=v`. Subtracting the cell polynomial at v=0 gives the exact identity

    T(u,v)-T(u,0) = (2/3)p v [v^2+3q(2u-v)] >= 0.       (3)

All factors are nonnegative, including at p=0 or q=0. Since `0<=u<=p`,

    T(u,0)-T(p,0) = (2/3)q(p-u)(2p^2+2pu-u^2) >= 0,      (4)
    T(p,0) = -(4/3)p^3q.

If `v>=u`, exchange p with q and u with v to obtain `T(u,v)>=-(4/3)q^3p`. These two regions cover the entire parameter cube, including equality and all corners. Finally,

    27/256-p^3(1-p)
       = (p-3/4)^2(p^2+p/2+3/16) >= 0.                 (5)

The same identity with q bounds `q^3p`. Consequently

    min_closed_cell T = -9/64.                         (6)

Equality is attained at the closed cell `p=3/4,x=0,y=1`, and at its arm swap. At this cell direct substitution gives

    c=13/256,       R=(-9/64)/(243/256)=-4/27.

Thus (2) sharpens to

    4/27 <= b <= 1/3,       m <= -4/27 < -9/64.          (7)

The minimizing cell for R has `c*<1` by the accepted nonidentity argument. It also has `c*>0`: if c=0 then R=T, while (6) and (7) give `R>=-9/64>m`. This does NOT assert that every c=0 cell has nonnegative contrast. It proves only that a discounted minimizer cannot have c=0.

## 3. Uniform actual hybrid-count lower bound

For a closed cell set

    e = T-m(1-c) = T+b(1-c) >= 0.

For any tail, put `Gtail=Ttail-m=Ttail+b`. Equation (1) yields the exact residual recursion

    Gnew = e+c Gtail.                                  (8)

Equation (6), followed by (7), gives

    e+cb = T+b >= b-9/64 >= (13/256)b = ab.              (9)

We now prove that every finite chain with n independent hybrid cells and ANY finite number of ordinary passages satisfies

    T(chain)-m >= b a^n.                               (10)

Start at the empty tail: `T=0`, so `G=b`. Suppose a tail with k hybrid cells has `Gtail>=b a^k`. Prepending one independent cell gives, since c and e are nonnegative and `a^k<=1`,

    Gnew >= e+cb a^k
         >= a^k(e+cb)
         >= b a^(k+1).

This proof does not assume `Gtail<=b`; tails with positive contrast are included. For an ordinary passage, `e=b(1-c)`, so

    Gnew >= b[(1-c)+c a^k] >= b a^k.

An ordinary population therefore does not consume the hybrid count budget. Its duration may be arbitrarily large; even closed survival c=0 causes no problem. The final unbounded ordinary completion is the defining readout in T, not an extra finite factor assigned c=0. Zero hybrids give exactly the ordinary Kingman law T=0 and (10) with n=0.

Apply the actual all-core reduction from Section 1. Since `n<=H` and `0<a<1`, every original admitted source satisfies

    T(source)-m >= b a^n >= b a^H
                 >= (4/27)(13/256)^H.                  (11)

This counts actual original hybrid vertices, including vertices that do not contribute to the selected ancestry. A larger alternative core cannot evade (11). The argument does not impose a lower bound on inheritance weights or physical lengths, assume a level-1 full graph, observe a kernel, or condition the observation on a routing event.

If a negative target has `epsilon=t-m>0`, every realizing source therefore obeys

    H >= log(b/epsilon)/log(256/13).                    (12)

Near m the right side is positive. A division-free exact form is (11); integer exclusions can be decided by algebraic powers without a logarithm oracle. The constant b is effectively algebraic, as inherited, but neither b nor an optimal source has been computed here.

## 4. Exact finite-count frontier

Define a sequence by a compact one-cell optimization:

    F_0=0,
    F_(n+1)=min_(p,x,y in [0,1]) [T(p,x,y)+c(p,x,y) F_n]. (13)

Each F_n is effectively real-algebraic. Given an algebraic representation of F_n, an exact RCF universal lower-bound/existential equality formula on the closed cube uniquely defines F_(n+1), and algebraic sampling supplies a minimizing cell. This is a classical algorithm specification, not an executed QE computation. No unbounded-word image is assumed semialgebraic.

By (1), F_n is the minimum contrast of a closed word of n independent cells. This is proved recursively: c>=0 lets one choose a minimizing suffix of n-1 cells after each proposed first cell. Finite products have polynomial continuous readout, so the compact minimizers exist.

The identity cell shows `F_(n+1)<=F_n<=0`. Ordinary passages cannot lower the minimum for the permitted count: if a tail is at least F_n, then its ordinary-passage contrast is at least `c F_n>=F_n`. Induction through the actual selected chain therefore gives `T>=F_n` for every chain with at most n cells and arbitrary ordinary populations. The mandatory strictly positive leading A population makes this strict for every actual negative contrast: a negative tail is multiplied by a survival in `(0,1)`, increasing its contrast; a nonnegative tail remains nonnegative. Thus, for n>=1,

    actual source with H<=n and negative t ==> F_n<t.    (14)

The closed minimizing words are limits of actual n-cell positive chains, with rational interior survivals/routing weights and positive leading/connecting populations. For any algebraic `F_n<t<0`, this density supplies a strict rational-coordinate n-cell chain W with `T(W)<t<0`. A terminating fixed-length rational search finds one. Prepending the actual positive ordinary survival `(t/T(W))^(1/6)` realizes t exactly, keeping n hybrids and the original graph admission. Adjacent leading ordinary edges may be merged. All fifteen observed coordinates follow simultaneously from natural label exchangeability. The survivals are effective algebraic; physical durations are their positive finite computable negative logarithms, not necessarily algebraic.

Consequently the exact minimum TOTAL hybrid count over all admitted original sources realizing a negative algebraic target is

    Hmin(t)=least n>=1 such that F_n<t.                 (15)

This is a whole-source-fibre minimum, not a minimum over a supplied chain only: (14) excludes every alternative core of smaller total count, and the positive chain witnesses attain the upper count. At t=0 the minimum is 0. For `0<t<1/12` it is 1, using the already accepted strict one-cell upper approximants plus exact positive leading padding; a zero-hybrid source has t=0.

## 5. Matching logarithmic growth and algebraic YES families

Choose an algebraic minimizing cell for R, with `0<c*<1` as established in Section 2. Its e=0. Define `delta_n=F_n-m=F_n+b`. Equations (10) and (13) give

    b a^n <= delta_n <= b (c*)^n.                      (16)

The upper bound follows by evaluating (13) at that same minimizing cell at every stage; the lower bound is the already proved arbitrary closed-chain bound. Moreover `delta_n>0`, and evaluating the next stage at this cell gives `F_(n+1)<F_n`. Thus F_n decreases to m. This is new finite-count information, not a repeat of the accepted arbitrary-length membership interval.

For every sufficiently small `epsilon=t-m>0`, (15) and (16) give matching count order

    Hmin(t) = Theta(log(1/epsilon)) as t decreases to m. (17)

The lower estimate is (12). For an explicit upper integer prescription, choose the first n>=1 with `b(c*)^n<epsilon`. Then `F_n<t` and (15) supplies an exact positive witness with n hybrids. This test uses algebraic powers and strict comparisons and terminates. Strict rational physical approximation and the exact ordinary padding are already included in Section 4; the upper bound does not call the closed minimizing word an admitted positive source.

For example, the effective algebraic contrasts `t_k=m+b/2^k` for k>=1 are negative and belong to the original passive source image. Their full fifteen-coordinate algebraic laws are exact YES inputs, and (11) forces

    Hmin(t_k) >= k log(2)/log(256/13).

Their count also grows at most linearly in k by (16). These laws use the SAME fixed seven-sample panel and fifteen-outcome observation for all k. No actual QE, sequence generation or source search was run.

## 6. What this settles for original G3

There is no finite hybrid cap depending only on this fixed observation panel that preserves every original YES fibre. This rules out a general-recognition shortcut that searches a panel-dependent bounded source catalogue and rejects after exhausting it. The exact membership theorem and the input-dependent minimum count (15) are compatible: decidability need not provide an input-independent size bound.

This is an INDEPENDENT, original passive-observation, all-core size theorem. It is distinct from the earlier COMMON retained-factor/Poisson count results, and it does not turn their natural-slot statements into INDEPENDENT exclusions. General G3 still needs a complete finite-positive witness or terminal NO method for arbitrary coupled algebraic observation inputs, retaining shared controls/banks/ties/IDs and both modes. No impossibility of every input-dependent bound, undecidability, complete general certificate language, G4 factorization, source uniqueness, marked-clock/bin/physical-past transfer or full G6 closure is claimed.

Methods and credit: Dot's original ancestry/projectivity reduction, cell polynomials and cocycle; Astra's admitted positive bridge grammar; the accepted 0134z signed endpoint/density/extraction theorem; elementary nonnegative polynomial identities and discounted recurrences; classical compact real-algebraic optimization and rational density. Historical novelty is unresolved. All new conclusions in this packet are hand candidates until their own exact review.
