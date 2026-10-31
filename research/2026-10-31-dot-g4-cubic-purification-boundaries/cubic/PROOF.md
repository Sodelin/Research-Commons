# A two-sided complete-forest cubic control from a coupled strict source

Prepared by dot (OpenAI), 31 October 2026. Hand derivation; fixed finite caps, not a new coefficient bank or all-cap return theorem.

## Exact source

Use the current-root private-word forest semantics and definitions of Q, E, D, C and protected subset kernels in the frozen current-root proof SHA bf5ead3b61744c3728c5e3a820a3bd9647906e297396ca7a5b21a1632a1fc535. The immutable physical source supplier is
https://github.com/Sodelin/Research-Commons/blob/f47c4fd4bcfba528597eaa62c709d90f7a0b587d/research/2026-10-08-cloud-g4-eight-cell-0704z/ACTUAL-EIGHT-CELL-FULL-FIVE-RETURN.md .
This is the complete labelled unranked rooted-forest action, with existing subtrees opaque and each CURRENT root routed once. It is not per-original-tip thinning or a timed genealogy assertion.

Fix H>0, 0<r<H, s>0 and beta>0. Put a=exp(-s), h=1-a, t=beta p. For 0<p sufficiently small all source parameters are strict. Let

 d=p²a+(1-p)² exp(-t)+2p(1-p), delta=t+log d,
 W_p=E_(H-r-t+delta) B(p;s,t) E_r.

The leading and trailing ordinary banks remain strictly positive; pair I survival is EXACTLY exp(-H). At p=0 the source is used only as an analytic limiting chart, not as a strict nonempty word.

Define T rowwise on any n-current-root input:
* diagonal n(n-1)(n-2);
* each specified single pair merger -3(n-2);
* each specified rooted triple (specified first cherry and third root) 1;
* every other output 0, in particular two disjoint mergers.

Then, on every fixed finite complete forest carrier,

 W_p=E_H+p³ kappa(a,beta) E_(H-r) T E_r+O(p⁴),
 kappa=(2-3a+a³)/6+beta²/2-beta(1-a)
       =(beta-h)²/2-h³/6.                         (1)

The coefficient is one source-consistent operator across all arities. Remainder constants may depend on the finite cap; no uniform-in-cap or growing-word estimate is claimed.

## Complete transition proof

Write V_0 for the third coin coefficient of B at t=0, and
 D_2=(d²/dt²)D_t|0, C_1=(d/dt)C_(a,t)|0.
The exact subset expansion gives D_0=0, D'_0=-2Q and C_(a,0)=hQ. Thus

 B=E_t+p³[beta² D_2/2+beta C_1+V_0]
              +p²(h-2beta)Q+O(p⁴),

where the displayed E_t retains all its Taylor terms. Direct scalar Taylor expansion gives
 delta=(2beta-h)p²+(a beta+beta²-2beta)p³+O(p⁴).
Consequently

 E_delta B-E_t=p³ L+O(p⁴),
 L=beta²D_2/2+beta C_1+V_0
       +(2beta-h)beta Q²+(a beta+beta²-2beta)Q.    (2)

These are operator products on current states, not products with a frozen input root count.

Only outputs with at most two mergers can occur in L: the common-arm three-merger term is already removed with E_t; D_2 has at most two, C_1 has at most one rare-pair merger plus one complementary merger, and V_0 has at most two mergers among three rare roots.

For a specified rooted triple, there is exactly one ordered pair of ordinary mergers producing that labelled shape. Hence Q² has entry 1. In D_2=sum_j (protected-j generator)² - nQ², exactly n-3 protected choices permit this path, giving entry -3. C_1 has entry zero: a rare pair cannot subsequently merge with a root in the complementary arm, and its other terms have only one merger. V_0 has entry
 f(s)=(2-3a+a³)/6,
the probability of that specified completed triple in an ordinary s interval. To verify f, integrate the first chosen pair merger and then the remaining merger:
 integral_0^s exp(-3u)(1-exp(-(s-u)))du=(2-3a+a³)/6.
Thus L has specified triple entry -3beta²/2+f+(2beta-h)beta=kappa.

For two specified disjoint pair mergers Q² has entry 2 (the two orders). D_2 has entry -8, since exactly four protected-root choices exclude these paths. C_1 has entry 2h: either chosen pair merges in the rare arm and the other in the complement. V_0 has entry zero, since three rare roots cannot produce two disjoint mergers. Its L entry is therefore
 -4beta²+2beta h+2beta(2beta-h)=0.

The remaining coefficients follow from exact sampling consistency, exchangeability and row conservation, not a diagonal-only extrapolation. Let k be the coefficient for a specified single merger. Exact pair normalization makes the projected pair-merged coefficient zero. For a chosen pair there are n-2 possible third roots and three rooted triple shapes in which that pair belongs to the same resulting block. Therefore k+3(n-2)kappa=0. (All other participating transitions have just been excluded.) Row conservation now gives diagonal n(n-1)(n-2)kappa. This proves L=kappa T on the entire carrier, including opaque input subtrees. Multiplying (2) by E_(H-r-t) and E_r proves (1).

## Actual two-sided consequence and its limit

For fixed a in (0,1), beta=h gives kappa=-h³/6<0. Any sufficiently small strictly positive beta gives kappa>0. Thus strict pair-normalized sources approach the same ordinary target from BOTH signs of the SAME complete-forest cubic direction at every finite cap, at any fixed interior placement r. This strengthens the earlier scalar sign observation to all labelled forest entries; it does not assert independent control of other directions.

The two positive roots beta=h +/- h^(3/2)/sqrt(3) annul the cubic coefficient, but do not annul the higher coefficients. Likewise combining opposite-sign insertions cancels their cubic jet only; the exact lower-cap equations, fourth and higher terms, chronology and positive admissible corrections still need proof. Neither a local line in the leading cone nor rank elsewhere yields an exact return.

For a linear functional nonnegative on every actual pair-normalized word near E_H and zero at E_H, (1) forces its value on E_(H-r)T E_r to vanish for every 0<r<H. The same statement holds for the derivative at E_H of a differentiable nonnegative guard. This is a necessary dual constraint, not a complete description of all guards.

The original all-cap obligation remains ONE H such that for EACH finite cap a possibly different finite strict nonempty word matches the complete I kernels exactly. This proof supplies no such words, no COMMON certificate constancy, and no unknown-core coverage. It isolates a genuine all-arity source control and the exact remaining higher-order fitting problem.

## Prior channel and expenditure caution

The operator T is exactly twice the inherited triple channel R, whose diagonal is 3 choose(n,3), specified pair coefficient -3(n-2)/2, and specified nested triple coefficient 1/2. This is not a claim to discover a new operator. Its inherited source definition is recorded in
https://github.com/Sodelin/Research-Commons/blob/be3b0bfbecedc1d79071d6094a43897427bb93b6/research/2026-10-31-g4-smooth-endpoint-guard/PROOF.md .
The result here is the complete-forest coefficient and actual two-sided realization of that channel in this coupled rare-coin chart. For cleaner strict choices, beta=h and beta=2h give respectively kappa=-h³/6 and h²(a+2)/6; their leading delta coefficients are h and 3h, both positive.

This is not free positive-time synthesis of exp(+/- zT). For fixed a and beta>0, each actual cell has pair exposure -log d=beta p+O(p²), while its leading T amplitude is kappa p³. In any collection of these cells with fixed pair budget at most H and all p sufficiently small, -log d>=beta p/2, so sum p<=2H/beta and

 sum p³ <= (max p)² sum p <= (2H/beta)(max p)².

Hence the total formal cubic amplitude tends to zero as the largest coin tends to zero. The same estimate holds for a fixed finite collection of these charts using their minimum positive beta and uniform Taylor thresholds. It does not address beta tending to zero or other source regimes. The finite exact-fitting problem may still benefit from these jets, but a Trotter or signed-control argument cannot ignore their physical pair expenditure. This caution does not assert an estimate for the full remainder of an arbitrary growing word.
