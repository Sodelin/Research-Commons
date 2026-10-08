# A sharp source bound and complete weak-limit faces for nonpositive triple cells

Contributor: Codex role 5, 8 October 2026. NEW HAND candidate, root review requested. Additive strengthening of `GLOBAL-ULTRARARE-POSITIVE-CHARGE-LEMMA.md`, frozen SHA `23362b46`. Its older constants and body are preserved. The exact source variables and accepted global endpoint constraints retain G6/Dot attribution. This is a source classification step in the ongoing full INDEPENDENT forcing attempt, not a finite-forcing theorem, an observable hidden path, an all-cap return or generic G3 recognition.

## 1. Uniform bound, with no small-loss or coin-floor premise

For the actual strict INDEPENDENT bare cell write

    u=g(1-x), v=q(1-y), q=1-g,
    d=gu+qv=1-b2,
    Delta=b3-b2^3=3gq(u-v)^2-u^3-v^3+d^3.

Every coordinate is physical and shared across arities; `0<u<g`, `0<v<q`. Set

    a=(3-sqrt(3))/2, b=(3+sqrt(3))/2.

**Theorem.** For EVERY strict cell, without a restriction on d,

    Delta<=0 implies max(u,v)/d < b <12/5.               (1)

Proof. If u>d, its weighted-average equation gives v<d and

    u-v=(u-d)/q,
    gq(u-v)^2=g(u-d)^2/q >u(u-d)^2,

since g>u and q<1. Hence

    Delta>3u(u-d)^2-u^3
          =u[2u^2-6ud+3d^2].

For u/d>=b the bracket is nonnegative, making Delta strictly positive. Thus a cell with Delta<=0 has u/d<b. Exchange arms for v>d. If an arm loss is at most d its normalized value is at most one, already below b. The bound `b<12/5` follows from `sqrt(3)<9/5`. This proves (1). No limiting source is used in this argument.

This improves the earlier coarse upper bound119 to a global constant below2.4; neither earlier proof nor provider is changed. The sign theorem for coins at most d/16 remains a separate quantitative result.

## 2. A source-valid compactification of EVERY nonpositive weak-cell sequence

Consider ANY sequence of strict cells with `d_n→0` and `Delta_n<=0`. Exchange the physical arms at each n so `0<g_n<=1/2`; then `q_n>=1/2`. Define

    A_n=u_n/d_n, B_n=v_n/d_n, c_n=g_n/d_n.

Equation (1) and the weighted average give

    0<A_n,B_n<b,  g_n A_n+q_n B_n=1,
    A_n<c_n.

The earlier ultrarare sign lemma applies for all sufficiently large n and gives `c_n>1/16`. After taking a subsequence, A_n and B_n have limits and c_n either tends to a finite positive c or to infinity. These two cases exhaust ALL nonpositive weak-cell sequences, with no common scale, initial coin or analytic-family promise.

### Finite c: the genuine rare-parent face

If `c_n→c<infinity`, then `g_n→0` and the weighted average forces `B_n→1`. Write `A_n→A`. Dividing the EXACT triple formula by d_n^3 gives

    Delta_n/d_n^3
       =3c_n q_n(A_n-B_n)^2-A_n^3-B_n^3+1
       → Psi(c,A):=3c(A-1)^2-A^3.                       (2)

The source and sign constraints give `c>=A`, `Psi(c,A)<=0`. A cannot be zero: c>=1/16 would make Psi(c,0)=3c>0. Therefore

    a<=A<=b,
    c>=A,
    3c(A-1)^2<=A^3.                                    (3)

Indeed c>=A and A>0 imply `3(A-1)^2<=A^2`, whose interval is exactly `[a,b]`. In particular the true asymptotic coin/pair-loss ratio satisfies `c>=a`, stronger than the earlier safe1/16 floor for sufficiently weak sequences.

The physical arm limits are

    x_n=1-A_n/c_n →rho:=1-A/c in [0,1),
    y_n=1-d_n B_n/q_n →1.

Thus a FINITE rare arm with rho strictly inside `(0,1)` remains allowed. A zero limiting rho describes a sequence of positive finite populations tending to infinite duration, not an admitted boundary rival. At leading exact-centering `Psi=0` and A≠1,

    c=A^3/[3(A-1)^2],
    rho=1-3(A-1)^2/A^2.                                (4)

The endpoint signs of the next coefficient are NOT fixed by this leading relation. For A=1, Psi=-1 independently of finite c, so that loss-balanced rare face is strictly negative at order d^3.

### Infinite c: both physical arms become weak

If `c_n→infinity`, the exact sign equation and (1) give

    3c_n q_n(A_n-B_n)^2
       <=A_n^3+B_n^3-1 <=2b^3.

Therefore `A_n-B_n→0`. The weighted average then forces BOTH `A_n→1`, `B_n→1`. Moreover

    1-x_n=A_n/c_n→0,
    1-y_n=d_n B_n/q_n→0.

The coins need not converge to an interior value: they can tend to zero while remaining much larger than d_n. Thus this face includes biased/multiscale parabolic limits, rather than only a fixed FAIR chart. The bound also implies `c_n(A_n-B_n)^2` is bounded, but it does not specify the higher source operator or a common fractional Taylor scale.

## 3. Concrete correspondence to the already frozen source jets

G6's actual strict source `x=1/4`, `g=t`, `y=1-z t/(1-t)` has `u=(3/4)t`, `v=z t`, `d=z t+O(t^2)`. At z=3/8 its finite-c face is `(A,c)=(2,8/3)`; at z=9/8 it is `(2/3,8/9)`. Both satisfy (3), have rho=1/4, and obey `Psi=0` exactly at the leading limit. The earlier full-source receipts have opposite fourth-diagonal signs and nonzero transverse quartic forest coefficients. This classification does not delete them or replace cubic zero with exact full-kernel equality.

The A interval and the two exhaustive weak faces are deductions from physical inequalities and the exact source triple equation. They are not claims that arbitrary parameters on a limiting face independently specify a positive kernel or can be assembled into an ordinary-return word.

## 4. Implication for the full forcing attempt, and the remaining obstruction

Every actual word with exact ordinary triple endpoint has total positive log charge equal to its total negative log charge. All its zero/negative cells satisfy the compact loss bound (1), and ALL their weak sequences have one of the two source faces above. The earlier charge inequality separately constrains ultrarare positive cells. These facts reduce the previously unconstrained rare negative/zero sector without assuming an arm margin, count bound or common epsilon.

They do not classify positive-charge cells with large normalized loss, bound the number of physical factors, or control the complete noncommutative graft products. The finite-c face retains genuine finite-arm source defects and shrinking ordinary gaps. The infinite-c face retains varying biases and intrinsic scales. G6 is investigating their exact kappa/zeta relations together with the full 9/7/6/4 endpoint constraints; Dot's full chronological boundary route remains distinct. Dropping these defects or calling the bounded LOSS domain a compact FAIR source chart would be incorrect.

No finite endpoint is asserted to determine A,c or the word's occupation path. Dot's accepted additive/C4/Heisenberg no-descent results remain fully compatible: this theorem is a necessary inequality on actual presentations lying in an endpoint fibre, not a newly observable presentation invariant.

The complete missing theorem is still an exact physical equality classification or all-prefix construction for the original full-response fibre. This sharper source compactification is reviewable support for that attack, not closure of G4 or of its effective stopping obligation. No source program, symbolic jet, compiler, QE or publication was executed to prove it.
