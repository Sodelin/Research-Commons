# The actual cap8 normal gives a global leading action bound

Stable key: G3-GLOBAL-NORMAL-ACTION-TERRA-20261031-01.
Contributor: Codex Terra, 31 October 2026. **Hand-derived conditional
full-fibre result; independent review and formal verification pending.**
It reuses the pinned actual cap8 normal and the independently reviewed
full-fibre bias/charge estimates. The polynomial factor checks and their
limits are recorded below. It does NOT establish AG-Pair, a phase rate,
an all-input recognizer, or original G3 closure.

## Statement

Use the original paired equal-arm same-tuple finite strict complete-cap12
fibre, unchanged reference S(t), all real chronological source weights,
and one sufficiently small allowed `H=(log 2)/m>0` fixed before `h -> 0`.
Arbitrary strict/rare coins, microscopic cells, relative scales, positive
gaps and finite source counts remain allowed. Define

    h=-log t,  x=t/(2-t),  e=1-x,  u_i=-log q_i,
    d_i=1-q_i,  X_i=d_i/e,  beta_i=(2g_i-1)^2,
    y_i=beta_i*u_i/h^2,  ell_i=log(b2(B_i)/q_i),
    L=H/4,  <v>_ell=(1/L)sum_i ell_i*v_i,
    F(X)=X^2*(1+X)*(X-1)^2.

Then, on every such physical full-fibre word,

    <F(X)>_ell <= C_H*h^(1/3),                            (1)
    <(X^2-1)^2>_ell <= C_H*h^(1/6),                       (2)
    Action_h=sum_i Phi_h(C_i) <= C_H*h^(25/6).             (3)

The constants do not depend on the actual count, source scales, coins or
placement; `C_H` may depend on the one fixed H. Empty fibres make the
universal word statements vacuous. This forces the gap-weighted physical
scale to concentrate at the reference and excludes zero-charge fair dust
at leading order. It does not force every cell into a relative window,
prove a witness-size bound, or supply the `O(h^(6+delta))` calibrated
action rate required by the existing sufficient phase route.

## 1. The exact physical normal and its global beta structure

The already-held cap8 normal gives EXACTLY

    sum_i W4_i*f4(q_i,beta_i;x)=0,                         (4)

where W4 is the product of all actual b8 factors before the cell and b4
factors after it, including ordinary factors. The original normal
annihilates all mixed 8-to-6-to-4 paths; it is not replaced by a scalar
source equation on a whole word. The COMMON budget gives
`exp(-28H)<=W4_i<=1`. Set `C4=275625/176>0` and define

    G_i=f4(q_i,beta_i;x)/(C4*e^5*ell_i).                   (5)

The source is the EXACT polynomial in the hash-pinned
`fullcap-normal/NORMAL-POLYNOMIAL.json`, not only its compact-scale
limit. Its certified factor is `(1-beta)d^2`, so define its polynomial
extension `Fbar=f4/(1-beta)` also at the formal endpoint beta=1.
Write exactly

    Fbar(q,beta;x)=f0(q;x)+beta*f1(q;x)+beta^2*R2(q,x,beta),
    f0(q;x)=f4(q,0;x).                                    (6)

Two inherited identities apply to this SAME normal:

    f0=q^2*(q-x)^2*d^3*R0(q,x),
    partial_beta f4(q,0;x)=(-28+2q*partial_q)f0(q;x).     (7)

The accepted fair-source proof gives, on a fixed weak rectangle,
`c(d+e)<=R0<=C(d+e)` and bounded first derivatives. From (7),
`f1=f0+partial_beta f4(q,0;x)=(-27+2q partial_q)f0`; differentiating
the displayed factors yields the UNIFORM bounds

    f0 >= c*d^3*(d-e)^2*(d+e),
    |f1| <= C*d^2*|d-e|*(d+e)^2.                          (8)

The exact saved polynomial has the factored form

    f4 = q^2*(beta-1)*(q-1)^2*P(q,x,beta)/187342848,
    P=P0+beta*P1+beta^2*P2+beta^3*P3.                     (9)

The targeted exact coefficient check verifies, for k=2,3,

    Pk(1,x)=0 identically in x,   partial_q Pk(1,1)=0.     (10)

Thus each Pk has a factor d, and after removing it the quotient vanishes
at `(q,x)=(1,1)`. Being a fixed polynomial, that quotient is bounded by
`C(d+e)` on a fixed weak rectangle. Equations (9)--(10) prove

    |R2(q,x,beta)| <= C*d^3*(d+e)    for ALL 0<=beta<=1.  (11)

In particular this is a finite-polynomial statement with no expansion
assuming bounded beta/e or bounded d/e. The formal endpoints are only
used to bound the polynomial; every actual source remains strict.

## 2. One coercive bound for every physical scale

The exact physical gap is

    ell=log[1+(1-beta)*d/(2q)].

On the fixed weak rectangle, `(1-beta)d/ell` has a positive bounded
extension to d=0 or beta=1. Put `Y=beta*d/e^2`. Dividing (6)--(11) by
the ACTUAL positive `C4 e^5 ell` gives

    G >= c*X^2*(X-1)^2*(1+X)
          -C*Y*|X-1|*(1+X)^2 -C*(1+X)*Y^2.               (12)

No factor depending on the coin is divided without its exact common
endpoint factor. For X>=1/2, apply Young's inequality to

    Y*|X-1|*(1+X)^2
      =[X*|X-1|*sqrt(1+X)]
        *[Y*(1+X)^(3/2)/X],

and use `(1+X)^2/X^2<=9`. For X<1/2, the same mixed expression is at
most a fixed multiple of Y. Since `e/h ->2` and `d/u ->1` uniformly on
the physical weak rectangle, Y and `y=beta*u/h^2` have uniformly
comparable positive factors, including their common zero. Hence

    G >= c*F(X)-C*[1_(X<1/2)*y+(1+X)*y^2].                 (13)

This is a source-uniform FINITE-h bound, not a pointwise claim `G>=0`
or a bounded-X Taylor remainder. It accommodates biased microscopic
cells and arbitrarily rare strict coins.

## 3. Actual whole-word balance and all-source bias

Apply (13) to every actual cell and sum using (4), keeping W4 throughout.
Because `W4>=exp(-28H)>0` and `W4<=1`,

    <F(X)>_ell
       <= C_H*[ <y>_ell +(1+max_i X_i)<y^2>_ell ].         (14)

The independently scoped reviewed full-band theorem supplies

    <y^2>_ell <= C*[h+H^(1/3)h^(2/3)] =: C*epsilon_h.

Cauchy gives `<y>_ell<=C sqrt(epsilon_h)`. The SEPARATE physical-arm
weakness theorem, valid at all rare coins, gives

    max_i X_i <= C*H^(1/3)*h^(-1/3).                      (15)

For fixed H, the right side of (14) is `O_H(h^(1/3))`, proving (1).
No finite-source lower scale, word-count bound or interchange of
uncontrolled high-degree normal moments is used.

## 4. Second moment removes the zero of F at microscopic scale

The same reviewed full-band charge theorem and the exact charge/gap
expansion give `<(u/h)^2>_ell=4+O(sqrt(epsilon_h))`. Since
`d=u+O(u^2)` and `e=2h+O(h^2)`, the inherited bounded fourth moment of
u/h implies

    |<X^2>_ell-1| <= C_H*h^(1/3).                         (16)

More explicitly, `|X^2-(u/(2h))^2|<=C*(u/h)^2*(u+h)`, and its
gap-weighted average is O(h) by the old fourth-moment bound. This
uses no uniform integrability of a higher normal polynomial.

Let `Q=<F(X)>_ell` and `D={X<1/2}`. On the complement,

    (X^2-1)^2 <= 6 F(X).                                  (17)

On D, `1-X^2>=3/4`. Splitting the exact mean in (16), then applying
Cauchy and (17), gives

    <1_D>_ell <= C*(|<X^2>_ell-1|+sqrt(Q)).               (18)

Also `(X^2-1)^2<=1` on D. Equations (17)--(18) yield

    <(X^2-1)^2>_ell
       <= C*[|<X^2>_ell-1|+sqrt(Q)+Q],                    (19)

which with (1),(16) proves (2). In particular the root X=0 of the fair
normal does not leave an unaccounted microscopic gap mass: the positive
second-moment equation eliminates it in the weighted limit.

## 5. Transfer to the literal source action

Let z=u/h. The physical scale comparison above and the separate maximum
u bound give

    <(z^2-4)^2>_ell
       <= C*<(X^2-1)^2>_ell+C*(max u+h)^2*<z^4>_ell.     (20)

The OLD all-source cost bounds `<z^4>_ell`; no z^8 moment is needed.
The exact all-coin J,F,ell source jets and reference calibration give
the previously recorded uniform action expansion

    Action_h/(Lh^4)
       =(3/4)*<(z^2-4)^2>_ell+O(sqrt(epsilon_h)).        (21)

Equation (21) is the conditional hand derivation in
`../2026-10-31-codex-terra-g3-return-residual/BIAS-FREE-ACTION-INTERFACE.md`;
the current result does not silently count the earlier charge review as
an independent review of that separate action expansion. Combining
(2),(15),(20)--(21) gives (3).

The power `25/6` is much weaker than `6+delta`; one cannot invoke the
old phase-rounding consumer from (3). The remaining original producer
task is a much sharper full-source action/phase estimate, or a different
valid source-faithful recognizer/impossibility route.

## Evidence and limits

`check_normal_factor_structure.py` first exited 1 because it mistakenly
selected the small additive factor `beta-1` as the large polynomial core;
its unchanged script and traceback log are preserved. The corrected
`check_normal_factor_structure.v2.py` exited 0 against the exact pinned
normal body SHA-256
`2844871e9c48a810df35670da4b5eb1f8c02c564d0c5bf3a13e43c141c097a3a`.
It checks the exact outer factor and the four identities in (10).
The inequalities and all-word/quantifier argument above are hand-derived,
not machine-verified. No new forest/source bank, parameter grid, higher
cap, external service, or physical realization experiment was run.
