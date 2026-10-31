# The remaining calibrated action after all-source bias suppression

Stable key: G3-BIAS-FREE-ACTION-INTERFACE-TERRA-20261031-01.
Contributor: Codex Terra, 31 October 2026. Hand-derived conditional
consequence of `FULL-BAND-CHARGE-TEST.md` and the cited existing source
jets; independent review and formal verification pending. This records
the next phase-facing interface, not a phase theorem or original G3
closure. It does not infer that an abstract limiting profile is realizable.

## Exact scope and conclusion

Use the same fixed-small-`H`, all-strict-coins, finite-word, paired
complete-cap12 fibre and constants as `FULL-BAND-CHARGE-TEST.md`. Define

    z_i=u_i/h,  y_i=beta_i*u_i/h^2,
    <f>_ell=(1/L) sum_i ell_i f_i,  L=H/4,
    epsilon_h=h+H^(1/3)h^(2/3),
    Action_h=sum_i Phi_h(C_i),

with the EXACT reference-calibrated source action Phi of
`REFERENCE-CALIBRATED-SOURCE-ACTION.md`. Then uniformly on the actual
fibre,

    <y^2>_ell <= C epsilon_h,                             (1)
    |<z^2>_ell-4| <= C sqrt(epsilon_h),                  (2)
    |Action_h/(Lh^4) - (3/4)<(z^2-4)^2>_ell|
         <= C sqrt(epsilon_h),                            (3)
    |Action_h/(Lh^4) - (3/4)(<z^4>_ell-16)|
         <= C sqrt(epsilon_h).                            (4)

The constants are uniform in strict coins, physical cell lengths,
chronology and finite source count on the inherited fixed small domain.
Equations (3)--(4) are *additive asymptotics at scale Lh^4*; they are not
relative estimates at the much smaller scale needed for phase rounding.

In particular, on any sequence of actual fitting words at fixed H,
`<y^2>_ell -> 0` and `<z^2>_ell -> 4`. A subsequential gap-weighted weak
limit therefore has `y=0` almost surely. This supersedes only the earlier
observation that positive-y dust was possible under a SMALLER set of
necessary equations. It does not exclude mass at `(z,y)=(0,0)`, nor does
it claim that any surviving abstract limit comes from an actual word.

## 1. Charge fixes the second gap-weighted scale moment

The independently source-derived exact charge expansion in
`CHRONOLOGICAL-GAP-LIMIT.md` is uniform even for rare coins:

    chi_i/(ell_i h^2)
       =(z_i^2-6y_i)/6 + O(u_i*(z_i^2+y_i)).             (5)

Here `(1/L)sum ell_i z_i^4<=C` is the inherited all-source cost bound.
From the new all-source result (1), Cauchy gives

    <y>_ell+<y*z^2>_ell <= C sqrt(epsilon_h).             (6)

The separate physical-arm theorem gives
`max_i u_i<=C H^(1/3)h^(2/3)`. Therefore the averaged remainder in (5)
is `O(epsilon_h)`. Applying the full-band smooth-test result to `f=1`
and using `T=3H/4=3L` gives

    (1/L)sum_i chi_i/h^2 = (2/9)*T/L+O(h)=2/3+O(h).

Equations (5)--(6) yield (2). In particular, the second moment passes
through weak limits using the existing fourth-moment uniform
integrability; the fourth moment itself is NOT asserted uniformly
integrable merely from its bounded expectation.

## 2. Uniform all-coin action expansion

The held source rules, always for the SAME normalized actual cell, give

    J = v[54 beta^2 u^3 -15 beta u^4 +(3/2)u^5] + O(u*s),
    F = v[-beta u^2/5+u^3/30+O(beta u^3+u^4)],
    ell = 2vu[1+O(u)],
    a_ref=360h^2+O(h^3),  b_ref=12h^4+O(h^5),            (7)
    Phi=J-a_ref*F+b_ref*ell.

The first jet is the exact displayed `56 sigma+55 rho` combination in
`POSITIVE-TRANSVERSE-SOURCE-COST.md`; `s` is the old positive source
majorant. For F, the all-coin quadratic and fair cubic coefficients,
closed-coin analyticity after division by v, and coin symmetry give the
displayed remainder as in `FULL-BAND-CHARGE-TEST.md`. The quotient for
ell has a uniform removable extension to the rare-coin boundary. No
cell is assumed near fair or comparable to h.

Divide (7) by the ACTUAL `ell*h^4` and substitute `z,y`. With a uniform
constant, all discarded terms are bounded by
`C(u+h)*(1+y^2+z^4)`. Hence

    Phi/(ell*h^4)
       =(3/4)(z^2-4)^2+27y^2-(15/2)y*z^2+36y
          +O((u+h)*(1+y^2+z^4)).                         (8)

The positivity of Phi is an exact earlier source theorem; (8) is only a
uniform leading expansion. Average (8), retain the true gap weights,
use (1), (6), the fourth-moment bound, and the physical-arm maximum.
This proves (3). Expanding `(z^2-4)^2=z^4-8z^2+16` and applying (2)
proves (4). There is no unjustified division by y, z, or a coin margin.

## 3. What is still missing for the original task

The terms in (3) show explicitly that the remaining leading action is
the FAIR scale-dispersion/dust cost after bias is suppressed. A full
source-conditioned proof forcing that cost to zero would already be a
further mathematical result. The present identity supplies no such
upper bound, because `sum ell_i=L` and `<z^2>_ell -> 4` do not determine
`<z^4>_ell`.

For the existing sufficient rounding route, one needs a substantially
finer actual-source statement, for example a supply of fitting physical
words with `Action_h<=C_H h^(6+delta)` for some fixed `delta>0` over the
relevant small h values. This is a sufficient target, not a claim of
necessity for G3. Even a proof that `<z^4>_ell-16=o(1)` would only imply
`Action_h=o(Lh^4)` through (4); and the explicit `O(sqrt(epsilon_h))`
error is much too large to transfer a guessed `h^(2+delta)` fourth-moment
rate to the action. The weighted full-band endpoint equations and their
actual prefix/diagonal terms must still provide a sharper, source-valid
condition or a different master-facing argument.

## Evidence

Hand derivation only. No new bank, parameter grid, source engine, formal
checker, external service, or full-fibre realization experiment was run.
The companion `SHA256SUMS.v2.txt` binds this file, the preceding new
proof and the original supplier/review bytes. It does not modify the
earlier preserved manifest or claim an independent review of this note.
