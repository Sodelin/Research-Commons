# A small-H improvement for the all-source bias cost

Contributor: Codex Terra, 31 October 2026. Hand-derived full-fibre
consequence of the matched-rate identity in `PROOF-AND-SURVIVING-TERM.md`
and the named original source suppliers. The finite diagonal/reference
coefficients are checked as recorded below; independent review and formal
verification of this integration are pending. It does NOT prove bias
vanishes at fixed H, AG-Pair, phase, or original G3 closure.

## Statement and quantifiers

There are fixed sufficiently small `H0,h0>0` and one fixed C such that,
for every allowed `H=(log 2)/m` in `(0,H0]`, every
`0<h<min(h0,H/4)`, and EVERY actual finite strict same-tuple paired
equal-arm word with complete cap12 commutation with the existing reference
S(t),

    (1/L) sum_i ell_i*y_i^2
       <= C*[H+h+H^(1/3)h^(2/3)] <= C'*H.                   (1)

where `L=H/4`, `u_i=-log q_i`, `beta_i=(2g_i-1)^2`,
`y_i=beta_i*u_i/h^2`, and
`ell_i=log[b2(B_i)/q_i]`. The sum is over ALL actual cells, including
arbitrarily small, large-relative-scale, and rare-coin cells. Constants
do not depend on word length, chronology, H, h or the coin margins. The
last bound uses the ORIGINAL `h<H/4` reference domain and a new fixed
constant `C'`.

Equivalently, at every fixed allowed small H, the limsup as h tends to zero
is at most `C H`. The old generic source cost supplied an `O(1)` bound;
this establishes an `O(H)` small-budget bound for the whole bias moment.
Since H is fixed in the AG-Pair quantifiers, (1) alone does NOT give
`o_h(1)` or force fair microscopic gap mass to disappear.

## 1. Existing all-source estimates

Retain the exact notation `T=3H/4`, `c=exp(-H)`, `v_i=g_i(1-g_i)`,
the physical prefix pair time `a_i=-log b2(P_i)`, and

    s_i=v_i*(beta_i^2*u_i^3+beta_i*u_i^4+u_i^5),
    Cchi=sum_i chi_i.

The inherited cap12 source cost, cap4 charge balance and COMMON budget
give, uniformly in the stated domain,

    sum s_i <= C Hh^4,       sum v_i u_i <= H/4,
    sum v_i(beta_i u_i^2+u_i^3) <= C Hh^2,
    sum v_i(beta_i u_i^3+u_i^4) <= C Hh^3.                 (2)

The third bound uses the old positive cap4 endpoint to compare the
weighted biased term with `sum v u^3`; the fourth is Cauchy--Schwarz
against the SAME full cost. Consequently

    sum |chi_i| <= C Hh^2,    sum u_i|chi_i| <= C Hh^3,
    sum |A5_i-(3/2)chi_i| <= C Hh^3.                       (3)

No division by a coin margin or assumed lower microscopic scale is used.

## 2. The actual unweighted chi total

Let `D_r(X)=b_r(X)/b2(X)^lambda_r`. For each fixed r, the old actual
diagonal expansion gives `log D_r(B)=O(v(beta u^2+u^3))`. Summing over
ANY actual prefix or suffix and using (2) gives `O(Hh^2)` uniformly.
For the cap5 5-to-2 weight this yields

    W52_i=exp(-T-9a_i)*exp(tau_i)*[1+O(Hh^2)],
    tau_i=-log b2(B_i)<=u_i.                                (4)

The current-cell factor `exp(tau_i)` is kept; after multiplying by chi,
its total replacement error is bounded by `sum u_i|chi_i|=O(Hh^3)`.
The exact cap5 endpoint and (3), with actual `k_r` retained, imply

    sum_i exp(-9a_i)*chi_i/h^2
       = (2/81)*(1-exp(-9T))+O(Hh).                         (5)

Indeed `s2-s5=27h+O(h^2)`, `t^10 b A5_*=h^3+O(h^4)`, and
the actual diagonal estimate gives `k_r=exp(-lambda_r T)[1+O(Hh^2)]`.
Since `a_i in [0,T]` and `sum|chi_i|/h^2=O(H)`, removing the weight in
(5) costs at most `O(H^2)`. As `2T/9=H/6`,

    Cchi/h^2 = H/6+O(H^2+Hh).                              (6)

This is an estimate for the SAME signed actual cells, not a pointwise
positivity claim, a source selector, or an exact unweighted conservation.

## 3. Matching the true cap5/cap6 endpoints

For `r=4,5,6`, the actual same-cell diagonal has the uniform identity

    log D_r(B_i) = -(3/2)binom(r,3)chi_i
                      +O[v_i*(beta_i*u_i^3+u_i^4)].         (7)

It follows from the actual binomial no-merger polynomial: the quadratic
pair-color covariance has factor `v beta`, and the remaining cubic error
has factor `v beta`; the higher remainder has factor v. The targeted exact
diagonal check records all three cubic coefficients. Summing (7) and
using (2)--(3) gives

    k4=e^(-6T)[1-6Cchi+O(Hh^3+H^2h^4)],
    k5=e^(-10T)[1-15Cchi+O(Hh^3+H^2h^4)],
    k6=e^(-15T)[1-30Cchi+O(Hh^3+H^2h^4)].                  (8)

These are CONSEQUENCES with errors; no unknown diagonal is assumed equal
to a fractional S power.

Use the exact `E52,E64` in the preceding matched-rate proof. Denote

    Gamma5=t^10*b*A5_*/(s2-s5),
    Gamma6=t^15*b^6*A6_*/(s4-s6).

The LEFT-normalized fair `J5,J6` agree through degree five, and the
actual fair reference diagonals satisfy
`log D_r(S)=-binom(r,3)h^3+O(h^4)`. Therefore

    Gamma5=h^2/27+O(h^3),
    Gamma6/Gamma5=1-(2/9)h^2+O(h^3).                       (9)

For clarity, the second formula retains the actual denominators. Since
`s2=t^3`, it follows from

    Gamma6/Gamma5 = (J6_*/J5_*)
       *[1-s2^9 D5(S)]/[D4(S)-s2^9 D6(S)].                  (10)

`J6_*/J5_*=1+O(h^3)`; the displayed quotient contributes the `-2/9`.
Putting `A=exp(-T)` and `B=exp(-10T)`, substitution of (8)--(9) into
the TRUE endpoint difference gives

    e^(5T)E64-E52
      = (h^2/27)*[(-6A+15B)Cchi-(2/9)h^2(A-B)]
          +O(Hh^5+H^2h^6).                                (11)

At `Cchi/h^2=H/6`, the square bracket divided by h^2 is `O(H^2)`:
`(-6A+15B)H/6` and `(2/9)(A-B)` have the SAME linear term in H.
Using the actual estimate (6),

    |e^(5T)E64-E52| <= C*(H^2 h^4+Hh^5).                  (12)

This is not a claim that the endpoint vanishes at h^4: the preceding
proof records its strictly nonzero negative fair-reference coefficient.

## 4. Keep, bound, and subtract the diagonal correction

The EXACT matched-rate identity is

    e^(5T)E64-E52-R_diag = -6 P_bias+Err,
    |Err|<=C H^(4/3)h^(14/3),                               (13)

with the actual positive `P_bias` and signed `R_diag` defined there.
The physical-arm weakness theorem is indispensable for the remainder.
Uniform prefix estimates in (2) give `|Delta_i-1|<=C Hh^2`, and the same
actual-source jet gives `sum |A6_i|<=C Hh^2`. Retaining the current-cell
factor `exp(5tau_i)`, one gets only

    |R_diag| <= C H^2 h^4.                                 (14)

This is an absolute bound, not an o(`Hh^4`) estimate at fixed H and not
a sign assertion. Equations (12)--(14) yield

    P_bias <= C*[H^2h^4+Hh^5+H^(4/3)h^(14/3)].             (15)

Finally the exact source weight obeys
`W52_i*b2(B_i)^10>=c^10`, and
`ell_i<=2exp(H0)v_i u_i`. Thus

    P_bias >= [c^10/(2exp(H0))] h^4 sum ell_i y_i^2.

Divide by `h^4 L`, using `c>=exp(-H0)`, to obtain (1).

## 5. Exact limit of this progress

For any tolerance one may choose a sufficiently small fixed allowed H so
that the SAME all-source bias moment is below that tolerance throughout
the stated h domain. This is a genuine source consequence of the full
paired commutator and uses no coin or word-length restriction. It does
not say the moment tends to zero as h tends to zero at that fixed H.
Achieving that stronger limit still needs the signed cancellation

    e^(5T)E64-E52-R_diag = o(Hh^4)

uniformly over the original full fibre, or a different argument. The
endpoint and correction cannot be separately dropped: both have the same
nonzero negative h^4 coefficient on intended fair reference powers.
No phase, count upper bound, witness selector, AG-Pair or original master
decision follows here.

## Evidence

`check_chi_diagonal_jet.py` checks the three actual-binomial diagonal jets
used in (7), and `check_reference_ratio.py` checks the formal reference
ratio and the first-order small-H cancellation. Both direct processes
exited 0; logs are saved. They do not run a full forest bank, parameter
grid or Lean. The exact all-coin source identity, physical-arm weakness,
original source pins and fair nonzero correction are preserved in
`PROOF-AND-SURVIVING-TERM.md` and its manifest.
