# Remainder and quantifier audit for the positive-kernel argument

Contributor: Codex Terra, 31 October 2026. This audits the proof in
`PSD-ALL-SOURCE-IMPROVEMENT.md`, SHA-256
`5957ea81b40dd41256367b18349eda647410f4e068a926e0729e3efa27202964`.
It is the author's hand audit, not a separate independent acceptance or
formal verification. The main coordinator independently checked the
kernel formula and the interpolation-norm argument as conveyed in the
31 October coordination; that scoped check did not rerun the transitive
source engines or by itself review every estimate below.

Fix the inherited small `H0,h0` once. The notation and source suppliers
are exactly those in the bound proof. The constants below are uniform in
`0<H<=H0`, `0<h<min(h0,H/4)`, all actual finite word lengths, strict
coins including rare ones, relative scales and physical placements.

## 1. Source and moment errors

The inherited cost, cap4 charge and Cauchy--Schwarz give

    sum v*u^3, sum v*beta*u^2, sum |chi| <= C Hh^2,
    sum v*(beta*u^3+u^4), sum u*|chi| <= C Hh^3.          (1)

The first line uses `sum v*u<=H/4`, `sum v*u^5<=C Hh^4` and the
old biased-charge bound. In the second line use

    sum v*beta*u^3 <= sqrt(sum v*beta^2*u^3 * sum v*u^3),
    sum v*u^4 <= sqrt(sum v*u^3 * sum v*u^5).

The exact A5/chi identity and the targeted A6-A5 deletion polynomial
also give the SAME-source bound

    sum |A6-(3/2)chi| <= C Hh^3.                           (2)

At cubic order the divided A6-A5 coefficient has the factor
`(3/2)beta(5+beta)`; the fair cubic is zero, and all remaining terms
have the original endpoint factor v and a further power of u. Thus (2)
does not divide by, or bound away, v or beta.

For the four moment tests, let `theta_h=sum (chi_i/h^2)delta_(a_i)`
and `theta_0=(2/9)da`. Every exact weight is

    W_(n,r),i=exp[-lambda_r*T-(lambda_n-lambda_r)a_i]
                 *exp(lambda_r*tau_i)*D_n(P_i)D_r(Q_i),
    tau_i<=u_i.

Here the actual pre/post segment D factors and the omitted current cell
are shown explicitly. Replacing this weight by its ordinary-clock leading
factor in the SOURCE SUM costs `O(Hh^3)` by (1), the uniform
`D=1+O(Hh^2)`, and `sum |chi|=O(Hh^2)`. The sources themselves are
`chi` for 4-to-2 and `(3/2)chi+O(Hh^3)` after summing for each cap5
channel. Each exact reference endpoint divided by h^2 is its leading
`O(H)` value plus `O(Hh)`: the reference source is O(h^3), its strict
diagonal difference is O(h), and actual endpoint diagonal errors are
O(Hh^2). Thus for every `lambda in {5,7,9,10}`,

    |int exp(-lambda*a) d(theta_h-theta_0)| <= C Hh.       (3)

This is the H-uniform version of the reviewed four-rate result; it does
not pass the higher-degree normal equations through an unproved tail limit.
The independent scoped review of that source/normal/abstract-model
boundary is `../2026-10-31-codex-terra-g3-microscopic-fibre-gate/REVIEW.md`,
SHA-256 `245381820f47ab1c79fd2ee239f76ee495c135e30420bee6f0595d067fe722d6`.

## 2. Actual diagonal correction through order h^4

The checked diagonal expansion and (1) give for ALL actual pre/post
segments, with `Cpre_i=sum_(j<i)chi_j`, `Csuf_i=sum_(j>i)chi_j`,

    log Delta_i = -15 Cpre_i-6 Csuf_i+O(Hh^3),
    Delta_i-1 = -15 Cpre_i-6 Csuf_i+O(Hh^3+H^2h^4).      (4)

Also the exact comparison has

    W52_i exp(5tau_i)
      =exp(-T-9a_i)*exp(6tau_i)*D5(P_i).

Use (1)--(2), `tau_i<=u_i`, and `D5(P_i)=1+O(Hh^2)`. Replacing the
current-cell/source/prefix factors ONLY AFTER summing gives

    R_diag=-(9/4)exp(-T) sum_(i<j)chi_i chi_j
               *[4 exp(-9a_i)+10 exp(-9a_j)]
               +O(H^2 h^5).                                (5)

The displayed error absorbs the `O(H^3h^6)` term by shrinking the fixed
small domain. Equation (5) retains both orders of each physical pair; it
is not a sourcewise square or a separately fitted time profile.

The endpoint calculation in the preceding proof keeps the actual k4,k5,k6
and gives, with `A=exp(-T),B=exp(-10T),Cchi=sum chi_i`,

    exp(5T)E64-E52
       =(h^2/27)*[(-6A+15B)Cchi-(2/9)h^2(A-B)]
           +O(Hh^5+H^2h^6).                                (6)

The reference factor `Gamma6/Gamma5=1-(2/9)h^2+O(h^3)` is the tested
actual reference denominator ratio. The error in (6) divided by h^4 is
`O(Hh)`, because `Hh<=1` on the chosen domain.

## 3. Self-pairs and the signed positive kernel

The ordered sum in (5) has i<j. For
`theta_i=chi_i/h^2`, the checked symmetric kernel has diagonal
`K(a_i,a_i)=14 exp(-9a_i)`. Its extra self-pairs are controlled by

    sum_i theta_i^2
       <= C h^(-4) sum_i u_i*s_i
       <= C H*max_i u_i
       <= C H^(4/3)h^(2/3).                                (7)

The last step is the SEPARATE reviewed physical-arm theorem; weighted
source cost alone would not establish it for rare coins. This is the
origin of the finite-h `h^(2/3)` error and is not an extrapolation from
an effective pair-gap scale.

With `eta=theta_h-(2/9)da`, the exact scalar integration checked in
`check_kernel_identity.py`, equations (3), (5)--(7), and
`||eta||_TV<=C H` give

    Z/h^4=exp(-T)[3M+(27/4)E(eta)]
              +O(Hh+H^(4/3)h^(2/3)),                      (8)
    M=int a exp(-9a)d eta.

The rate9 cross terms are proportional to its moment error `O(Hh)`;
the remaining cross term is exactly `3M`. In the original time variable
the positive kernel can also be written

    E(eta)=exp(-9T)*eta([0,T])^2
          +9 int_0^T exp(-9a)*eta([0,a])^2 da >=0.          (9)

This identity is valid for signed finite measures, including atoms. The
positive square is a consequence of THIS matched full-source expansion;
it is not asserted to be a global endpoint cocycle or to control the
signed linear term M by itself.

## 4. Interpolation and final error accounting

The four already acquired rates give an interpolation remainder r with
`|r|<=C a^4`, `|r'|<=C a^3`. Subtract the controlled rate9 function
so `r0(T)=0`. Equation (3) pays `O(Hh)` for all subtracted tests, while
`|r0'|<=C H^3`. The Cauchy bound in (9) gives

    |M|<=C H^(7/2)*sqrt(E(eta))+C Hh.                      (10)

Combining (8) with the exact all-coin source comparison
`Z=-6P_bias+O(H^(4/3)h^(14/3))`, then using Young's inequality to absorb
half the positive E term, yields

    P_bias/h^4 <= C[H^7+Hh+H^(4/3)h^(2/3)].                 (11)

The original exact physical weights satisfy
`P_bias >= c^10 h^4 sum ell_i*y_i^2/(2 exp(H0))`. Dividing by
`L=H/4` gives exactly the claimed
`C[H^6+h+H^(1/3)h^(2/3)]`. No step sends H to zero as a function of h;
at fixed H the `C H^6` floor remains. It may be made small by choosing an
allowed fixed m, but it does not establish the fixed-H vanishing needed
by the stated AG-Pair route.

No new source engine, numeric parameter grid, full bank, Lean or external
service was run for this audit. The earlier targeted symbolic scalar
checks and their direct exit-0 logs remain separately hash-bound.
