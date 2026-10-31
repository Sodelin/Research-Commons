# A positive-kernel improvement of the all-source bias bound

Contributor: Codex Terra, 31 October 2026. Hand-derived full-fibre
consequence of the exact matched-rate identity and the four previously
derived charge moments. Its scalar kernel/interpolation algebra is
checked as recorded below. Independent mathematical review and formal
verification are pending. In particular, the bound still does NOT vanish
as h tends to zero at one fixed H, and original G3 remains open.

## Statement

Under precisely the original small-H, finite strict same-tuple paired
equal-arm complete-cap12 fibre of `SMALL-H-ALL-SOURCE-BIAS.md`, there is
one fixed constant C such that uniformly in all physical source lengths,
chronology, strict coins and relative scales,

    (1/L) sum_i ell_i*y_i^2
       <= C*[H^6+h+H^(1/3)h^(2/3)],                         (1)

where `L=H/4`, `y_i=beta_i*u_i/h^2`, and the sum includes EVERY actual
bigon. Thus for any fixed sufficiently small allowed H,

    limsup_(h->0) sup_(K in F_H(h)) (1/L)sum ell_i*y_i^2 <= C H^6.

The sup is over nonempty original full fibres. This improves the earlier
`O(H)` limsup and the old `O(1)` source-cost bound. The error still leaves
a positive H-dependent floor; (1) does not prove the required `o_h(1)` at
fixed H, fair-dust removal, integer phase or a recognition algorithm.

## 1. Actual signed charge and its four known tests

Let `T=3H/4`, `a_i=-log b2(P_i)` for the ACTUAL prefix before the cell,
and define signed finite measures on `[0,T]`

    theta_h=sum_i (chi_i/h^2) delta_(a_i),
    theta_0=(2/9) da,
    eta_h=theta_h-theta_0.                                 (2)

The accepted cap4/source-cost estimates used in the preceding note give
`||theta_h||_TV<=C H`, hence `||eta_h||_TV<=C H`. The four actual
cap4/cap5 moment constraints in the companion microscopic-fibre-gate
proof imply, uniformly for `lambda=5,7,9,10`,

    |int_0^T exp(-lambda*a) d eta_h(a)| <= C Hh.            (3)

Indeed the unperturbed integral is
`(2/(9lambda))*(1-exp(-lambda*T))`. The O(Hh) form follows by multiplying
the gap-normalized proof by `L/6`: every source, current-cell, endpoint
and denominator error there is bounded with the same initial fixed
small-H constants. It is not a claim of exact uniformity in time.

## 2. Exact matched receiver and the quadratic kernel

Use the exact source weights, true endpoints, signed `R_diag` and actual
positive `P_bias` of `PROOF-AND-SURVIVING-TERM.md`. In particular

    Z=exp(5T)E64-E52-R_diag,
    Z=-6P_bias+O(H^(4/3)h^(14/3)).                          (4)

For `a,b in [0,T]` set

    K(a,b)=4 exp[-9 min(a,b)]+10 exp[-9 max(a,b)],
    E(eta)=int int min(exp(-9a),exp(-9b)) d eta(a)d eta(b).  (5)

Despite eta being signed, `E(eta)>=0`: after pushing forward by
`x=exp(-9a)`, the kernel `min(x,x')` equals
`int_0^1 1_{t<=x}1_{t<=x'} dt`. Thus it is the integral of the square of
the SAME signed cumulative measure.

The matched receiver has the uniform expansion

    Z/h^4 = exp(-T)*[3 M_h+(27/4)E(eta_h)]
              +O(Hh+H^(4/3)h^(2/3)),                       (6)
    M_h=int_0^T a exp(-9a) d eta_h(a).

This is a consequence, not an additional hypothesis. The derivation is
included next because the second-order diagonal terms cannot be discarded.

### Derivation of (6)

For any actual segment X, the checked all-coin diagonal jet gives

    log D_r(X)=-(3/2)binom(r,3) sum_(B_j in X) chi_j
                  +O(Hh^3),  r=4,5,6.                      (7)

The error is uniform for every prefix and suffix by the full source-cost
bound. With `Cpre_i=sum_(j<i)chi_j` and `Csuf_i=sum_(j>i)chi_j`,

    Delta_i-1 = -15 Cpre_i-6 Csuf_i+O(Hh^3+H^2h^4),
    sum_i |A6_i-(3/2)chi_i| <= C Hh^3.                       (8)

Use the exact `W52_i exp(5tau_i)` in `R_diag`, and only AFTER summation
replace it by `exp(-T-9a_i)`. The omitted current-cell error is paid by
`sum u_i|chi_i|=O(Hh^3)`. Equations (7)--(8) then give

    R_diag/h^4 = -(9/4)exp(-T) sum_(i<j)
       (chi_i chi_j/h^4)*[4 exp(-9a_i)+10 exp(-9a_j)]
       +O(Hh).                                              (9)

The physical diagonal `i=j` has NOT been inserted. Replacing the ordered
sum by the continuous symmetric kernel costs at most `C sum chi_i^2/h^4`.
For the old `r_i=v_i(beta_i u_i^2+u_i^3)`, the exact source majorant
satisfies `|chi_i|<=C r_i` and `r_i^2<=u_i*s_i/2`. The separately pinned
full-cap12 PHYSICAL-arm weakness theorem and source cost therefore give

    sum chi_i^2/h^4 <= C H max_i u_i
                       <= C H^(4/3)h^(2/3).                (10)

Consequently (9) equals
`-(9/8)exp(-T) int int K dtheta_h dtheta_h` up to the error in (6).

The SAME endpoint expansion, with `Cchi=sum chi_i`, is

    (exp(5T)E64-E52)/h^4
      = [(-6e^(-T)+15e^(-10T))*(Cchi/h^2)
           -(2/9)(e^(-T)-e^(-10T))]/27+O(Hh).              (11)

Subtract the reference measure `theta_0`. Direct scalar integration
shows its constant term cancels exactly. The cross term is

    exp(-T)*int [(1/3+2T+3a)exp(-9a)] d eta_h(a).

Finally, with `x=exp(-9a)` and `x'=exp(-9b)`,

    K(a,b)=4(x+x')+6 min(x,x').

The terms involving `int exp(-9a)d eta_h` are O(Hh) by (3) and the TV
bound. What remains is precisely (6), with the positive coefficient
`27/4`. The scalar integrations and factors are exactly checked in
`check_kernel_identity.py`.

## 3. Four-rate interpolation and positive-energy absorption

The four functions already supplied by the actual cap4/cap5 channels
approximate the missing derivative test at a=0:

    a exp(-9a) = -exp(-5a)/20+exp(-7a)/3
                    +exp(-9a)/4-8exp(-10a)/15+r(a),
    |r(a)|<=C a^4,   |r'(a)|<=C a^3  (0<=a<=T).            (12)

Thus the known moments reduce M_h to `int r d eta_h` up to `O(Hh)`.
For the positive-kernel norm, subtract a multiple of the ALREADY controlled
rate-9 test:

    r0(a)=r(a)-r(T)exp(9T)exp(-9a),    r0(T)=0.

After pushing `eta_h` to `x=exp(-9a)`, put
`g(x)=r0(-log(x)/9)` on `[exp(-9T),1]`. It has `g(exp(-9T))=0`, and
`|g'(x)|<=C H^3` on an interval of length O(H). Fubini and
Cauchy--Schwarz for the min kernel yield

    |int r0 d eta_h|
       <= [E(eta_h)]^(1/2) * [int |g'(x)|^2 dx]^(1/2)
       <= C H^(7/2)*[E(eta_h)]^(1/2).                      (13)

This remains true for a signed eta and does not posit a density or
ordinary-clock source. The coefficient subtracted from r is O(H^4), so
its controlled rate-9 moment costs at most O(Hh). Therefore

    |M_h| <= C H^(7/2)*sqrt(E(eta_h))+C Hh.                (14)

Combine (4), (6), E>=0 and (14). Young's inequality absorbs half the
positive E term and gives

    P_bias/h^4 <= C*[H^7+Hh+H^(4/3)h^(2/3)].                (15)

The exact source weights satisfy `W52_i*b2(B_i)^10>=c^10`, and
`ell_i<=2exp(H0)v_i u_i`. Hence

    P_bias >= [c^10/(2exp(H0))]h^4 sum ell_i*y_i^2.

Divide (15) by L and use `c>=exp(-H0)` to prove (1). The same absorption
also bounds the positive signed-profile kernel energy E by the right side
of (15), up to a fixed constant.

## 4. Evidence and remaining gap

`check_kernel_identity.py` verifies the exact four-node interpolation,
the symmetric kernel's reference integral and its cross-term coefficients
by scalar symbolic arithmetic. Its direct process exited 0. The existing
targeted 5/6-root EPPF, diagonal-jet, fair-reference and endpoint checks
are preserved in the two preceding notes and their manifests. No new full
source bank, parameter grid, Lean or external service was run.

The exact remaining goal is still to remove the fixed-H floor: prove the
relevant actual signed derivative/endpoint term has the needed
`o_h(1)` behavior, or find a different full-source argument. Four finite
Laplace tests do not determine that derivative for a general signed
profile, and the present Hilbert-space absorption pays the positive
`O(H^7)` cost in (15). No limiting abstract profile has been promoted to
an admitted word, and no phase or master closure is claimed.
