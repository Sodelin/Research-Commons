# Full-band return controls the actual chronological charge profile

Stable key: G3-FULL-BAND-CHARGE-TEST-TERRA-20261031-01.
Contributor: Codex Terra, 31 October 2026. **Hand-derived, conditional on
the cited source/energy suppliers; independent review and formal
verification pending.** The scalar estimates below use the original
physical sources. No new source engine, parameter grid, or full bank was
run. The conclusion is a full-fibre bias suppression statement, not
AG-Pair, a phase theorem, or closure of original G3.

## Statement and quantifiers

Use the paired equal-arm finite-word fibre, unchanged reference `S(t)`,
both clocks, and complete `[K_I,S(t)]=0` through cap 12 of
`../2026-10-31-codex-terra-g3-equal-rate-channel/PSD-ALL-SOURCE-IMPROVEMENT.md`.
Thus `H=(log 2)/m` is selected sufficiently small **before** `h -> 0`,
`L=H/4`, `T=3H/4`, and the number, chronology, relative scales and every
strict coin are arbitrary. There are uniform constants on one fixed small
`H,h` domain. Write, for each physical cell,

    u_i=-log q_i,  v_i=g_i(1-g_i),  beta_i=(2g_i-1)^2,
    tau_i=-log b2(B_i),  ell_i=log(b2(B_i)/q_i),
    y_i=beta_i*u_i/h^2,  a_i=-log b2(P_i),
    chi_i=(v_i/3)(1-exp(-u_i))^2
                       *[(1-exp(-u_i))-(5+exp(-u_i))*beta_i],

where `P_i` is the ACTUAL product before `B_i`, with all ordinary gaps.
The exact clocks give `sum ell_i=L` and total pair-normalized ordinary
duration `T`. Define the signed actual charge profile

    eta_h=sum_i (chi_i/h^2) delta_(a_i) - (2/9) da,  0<=a<=T.  (1)

For every continuously differentiable real function `f` on `[0,T]`,
the full-fibre return and the inherited cap-12 energy imply

    |int f d eta_h|
       <= C Hh*(||f||_infinity+||f'||_infinity).          (2)

The same `C` works for all allowed source words and coins; the displayed
norms refer to `[0,T]`. This is a smooth-test estimate, not a total
variation estimate and not a statement that every time interval contains
any particular cell. It includes the actual interpolation residual `r0`
of the PSD note, and in particular

    M_h=int a exp(-9a) d eta_h = O(Hh).                    (3)

Consequently the independently scoped reviewed matched identity and
positive kernel `E(eta)` in that note give

    P_bias/h^4 + E(eta_h)
       <= C*[Hh+H^(4/3)h^(2/3)],                           (4)
    (1/L) sum_i ell_i*y_i^2
       <= C*[h+H^(1/3)h^(2/3)].                            (5)

Here `P_bias` is the exact positive, physically weighted quantity in
`PROOF-AND-SURVIVING-TERM.md`, not a free source parameter. In particular,
for each fixed admissible `H`, the supremum of the left side of (5) over
the nonempty original fibres tends to zero with `h`. If a fibre is empty,
the universal finite-word assertion is vacuous. This removes the `H^6`
floor in the earlier bias estimate. It does not remove unbiased dust,
bound the source action, or select an integer phase.

## 1. The inherited full-band state

We quote the actual fixed-reference 9-to-6 state `b` from
`QUADRATIC-STATE-ABSORPTION.md` and the cap-12 energy from
`RESONANT-ORDINARY-FORCING-ENERGY.md`. Pair-normalize on the LEFT:

    C_i=E(-tau_i)B_i,  B_i=E(tau_i)C_i.

The inverse is an algebraic device, not a physical source. The positive
`tau_i` ordinary segment remains in the original word. On the resulting
nominal time axis the full reference-basis state satisfies

    b(0)=b(T)=0,  b'=21(b-B_h),
    B_h=h^2/945+O(h^3),  E_b=int_0^T b(a)^2 da <= C Hh^6.  (6)

Its source jump after the `tau_i` segment is EXACTLY

    b_i+ - b_i- = F_i/d9_i + (gamma_i-1)(b_i- - B_h),
    F_i=J9(C_i)/15,  gamma_i=d6_i/d9_i,                    (7)

with the old diagonal notation. `J9(C_i)=exp(36 tau_i) A9(B_i)` and
`chi_i=(2/3)A4(B_i)` have different normalizations. Endpoints vanish by
the full commutator in the fixed reference basis; unknown word diagonals
remain unknown, and are never set to reference fractional powers.

The inherited uniform bounds include, with

    r_i=v_i*(beta_i*u_i^2+u_i^3),
    s_i=v_i*(beta_i^2*u_i^3+beta_i*u_i^4+u_i^5),

    sum s_i<=C Hh^4,   sum r_i<=C Hh^2,
    sum r_i^2/u_i<=C Hh^4,
    sum u_i*(b_i-)^2<=C E_b,
    |gamma_i-1|+|d9_i-1|<=C r_i,  |F_i|<=C r_i.          (8)

The trace uses each cell's disjoint OWN PRECEDING ordinary interval and
retains its affine forcing. It does not impose a minimum cell size or a
coin margin. The `d9` reciprocals are uniformly bounded on the stated
domain. The separately inherited moment consequences are

    sum v_i*u_i^3 + sum v_i*beta_i*u_i^2 <= C Hh^2,
    sum v_i*(beta_i*u_i^3+u_i^4) <= C Hh^3,
    sum u_i*|chi_i| <= C Hh^3.                            (9)

For example the second line follows by Cauchy--Schwarz from the first
line and `sum s_i<=C Hh^4`. All bounds are valid even for rare coins.

## 2. The SAME source supplies the charge, with correct factors

For one actual cell, the already held all-n merger count gives

    [u^2] J9(C)=-3 v beta,
    J9(C)|_(beta=0)=u^3/8+O(u^4).

The first coefficient is unchanged by LEFT pair normalization, and the
second is the held all-n fair rule. The displayed exact formula for chi
has `[u^2] chi=-2v beta` and `chi|_(beta=0)=u^3/12+O(u^4)`. The
normalized source functions are analytic on the closed small `u,g`
domain after the genuine deterministic-coin factor `v` is divided out;
they are symmetric in `g` and `1-g`. Thus the entire order-`u^3`
coefficient of `(F-chi/10)/v` vanishes at `beta=0`, and

    |F_i-chi_i/10| <= C v_i*(beta_i*u_i^3+u_i^4).         (10)

This is an all-coin Taylor consequence, not a fitted coefficient for
particular parameters. Using (8)--(9) and
`sum r_i^2 <= (max u_i) sum r_i^2/u_i <= C H^2 h^4`,

    sum |F_i/d9_i-chi_i/10| <= C Hh^3.                    (11)

Also the EXACT jump correction in (7) satisfies

    sum |gamma_i-1| |b_i- - B_h|
      <= C sqrt[(sum r_i^2/u_i)*(sum u_i*(b_i-)^2)]
           + C |B_h| sum r_i
      <= C Hh^5+C Hh^4 <= C Hh^4.                         (12)

No step divides by `v` in a bound on an actual source.

## 3. Exact return integration and chronology

Let `a_i+tau_i` be the location of `C_i` on the nominal pair-time axis.
The signed physical charge in (1) is placed at `a_i`, BEFORE the same
bare cell. Both locations are within `[0,T]`. Since `tau_i<=u_i`, (9)
gives, for any `f` as above,

    sum |chi_i| |f(a_i+tau_i)-f(a_i)|
       <= C Hh^3 ||f'||_infinity.                           (13)

Thus moving a jump is paid for; it is not a silent shift of the physical
prefix. Integration by parts for the actual piecewise-smooth `b` gives,
with `f_i=f(a_i+tau_i)`,

    sum f_i F_i/d9_i
      = -int_0^T (f'+21f)b da + 21 B_h int_0^T f da
        -sum f_i (gamma_i-1)(b_i- - B_h).                 (14)

The boundary term is zero at BOTH ends by (6). Equations (11)--(14),
`210 B_h/h^2=2/9+O(h)`, Cauchy--Schwarz and (6) yield

    |int f d eta_h|
      <= 10 h^(-2) sqrt(E_b)*||f'+21f||_(L^2[0,T])
         + C Hh*(||f||_infinity+||f'||_infinity)
      <= C Hh*(||f||_infinity+||f'||_infinity).

The numerical constant absorbs the fixed maximal time and the error in
the known reference eigenvector. This proves (2) and hence (3); for the
latter `f(a)=a exp(-9a)` has uniformly bounded `C^1` norm.

## 4. The positive-kernel consequence

The reviewed earlier result is, with its actual signed endpoints and all
diagonal corrections retained,

    Z/h^4=exp(-T)*[3M_h+(27/4)E(eta_h)]
                       +O(Hh+H^(4/3)h^(2/3)),
    Z=-6P_bias+O(H^(4/3)h^(14/3)),  E(eta_h)>=0.

The `h^(2/3)` term uses the SEPARATE full-fibre PHYSICAL arm weakness
theorem for `max u_i`, not a false rare-coin consequence of source cost.
Substitute (3), move the two nonnegative terms to the same side, and use
the uniformly positive `exp(-T)`. This proves (4). The old exact weight
comparison `P_bias >= c^10 h^4 sum ell_i*y_i^2/(2 exp(H0))` and `L=H/4`
then prove (5).

The proof works on the complete actual return fibre. It does not turn a
generic signed profile satisfying four moments into a witness. Conversely,
the conclusion does not prove concentration of `u_i/h`, eliminate
zero-charge fair microscopic mass, establish an upper bound on the
calibrated source action, or determine the integer phase. Those remain
separate original-goal implications.

## Evidence and direct reuse

This is a hand argument from named held suppliers and the reviewed PSD
identity; no new code or external call was used for it. `SHA256SUMS.txt`
binds this note and exact supplier bytes. The independently scoped review
of the earlier matched/kernel argument is `../2026-10-31-codex-terra-g3-equal-rate-channel/REVIEW.md`;
that review does not by itself accept this new note. The immediate reuse is
the full-fibre all-source bound (5) at one fixed budget, with the original
four-rate abstract countercontrol retained at its smaller formal scope.
