# Four actual cap5 chronology constraints and a microscopic limit gate

Contributor: Codex Terra, 31 October 2026 UTC. The necessary limit equations
and abstract countercontrol below are hand-derived from the pinned prior
sources. Their polynomial changes of variables were checked exactly as
recorded at the end. Independent review and formal verification of this
integration are pending. The countercontrol is NOT a fully commuting word,
an admitted source limit, a counterexample to AG-Pair, or a G3 solution.

## 1. Full-fibre statement and actual source chronology

Fix one sufficiently small allowed `H=(log 2)/m>0` and put

    L=H/4, T=3H/4, c=exp(-H), h=-log t.

Use one actual finite strict equal-arm word with arbitrary natural coins,
ordinary gaps and length, BOTH exact paired clocks, and complete forest
commutation with the existing fixed `S(t)` through cap12. For each actual
bigon put

    u_i=-log q_i, beta_i=(2g_i-1)^2, v_i=g_i(1-g_i),
    ell_i=log[(q_i+2v_i(1-q_i))/q_i],
    z_i=u_i/h, y_i=beta_i*u_i/h^2.

The same source and paired clocks give `sum ell_i=L`. Let `a_i` be MINUS
the log of the actual independent two-root diagonal product of EVERY factor
strictly preceding this cell. In particular ordinary gaps and all preceding
bigons are included, and `0<=a_i<=T`. Define the probability measure

    mu_h = sum_i (ell_i/L) delta_(a_i,z_i,y_i).             (1)

For each fixed `lambda` in `{5,7,9,10}`, the full fibre satisfies

    integral exp(-lambda*a) (z^2-6y) dmu_h
      = 4*(1-exp(-lambda*T))/(lambda*T) + O_H(h).            (2)

The constants are uniform in the actual word length, chronology, and all
strict coins. The four rates use different ACTUAL cap4/cap5 prefix and
suffix weights; they are not four copies of one freely reweighted source.
The rate5 equation extends the earlier chronological-gap result by
identifying its endpoint limit and its position coordinate. Rates7,9,10
are the additional uses of the already derived three cap5 source channels.

The inherited source cost also gives the single combined moment estimate

    integral (z^4+y*z^2+y^2) dmu_h <= B0,                  (3)
    B0=8*exp(H0)*C0,

where `H0,C0` are the fixed constants in the cited cost theorem. Thus
the measures are tight, and every weak subsequential limit of (1), with H
fixed and h tending to zero, obeys all four equations (2) without the error.
Here `z^2` and `y` are uniformly integrable by (3). No assertion is made
that an arbitrary measure satisfying these conditions is source-realizable.

## 2. Why the four necessary equations hold

Use the already published all-source cost and positive-charge balance:

    sum v_i*(beta_i^2*u_i^3+beta_i*u_i^4+u_i^5) <= C0*H*h^4,
    sum v_i*beta_i*u_i^2 <= C_H*sum v_i*u_i^3.

Since `sum v_i*u_i<=H/4`, Cauchy--Schwarz gives, uniformly,

    sum v_i*u_i^3 = O_H(H*h^2),
    sum v_i*beta_i*u_i^2 = O_H(H*h^2),
    sum v_i*(beta_i*u_i^3+u_i^4) = O_H(H*h^3).             (4)

For any fixed root count r, write `lambda_r=binom(r,2)` and `b_r` for
the actual source's no-merger diagonal. The existing same-source diagonal
estimate, also obtained by the variance of the same-colour pair indicators,
is uniformly

    |log b_r(B_i)-lambda_r log b_2(B_i)|
       <= C_r*v_i*(beta_i*u_i^2+u_i^3).                     (5)

Ordinary factors give zero in (5). Taking absolute sums over any prefix OR
suffix and applying (4) proves a uniform `O_H(H h^2)` bound for its total
log-diagonal deviation. In particular the actual UNKNOWN endpoint diagonals
are not set equal to reference powers; instead the clocks and (5) imply

    k_r=b_r(K)=exp(-lambda_r*T)*(1+O_H(H h^2)).             (6)

The exact cap4 source and the previously checked cap5 source are

    chi_i=(v_i/3)*(1-q_i)^2*((1-q_i)-(5+q_i)*beta_i),
    A5_i=a(q_i)*chi_i-D5_i,
    a(q)=3q(q^2+3q+1)/10,
    D5_i=q_i*v_i*beta_i*(q_i+1)*(1-q_i)^4/5 >=0.

The same sums give

    sum |chi_i|=O_H(H h^2),  sum u_i|chi_i|=O_H(H h^3),
    sum D5_i=O_H(H h^4),
    sum |A5_i-(3/2)chi_i|=O_H(H h^3).                      (7)

For example, the first `u|chi|` term follows from
`sum v beta u^3 <= (sum v beta^2 u^3)^(1/2)
                    (sum v u^3)^(1/2)`;
the second uses `sum v u^4 <= (sum v u^3)^(1/2)(sum v u^5)^(1/2)`.
No lower bound on v or on an individual u is used.

The reviewed gap expansion says, after dividing the original common v
factor rather than taking a rare-coin inverse,

    chi_i/(ell_i h^2)=(z_i^2-6y_i)/6
                       +O_H(u_i*(z_i^2+y_i)).               (8)

The integral of the error is O_H(h), using (3) and Holder. For each
`r=1,2,3`, the exact cap5 equation has its own chronological weight

    W_(5,r),i=(product before B_i b5)*(product after B_i b_r),
    sum W_(5,r),i A5_i
      = t^10*b(t)^lambda_r * (k_r-k5)/(s_r-s5) * A5_*,    (9)

where `s_r=b_r(S)`, `A5_*` is the actual fair bare reference source,
and `k1=s1=1`. With `(10,lambda_r)=(10,0),(10,1),(10,3)`, respectively,
the limiting rates are 10,9,7. The cap4 charge equation analogously uses
`W_(4,2)` and rate `6-1=5`.

It is important that a current cell is omitted from both its prefix and
suffix. If `tau_i=-log b2(B_i)`, then its suffix pair-time is
`T-a_i-tau_i`, not `T-a_i`. Equation (5) gives, for the ACTUAL weight,

    W_(5,r),i = exp[-lambda_r*T-(10-lambda_r)*a_i]
                 *exp(lambda_r*tau_i)*(1+O_H(H h^2)).       (10)

Here `0<tau_i<=u_i`. Replacing the extra factor by 1 is justified only
after summing the signed sources, since (7) controls
`sum u_i|chi_i|`; it is not a uniform unweighted assertion about cells.
The same treatment applies to `W_(4,2)`.

The fixed reference has

    s_r=1-3*lambda_r*h+O(h^2),
    chi_*=(2/3)h^3+O(h^4),  A5_*=h^3+O(h^4).

Insert (6)--(8) into (9) and its cap4 counterpart, retaining the actual
reference prefactors. After dividing by `L h^2`, each source equation is
exactly (2) up to `O_H(h)`. The cost bound (3) follows from
`ell_i<=2 exp(H0) v_i u_i` and the first displayed cost inequality.

## 3. An exact bounded leading-profile countercontrol

The four constraints (2), the quantitative moment bound (3), BOTH limiting
clock budgets and the two FORMAL leading normal tests do not alone imply
that microscopic biased mass vanishes. The following is an abstract
measure-level countercontrol. It is not claimed to be a weak limit of
complete-commuting words.

Reuse the exact scaled source polynomials from the saved three-outlier
proof, with its corrected cap10 sign:

    f4(X,Y)=X^2(X-1)[2X^3-24X^2Y-X^2+24XY^2+6XY-X+6Y],
    f5(X,Y)=X^2[5X^6-80X^5Y+140X^4Y^2-25X^4-48X^3Y^3
                 +300X^3Y+25X^3-300X^2Y^2-250X^2Y
                 +200XY^2-5X+30Y].                          (11)

For `z>0`, put `X=z/2`, `Y=y/(2z)` and define the gap-normalized leading
functions

    G4(z,y)=2 f4(X,Y)/X,  G5(z,y)=2 f5(X,Y)/X.             (12)

These extend polynomially to z=0, and the independently checked singular
microscopic scaling gives the SAME boundary values

    G4(0,y)=-3y(y+1),  G5(0,y)=5y(5y+3).                   (13)

The original normal equations have distinct limiting weights

    W4(a)=exp(-6T-22a),  W5(a)=exp(-10T-35a).               (14)

For the bounded measures constructed BELOW, the formal tests
`integral W4 G4 dmu=integral W5 G5 dmu=0` are ordinary finite polynomial
integrals. For an arbitrary full-fibre sequence, the moment bound (3)
does NOT alone justify taking these higher-degree normal limits: their
tails and uniform integrability require separate control. We do not assume
that missing limit passage.

Let the EXISTING root `(A0,X0,Y0)` be the actual real root in the saved
rational interval box for

    G1=2A^3+X^3-6YX^2-2A-X,
    G2=2 f4(A,0)+f4(X,Y),
    G3=2 f5(A,0)+f5(X,Y).                                  (15)

That exact saved contraction certificate proves a nonsingular Jacobian;
we do not regenerate the bank or find a new root. Its three coordinates
are strictly positive. For any nearby `(A,X,Y)`, set `M=2A+X` and define
the *gap-normalized* comparable-scale law

    nu_(A,X,Y) = (2A/M) delta_(2A,0)
                    +(X/M) delta_(2X,4XY).                  (16)

The non-obvious weights are `2A:X`, because there are two fair cells of
gap asymptotic to `epsilon*A/2` and one biased cell of gap asymptotic to
`epsilon*X/2`. Direct substitution in (11)--(12) yields EXACTLY

    M*E_nu[z^2-6y-4] = 4 G1,
    M*E_nu[G4]        = 2 G2,
    M*E_nu[G5]        = 2 G3.                              (17)

At the saved root all three expectations vanish. Now fix ANY `M_dust>0`
and choose a dust point `z=0,y=y0=M_dust`. For sufficiently small
`alpha>0`, the implicit-function theorem and the nonsingular saved
Jacobian give nearby positive A,X,Y such that

    nu_alpha=(1-alpha)nu_(A,X,Y)+alpha delta_(0,y0)

still has the three expectations in (17) equal to zero. Its Jacobian is
the old Jacobian multiplied by the invertible diagonal row scaling
`diag(4,2,2)/M`; the dust merely contributes a continuous perturbation.
There is no new outlier root search or physical word construction here.

Make the chronology independent and uniform, with

    mu_alpha=(da/T on [0,T]) tensor nu_alpha.

It satisfies all four tests (2) exactly, because the charge expectation is
4, and both bounded formal normal tests in (14) exactly, because each
corresponding G expectation is zero. Yet its `z=0` atom has strictly
positive `y^2` mass `alpha*y0^2`.

The quantitative bound (3) can also be retained. Every true reference
power `S(t)^N`, with `h=H/(4N)`, has
`sum v_i u_i^5/(H h^4)->2`; hence `C0>=2` and
`B0>=16 exp(H0)>16`. The reference law

    mu_ref=(da/T) tensor delta_(2,0)

has the same four charge tests, both formal normal tests, and cost exactly
16. Mix `mu_alpha` with `mu_ref` using a sufficiently small but strictly
positive mixing weight theta. All six tests remain exactly satisfied, its
finite moment (3) is at most B0, and its microscopic `y^2` mass is
`theta*alpha*y0^2>0`. It also satisfies the inherited positive z-second-
moment lower bound, since the charge expectation gives `E z^2>=4`.

This abstract choice is consistent with the two leading clock budgets:
choose the microscopic coin `beta=1/2` and arm duration
`u~2*y0*h^2`, giving `U=(1-q)/epsilon^2->y0/2<M_dust` and
independent-pair-time/gap ratio tending to 3. Comparable and reference
cells have ratio tending to 1. Since `T=3L`, the averaged cell pair time
is `(1+2 theta alpha)L<3L`; positive ordinary time fills the remainder.
This is clock ACCOUNTING ONLY. It is not a construction of an actual
sequence obeying all equations, the original quantifiers, or source energy.

## 4. The signed term that remains

On the bounded abstract measure, the formal combined receiver is

    D(a,z,y)=W5(a)G5(z,y)+5*c^17 W4(a)G4(z,y).

Its total integral vanishes by the two formal tests. At `z=0` the true
weight ratio `W5/W4=exp(-4T-13a)` is at least `c^17` on `[0,T]`, so the
microscopic contribution is strictly positive; the complementary source
contribution is consequently strictly negative. Thus the actual needed
full-fibre implication is, for each fixed `M_dust>0`, a bound such as

    liminf_(h->0) [1/L] sum_(U_i>M_dust) ell_i D_i >= 0,     (18)

uniformly over the ACTUAL finite strict paired cap12-commuting fibre at
fixed H. Here `D_i` and the different actual `W4_i,W5_i` are exactly those
in `MICROSCOPIC-BIASED-DUST-RECEIVER.md`. A power-rate version, with a
fixed positive exponent and constants independent of the word, supplies a
corresponding microscopic-cost rate; the existing two-sided receiver
comparison gives the converse with the recorded square-root exponent loss.
The formal countercontrol proves that (18) cannot be inferred just from
(2), (3), clock accounting and the two bounded leading normal tests.
Additional complete-band, nonlinear/prefix, higher-order, or
return-conditioned source information is necessary for that route.

## 5. Source custody and checks

The three cap5 endpoint formulas and source factor are in the hash-bound
`../2026-10-31-codex-terra-g3-cap5-spectral-audit/PROOF-AND-OVERLAP.md`
and `EXACT-COUPLED-CHARGE.v2.md`. The original cost, cap4 charge and
chronological gap expansion are named in
`../2026-10-31-codex-terra-g3-general-closure/REFERENCE-SCALE-GAP-BUDGET.md`
and `CHRONOLOGICAL-GAP-LIMIT.md`. The saved root/normal limits are in
`CAP4-AND-TWO-NORMALS-OUTLIER.md`, with the original checked root/log and
the separately pinned archive SHA `baafd3589c9d2aab0f7c7a0e0d1b00a0f4bf0a2a61267804f3a3976b26ba2ad6`.
The singular microscopic receiver is the reviewed
`MICROSCOPIC-BIASED-DUST-RECEIVER.md` and its review.

`check_profile_algebra.py` checks (12), (13), (17), the reference normal
zeros, the four scalar endpoint coefficients and the reference cost ratio
by exact symbolic arithmetic using ONLY the displayed saved polynomials;
its direct process exited 0 and output is in its log. No source bank,
parameter grid, new outlier, solver, Lean or external service was run. The
endpoint transport, clock accounting, IFT perturbation and source-cost/
quantifier implications above are hand mathematics, not claims of
independent review or machine-verified proof.
