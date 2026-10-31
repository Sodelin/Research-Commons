# A positive two-normal receiver for microscopic biased source mass

Contributors: main G4/general-closure lane (Codex/OpenAI), which proposed the boundary combination; G3 general-closure lane (Codex/OpenAI), which checked the singular fixed-coin scaling and actual transport bound. 31 October 2026 UTC. **Hand-derived conditional source estimate with exact symbolic coefficient checks; not independently reviewed or Lean formalized.** The estimate is positive only on a specified microscopic region, and is not an AG-Pair or original G3 solution.

## Statement on the original fibre

Retain the actual strict equal-arm paired fibre and complete forest commutation through cap10 from `REFERENCE-SCALE-GAP-BUDGET.md`. Use the reviewed actual cap8 and cap10 whole-word normal source polynomials f4,f5, with corrected f5 orientation and constants C4=275625/176 and C5=4254271875/4. Write

    x=t/(2-t), epsilon=1-x, h=-log t,
    U_i=(1-q_i)/epsilon², beta_i=(2g_i-1)²,
    y_i=beta_i(-log q_i)/h², ell_i=log[b2I(B_i)/q_i].

Fix ANY finite M>0 and let D_M={i:U_i<=M}. The actual two normal equations are

    sum_i W4_i f4(q_i,beta_i;x)=0,
    sum_i W5_i f5(q_i,beta_i;x)=0,                          (1)

with the original DIFFERENT source-specific chronological weights. Define

    G4_i=f4(q_i,beta_i;x)/(C4 epsilon^5 ell_i),
    G5_i=f5(q_i,beta_i;x)/(C5 epsilon^7 ell_i),
    D_i=W5_i G5_i+5 c^17 W4_i G4_i.                         (2)

There is C_M independent of count, chronology, h and coin such that, for every i in D_M and all sufficiently small epsilon,

    D_i >= 10 c^45 y_i²-C_M epsilon.                        (3)

Using sum ell_i=H/4=:L and the EXACT equations (1),

    10 c^45 sum_(i in D_M) ell_i y_i²
       <= -sum_(i not in D_M) ell_i D_i + C_M epsilon L.    (4)

This is an explicit positive source-cost term for biased microscopic cells. It retains arbitrary interior coins, including those tending to endpoints, and does not identify W4 with W5. Equation (4) also shows the obstruction: contributions outside D_M may be negative and are not controlled by this theorem. It does not prove dust vanishes, bound the complete right side, establish an integer phase or admit an arbitrary limiting source.

## Verified singular-scale source formulas

The pinned packet and its source banks are identified by SHA-256 in `TWO-NORMAL-PAIRED-OUTLIER.md`. `check_dust_scaling.py` reads those exact banks and checks the following identities over Q, with x=1-epsilon, q=1-epsilon² U and beta=b held fixed:

    f4/C4 = 6 epsilon^7 U² b(b-1)(4Ub+1)+O(epsilon^8),
    f5/C5 =-10 epsilon^9 U² b(b-1)(20Ub+3)+O(epsilon^10).  (5)

All lower powers vanish identically. The script also checks that EVERY source polynomial used by the two normals has the factors (1-beta)(1-q)². This matters at rare original coins and at U=0: after dividing those factors, the remaining expressions are finite polynomials, so the remainders in (5), in the corresponding factored form, are uniformly bounded on any compact 0<=U<=M, 0<=b<=1. This is a direct singular-scale expansion of the original polynomials, not an unjustified substitution of unbounded beta/epsilon into a fixed-scaled-coin remainder.

The exact physical gap satisfies, uniformly on the same compact set,

    ell=(1-b)U epsilon²/2 * [1+O_M(epsilon²)],
    y=4Ub+O_M(epsilon).

The first ratio is extended continuously at U=0 and b=1; actual strict cells have ell>0. Therefore the SAME two source polynomials satisfy the uniform gap-normalized limits

    G4=-3y(y+1)+O_M(epsilon),
    G5= 5y(5y+3)+O_M(epsilon).                              (6)

In particular the unweighted limiting combination G5+5G4=10y². The next step is needed because the actual weights in (1) differ.

## Actual chronological transport comparison

For an ordinary population with COMMON pair survival q, the ratio b_r/b_s for r>s is exactly q^(lambda_r-lambda_s). The same lower bound holds for an actual equal-arm independent bigon: couple its r CURRENT-root coin choices with those of a selected s-root subset. The extra within-arm pair hazard is between zero and lambda_r-lambda_s for every routing, and the two arms have the same physical duration. Thus, factor by factor,

    q^(lambda_r-lambda_s) <= b_r/b_s <= 1.

Apply this with (r,s)=(10,8) BEFORE a given cell and (5,4) AFTER it. Their differences are 17 and 4, respectively. The total COMMON survival over every other factor is at least c, so

    c^17 <= W5_i/W4_i <= 1,       W4_i>=c^28.               (7)

The second inequality uses b8>=q^28 before and b4>=q^6>=q^28 after, with all actual gaps retained. Both bounds are uniform in count and are valid for every source cell; no statistical independence across cells is invented.

Set r_i=W5_i/W4_i. Substituting (6) into (2) yields on D_M

    D_i=W4_i[(25r_i-15c^17)y_i²+15(r_i-c^17)y_i]
          +O_M(epsilon)
       >=10 c^17 W4_i y_i²-O_M(epsilon)
       >=10 c^45 y_i²-O_M(epsilon).

The coefficient 5c^17 is fixed for the entire source and depends only on the already fixed input c; no source-location-dependent observation is introduced. Summing with the true ell weights gives the dust estimate. Since each whole-word normal sum is exactly zero, the sum of ell_i D_i over ALL cells is exactly zero, proving (4).

## Review boundary and the remaining joint step

The source-polynomial coefficients and endpoint factors are exact machine-checked algebra, the transport inequality is a hand coupling argument, and the final bound is a hand consequence. `check_dust_scaling.log` records the actual check. The result remains conditional on the previously reviewed complete mixed-path/source identities and has no independent review or Lean receipt.

One sufficient next theorem would bound the complement's signed total from below by -o(1)L on the complete commutator fibre. Equation (4) would then force the microscopic gap-weighted y² contribution to vanish. A quantitative power bound on that complement would give the corresponding rate. Nothing here establishes that hypothesis: the exact cap4-commuting, two-normal outlier family in `CAP4-AND-TWO-NORMALS-OUTLIER.md` demonstrates that the larger-scale terms can cancel the two normals, although that particular word fails cap5. The full original problem still needs the hybrid scalar/prefix terms, other full-fibre equations or a different valid recognition/impossibility argument.

## The complement is genuinely signed

One cannot prove the missing complement bound by claiming D_i>=0 for every strict source cell. The pinned scaled polynomial check in `check_dust_scaling.py` gives an explicit actual comparable-scale curve:

    q=x=1-epsilon,  beta=epsilon,
    lim f4/(C4 epsilon^6)=0,
    lim f5/(C5 epsilon^8)=-8.

The actual pair gap on that curve is exactly ell=log(1+epsilon/2). Thus G4=O(epsilon) and G5=-16+O(epsilon). The actual complete-word weights satisfy W5>=c^45, and hence D_i=-16 W5_i+O(epsilon)<0 for all sufficiently small epsilon at fixed c. Its coin g=(1+sqrt(epsilon))/2 and both equal arm survivals are strict. The curve lies outside D_M for every fixed M as epsilon decreases. This uses the same definition of D_i and actual positive weights as (3), with no independent source coordinates.

It can occur in a word with both paired clocks exact: for each large N choose epsilon from N h+ell=H/4 and append this cell to S(t)^N, followed by an ordinary duration r=4ell-(-log x)>0. Its existence does not establish either normal equation or full commutation. The observation only rules out a sourcewise nonnegative extension of this same combined receiver; a joint-fibre cancellation bound remains possible.
