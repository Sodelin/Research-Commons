# Goldbach exclusion debate: three proposals and a synthesis

This is an edited record of three independent arguments and a fourth synthesis. No new Goldbach theorem, novel priority claim, or VibeMath submission. The arithmetic checks and the exact proof scope are recorded below.

## 1. Sieve advocate: rule out total cancellation

For a fixed even target N, attack the case in which the long-divisor Möbius contribution cancels the positive term in the earlier [Huang–Li comparison](../second-pass/README.md). We need neither an exact pair count nor a zero mean for the shifted Möbius sequence. If 3 does not divide N, the progression p≡N mod 9 has asymptotic weighted prime mass N/6; all those leftovers have Möbius value zero. Everywhere else μ≤1. This gives an unconditional margin in the model main term.

**Why this over the others:** there is already an arithmetic source of slack, and it points at a concrete estimate for the actual sequence Λ(n)μ(N−n) in diagonal remainder classes. The circle route needs a signed cancellation bound at a specified phase; the rigidity route still needs an estimate to detect a single missing target.

**Best objection:** the missing estimate is not ordinary prime distribution, even if one grants Dirichlet GRH. The reflected partner sets the sign, which is close to the difficulty we set out to resolve. Good margin plus unproved transfer is still conditional.

## 2. Circle-method advocate: rule out a large negative error

For an even N in a bulk range, write the weighted pair count as a positive major-arc term M(N), plus a minor-arc term. It suffices to control only the negative direction, e.g. minor(N) ≥ −(1−δ)M(N) with fixed δ>0, leaving room to discard prime powers. If A+iB=e(−Nα/2)S(α), the real part of the minor integrand is A²−B². Keep that phase and the actual singular-series budget; don't reduce it to a global fourth moment or a universal minimum. See [Li–Liu's analysis](https://arxiv.org/html/2610.26756v1#S4).

**Why this over the others:** it attacks the exact target without a broad shifted Möbius theorem or a speculative claim that exceptions cluster. Split into bands and use absolute bounds only on the ones that already fit the budget.

**Best objection:** recentering changes the expression, not the strength of any known bound. Discarding its phase returns us to the same bad global estimate. No bandwise signed gain is proved here.

## 3. Local-deficit advocate: rule out a missing target hidden by neighbors

Choose shifts h with nonnegative weights w_h and w_0=1. If the weighted sum of prime-only pair counts is at least its predicted total minus A, and each neighbor's count is at most its own prediction plus u_h, then subtracting the other targets yields

    R(N) ≥ M(N) − A − sum_{h≠0} w_h u_h.

Thus A+sum w_h u_h < M(N) would force a pair without a full pointwise asymptotic. Compare [Grimmelt's short-interval tools](https://arxiv.org/abs/1910.05187), [Goldston–Suriajaya's averaged formula](https://arxiv.org/abs/2110.14250), and [Lichtman's upper bounds](https://arxiv.org/abs/2309.08522). These are tools to test, not assertions that their window, constants and weights already match.

**Why this over the others:** it tries to use existing average and upper-bound information rather than ask for a full shifted sign theorem or an immediate pointwise minor-arc breakthrough. It doesn't require exceptions to come in clusters.

**Best objection:** a single missing target loses only one main-term unit; neighbors can hide it. With H comparable, equally weighted neighbors, their average relative overshoot must be less than order 1/H before paying for the aggregate error. Known upper bounds losing a constant factor won't do. Our [synthetic isolated misses](../second-pass/README.md) explain why generic distribution can't supply the exact inequality. [Budget.lean](Budget.lean) checks the ledger inequality and a strictness example after integer scaling; it does not check any analytic premise.

## 4. Synthesis: partial exclusions that really fit together

**Stack genuine zero lanes, but count their overlap.** For a finite set S of odd primes not dividing N, μ(N−n)=0 if n≡N mod ell² for any ell in S. By CRT and the [prime number theorem in fixed progressions](https://kskedlaya.org/ant/chap-primes-in-ap.html), the union of those lanes has asymptotic Λ-mass

    N [1 − ∏_{ell∈S} (1 − 1/φ(ell²))] + o(N).

Each lane selects exactly one reduced residue mod ell²; at the product modulus the choices are independent in the uniform residue count. The finite family of target residues gives uniformity for fixed S. This implies an upper bound for the full shifted Möbius sum of N minus that mass.

For the starter progression 192 mod 210, 3 divides the target so the mod-9 lane isn't a reduced prime class. But 5 and 7 do not divide it. The corresponding mod-25 and mod-49 lanes each work on the **entire** progression, and they cost 42 and 20 out of 840 reduced classes mod 1225, with one shared class. The joint margin in the shifted total is therefore **(61/840+o(1))N**, not 62/840. The finite replay checks all 35 relevant target classes mod 1225. This gets a sharper, uniform arithmetic margin; it still does not prove the shifted distribution estimate.

**Complementarity with the circle method is real but conditional.** At an odd prime ell, the square-divisibility lane supplies a positive margin when ell doesn't divide N. When ell does divide N, that lane no longer supplies fixed positive prime mass, but the classical Goldbach singular-series factor increases by (ell−1)/(ell−2) relative to the nondivisibility case. For ell=3 that factor is 2; see the singular series normalization in [Li–Liu §1](https://arxiv.org/html/2606.05224v2). So a possible split is sieve on even targets not divisible by 3 and circle on the multiples of 3, with the latter allowed to spend its larger main-term budget. A successful proof needs uniform estimates on both pieces, or an arithmetic rule excluding the **intersection** of their failure sets. Separate small exceptional-set bounds alone do not do that. Do not add sieve and circle margins as if they were parts of a single identity.

**Priority:** pursue the square-lane sieve input first. It has a guaranteed margin and a precise remaining estimate. Use the circle ledger as a distinct alternative for target families where that margin is weaker, and use the local-deficit idea as a quantitative challenge to candidate window bounds, not as an assumption about exceptions. This is a change of intermediate goal, not abandonment of the Goldbach finish line.

The RH parallel is methodological: identify the weakest one-sided bound that still gives the conclusion. Our separate [RH reading notes](https://github.com/Sodelin/Research-Commons/tree/main/research/2026-11-23-rh-proof-reading) study other extensions. They are not ingredients of this calculation; no theorem from their proposed RH extensions is assumed here.

## Reproduce the checks

Run `python3 -B replay.py | diff -u REPLAY.txt -`. Check the finite budget in Lean 4.33.1 with `lean --trust=0 -o Budget.olean Budget.lean`. [Lean receipt](LEAN-REPLAY.txt).
