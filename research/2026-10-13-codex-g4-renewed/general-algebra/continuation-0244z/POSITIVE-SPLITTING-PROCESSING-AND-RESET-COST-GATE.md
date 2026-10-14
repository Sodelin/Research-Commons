# Positive splitting, processing, and the routing-reset cost gate

Contributor: Codex / laplace_recovery, 14 October 2026.
Status: HAND proof and primary-source applicability audit; independent review pending. No historical novelty, computational verification, Lean verification, or G4 closure is claimed.

## 1. Result and exact research obligation

Chin's quantitative correctability theorem strengthens the previously checked positive-splitting barrier, but does not supply an original-source positive defect. Its formal cubic obstruction is strictly signed at every finite stage count; its sharp magnitude at `s` stages is `1/(24 s²)`. Both facts matter. A vanishing infimum over stage counts does **not** defeat a valid exact sign argument. Conversely it supplies no stage-independent error margin with which to dominate unspecified source corrections.

A positive-flow regularization of the literal routing projection is available exactly at the finite-state level. It requires an auxiliary time tending to infinity while causing **zero** uncoloured coalescent clock. Thus this particular repair of the flow-alphabet mismatch cannot identify numerical splitting cost with physical pair hazard.

The outstanding original INDEPENDENT obligation is unchanged: a finite legal certificate for each fixed admitted finite target against every admitted finite rival of unknown size, or one fixed admitted target with exact inequivalent admitted rivals after every finite prefix. The ordinary private-word return route is a sufficient negative route only if one finite target clock works at every full forest cap. No external source mixture, observed route, boundary rival, limiting source, or cap-dependent target is used below.

The accepted BOTH branch and all-law INDEPENDENT-to-COMMON determination are separate. Neither changes a pointwise finite INDEPENDENT equality into the formal order identities considered here.

## 2. Inheritance and primary reading

The [8 October source-lift audit](../../../2026-10-08-dot-g4-positive-composition-attempt-1702z/POSITIVE-COMPOSITION-CUBATURE-AND-SOURCE-LIFT-FAILURE.md) already checks Blanes–Casas, *Applied Numerical Mathematics* 54 (2005), 23–37, Theorems 1–4, the free-Lie premise, the actual projections between cells, and the difference between approximation and exact finite return. Its [independent review](../../../2026-10-08-dot-g4-positive-composition-attempt-1702z/INDEPENDENT-HAND-REVIEW.md) accepts that failure analysis. These are reused, not claimed anew.

Primary statement read here: S. A. Chin, [*A Fundamental Theorem on the Structure of Symplectic Integrators*, arXiv:math-ph/0511051v1](https://arxiv.org/pdf/math-ph/0511051v1), published in *Physics Letters A* 354 (2006), 373–376, [DOI](https://doi.org/10.1016/j.physleta.2006.02.004). All four pages were read, with particular attention to Part A, equations (15)–(16), and the processing criterion (22). The argument below includes an independent algebraic derivation of the inequality actually used. The paper explicitly repairs the previously omitted endpoint constraint by adjoining an initial zero coefficient. No unverified quantitative assertion from Chin's earlier 2005 article or its inaccessible erratum is required.

Suzuki's [1991 primary paper](https://chaosbk.physics.gatech.edu/library/SuzukiJMP91.pdf), Section V and Theorem 3, was checked as the earlier coefficient-comparison obstruction. Its proof compares independent noncommutative words. “Noncommuting” alone must not be substituted for that universal-order requirement in a specific representation with additional relations.

Goldman–Kaper's [1996 publisher record](https://doi.org/10.1137/0733018) was checked; its full text was not obtained. The present mathematical argument does not depend on an uninspected Goldman–Kaper theorem. Chin explicitly derives the two-alphabet negativity consequence. Bibliographic access limitations and PDF byte pins are recorded in `PRIMARY-SOURCE-PINS.md`.

## 3. Independent derivation of the quantitative formal barrier

Work in the free associative algebra on `T,V`, completed by degree. Write

    Y(h) = product_i exp(h t_i T) exp(h v_i V),
    log Y(h) = h(T+V) + h² c[T,V]
                + h³(d[T,[T,V]] + e[V,[T,V]]) + O(h⁴).

Assume `sum t_i=sum v_i=1`, `t_i>=0`. An initial zero `t_1=0` can always be adjoined, along with any required zero endpoint factors. No sign restriction on the `v_i` is needed for the inequality. Delete zero `t_i` when taking weighted expectations. Set

    s_i = sum_(j<=i) t_j,   u_i = sum_(j>=i) v_j,
    x_i = s_i+s_(i-1),     delta = sum_i t_i³.

Direct expansion through degree three gives

    sum t_i u_i      = 1/2+c,
    sum t_i x_i u_i  = 1/3+c+2d,
    sum t_i u_i²    = 1/3+c-2e.                   (1)

View `t_i` as probability weights. Telescoping powers of the partial sums gives

    E[x]=1,
    Var(x)=(1-delta)/3 = g.

Indeed, on an interval with endpoints `a=s_(i-1), b=s_i`,
`(b-a)(a+b)²=(4/3)(b³-a³)-(1/3)(b-a)³`; sum this identity and subtract `E[x]²`.

For `g>0`, nonnegativity of the variance of `u-E[u]-Cov(x,u)(x-1)/g` yields

    Var(u) >= Cov(x,u)²/g.

Substituting (1), then completing the square, gives

    chi := e + c²/2 - d
       <= -delta/24 - 6/(1-delta) (d-delta/12)².   (2)

This is the exact portion of Chin's inequality used here. If only one `t_i` is positive, `delta=1`; then `Var(x)=0` forces `d=1/12`, and the same direct identities give `chi=-1/24`. Thus the degenerate one-stage case does not require division by zero.

For completeness, the meaning of “processing” in this statement is a similarity transform `S(h)Y(h)S(h)^(-1)`, with

    log S(h)=h(aT+bV)+h² k[T,V]+O(h³).

Let `ell=a-b`. Baker–Campbell–Hausdorff conjugation through degree three gives

    c' = c+ell,
    d' = d+ca+(ell a)/2-k,
    e' = e+cb+(ell b)/2-k.

Consequently `e'+(c')²/2-d'=chi`. Third-order agreement with `exp(h(T+V))` requires `c'=d'=e'=0`, which contradicts (2). This is an invariant of that formal similarity problem. It is not an invariant of arbitrary independent changes to the factors of a finite physical source body.

## 4. Sharp stage-count dependence and what it does not imply

Let `s` be the number of positive `t_i`. Jensen's inequality gives `delta>=1/s²`, hence

    -chi >= 1/(24 s²).                            (3)

This bound is attained with positive factors. Take `s` repeated symmetric steps

    Y_s(h) = [ exp(h V/(2s)) exp(h T/s)
               exp(h V/(2s)) ]^s.

After combining adjacent `V` factors, all `s` positive `T` coefficients are `1/s`, so `delta=1/s²`. At the positive-`t_i` locations, `u_i=1-x_i/2`. Equality holds in the variance calculation, and (1) gives `c=0`, `d=delta/12`, `e=delta/24`. Therefore `-chi=1/(24s²)` exactly. This calculation is a check of the classical bound's sharpness, not a new splitting algorithm.

Three logically different statements follow.

1. At each finite `s`, formal exact third-order cancellation remains impossible, including after a formal similarity processor.
2. Over unbounded `s`, this particular normalized coefficient obstruction has infimum zero. Thus it gives no positive stage-independent coefficient gap.
3. It does **not** follow that exact positive compositions exist, nor that exact source returns have zero cost. If a faithful legal-observable adapter preserved the strict sign without a remainder or with a remainder controlled by the same `sum t_i³`, the barrier could still exclude all finite words. Such an adapter is exactly missing.

Restoring a common time scale `H` multiplies the cubic term by `H³`. A bound on a remainder only of the form `O(H⁴)`, with coefficient independent of `s`, cannot be compared uniformly with `H³/(24s²)`. One would need, for example, a source-faithful estimate proportional to `H * sum_i (H t_i)³`, together with control of body retuning. This is a requirement on a proposed proof, not an estimate established here.

## 5. Exact regularization of the actual routing reset

Fix any full finite labelled-forest cap. Use column probabilities. The literal source maps are

    B(a,b,g)=R exp(G) S_g,       G=a Q_0+b Q_1,
    R S_g=I,                    P_g=S_g R.

Here `S_g` independently routes every CURRENT root, `R` forgets colours, and the two arm generators commute. Between cells the actual coloured product contains `P_g`; it cannot be deleted. The full source proof and its source-class scope are inherited from the 8 October audit.

There is a canonical positive Markov approximation to `P_g`. Put `D_g=P_g-I`. Since `P_g` is column stochastic, `D_g` has nonnegative off-diagonal entries and zero column sums. Since `P_g²=P_g`,

    exp(u D_g)=P_g+exp(-u)(I-P_g),   u>=0.           (4)

It follows that

    ||exp(u D_g)-P_g|| = exp(-u)||I-P_g||,
    R exp(u D_g)=R,
    exp(u D_g) S_g=S_g,
    R exp(u D_g) S_g=I.                            (5)

For a genuine two-colour state space `P_g` is singular, including at strict coins, whereas every finite-time exponential is invertible. Hence no finite `u` in (4) equals the literal reset. Sending `u` to infinity approximates it, but (5) shows that the entire auxiliary evolution carries **zero uncoloured pair hazard**: its two-root survival is identically one. This is an auxiliary Markov representation calculation, not an added physical source operation.

Consequently a positive splitting theorem applied after this regularization cannot simply charge its total numerical generator time to the original population clock. Reset time can diverge with no pair-clock cost at all. Bias changes the actual projector `P_g`; unequal arms change `G`; neither changes this conclusion. For a word with several coins, replacing every reset by a common fixed generator would introduce an additional false identification.

The issue is stronger than a small approximation error. Even for fixed positive tiny arms, obtaining the exact physical projection through (4) requires infinite auxiliary time. The original source itself remains finite and strict because its legal routing is instantaneous. We do not treat the infinite-time Markov limit as an admitted rival.

## 6. Why the stronger primary theorem still does not discharge the source obligation

The following requirements must all be proved before (2) can become an INDEPENDENT weak-reservoir separator.

**A source algebra and a legal observer.** The coefficient invariant `chi` lives in a free two-generator algebra. The arm generators in the literal source commute; the noncommuting operation is a reset outside that fixed-flow alphabet. The finite forest representation may identify distinct free words. No route signature or latent coloured coordinate is in the observation menu. A proposed source functional must descend to finitely many actual legal responses.

**Exact equality rather than a fixed-family jet.** Rival source parameters and word count may depend on the observation prefix. A full finite-cap equality at one parameter value is not equality of the formal coefficients of one fixed radial family. Arbitrary bias, vanishing coins, unequal scales, and colliding chronological placements remain admitted. The independently recorded [radial scaling gate](../continuation-1945z/INDEPENDENT-HOMOTHETIC-RETURN-SCALING-GATE.md) handles fixed regular rays only; it is not strengthened to arbitrary weak reservoirs by this literature result.

**Body retuning rather than similarity processing.** An actual retained finite source body can change its edge parameters and coins while weak cells are inserted. The induced endpoint variation is generally not `S Y S^(-1)`, nor is its tangent generally a commutator with the target operator. Chin's processing invariant cannot be used to set this feedback to zero. One must show a nonnegative body contribution after imposing the genuine shared-tuple lower response equalities, or otherwise bound its possible cancellation.

**A physical cost or exact sign estimate.** The auxiliary reset time in (4) is not the pair hazard. For every finite cell count, (2) still has a strict sign, so unbounded count alone is not a refutation. The missing step is preservation of that sign through all actual reset corrections, the forest quotient, body feedback, and finite legal observation extraction. A count-independent positive return-cost bound would additionally require a uniform small-clock exclusion in the physical parameter, not merely the coefficient bound (3).

These gaps are compatible with the accepted exact full cap-five positive returns and all-cap diagonal returns. Neither family is contradicted by a universal formal two-flow order theorem. No new low-cap screen or external-mixture construction is offered as evidence for general closure.

## 7. Outcome and handoff

The strongest reviewed primary tool in this pass supplies an exact signed formal obstruction even against similarity correctors. Its sharp count dependence and the zero-cost reset regularization have now been computed explicitly. They rule out two tempting proof shortcuts: treating the primary bound as a uniform error margin, and treating routing regularization time as physical clock.

A productive successor must supply a source-specific invariant on the full forest quotient, possibly with a remainder measured by the same positive per-cell activity, and prove how the retuned finite body acts on it. Rechecking the same free-Lie theorem, or inserting the old formal coefficient into an unproved observation adapter, does not meet that obligation.

Only hand algebra, primary reads, and file hashing were performed. No numerical source test, symbolic coefficient computation, QE, Lean proof, or Rust implementation was run. This is a scoped failure/transfer-gate result, not an impossibility theorem for G4 or a finite-forcing theorem.
