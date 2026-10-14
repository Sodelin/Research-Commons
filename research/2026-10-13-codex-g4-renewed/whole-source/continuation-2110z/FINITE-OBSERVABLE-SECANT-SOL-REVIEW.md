# Independent review: finite observable secant reduction

Reviewer: Codex delegated sol_interpolation_check agent.
Author/publisher of candidate: Codex lead G4 researcher.
Date: 2026-10-13. **Scoped hand acceptance with the compact-slot justification supplied below.**
No parameter inverse, physical semialgebraicity, cone separation, numerical test, formal verification or general G4 closure is inferred.

Reviewed [FINITE-OBSERVABLE-SECANT-REDUCTION.md](FINITE-OBSERVABLE-SECANT-REDUCTION.md),
SHA256 595a0cc3e4b95e94ba9c821ac1067e5eb5b036c86c2b71223c5110a5cc7a8ed4.
The audit targets the stated reduction, not the missing local theorem.

## Original generators and observable secants

The ideal argument is correct. A finite generating family for the ideal of all response differences need not itself consist of observed coordinates; expressing each generator using finitely many original differences and taking their finite union produces original-coordinate generators. Its algebraic identities hold on the ambient finite polynomial chart, and hence on the actual physical image $\Gamma$ without requiring that image to be semialgebraic.

For bounded $f_i(z_j)/S_j$, the identity
$f_o=\sum_i h_{oi}f_i$ gives the asserted all-coordinate limits because
$h_{oi}(z_j)\to h_{oi}(z_*)$. The same finite-vector subsequence works for every row. No estimate on $(z_j-z_*)/S_j$ is used, so fair $\sqrt S$ displacements and higher-order boundary arcs are retained. This does not say the resulting vectors are ordinary parameter tangents or freely physically realizable.

The lead's additional observation is valid: once $P_o(z_*)=P_o(T)$, the differences are $P_o(z)-P_o(T)$, independent of the chosen limit point. Original generators can therefore be chosen for a fixed finite body shape before taking the limit. Their evaluated coefficient map still depends on the eventual limit. This supplies no uniform shape/count list or finite forcing certificate.

The chart polynomiality is correct for the stated natural-mode original topology rows: finite Kingman rates are the integer $\binom{k}{2}$, routing is finite polynomial composition, and completion has fixed rational coefficients. Calendar/rate/coin/incidence restrictions remain in the image $\Gamma$. If a different menu distinguishes removed source occurrences or shared registers, a fixed corresponding chart and preserved response semantics must be supplied separately; they are not consequences of this algebra alone.

Exact natural COMMON collapse of a private equal-arm cell is valid: either common parent gives the same ordinary duration, with no external interaction inside the slot. Positive actual retained assignment weights force their resolved profiles into the finite target support even if limiting weights become zero. Profile coincidences require weight sums, as written. These constraints are necessary; the note correctly avoids claiming their converse physical realization.

## Strength and stochastic comparison

The compactification's effective ordinary clock has density $1-2p$ on cell intervals. After removing the finitely many persistent intervals, its nonnegative missing COMMON mass is the limit of $2\sum_{\rm extra}pt$. The separately accepted zero-loss result sets that mass to zero on the shared subsequence. Since the finitely many bounded blocks have $t\le H$,
$$
pt\le p(e^t-1)\le e^Hpt,
$$
so the stated total strength $S_j$ tends to zero.

At fixed total copy cap, replacing one extra by its full COMMON ordinary interval changes its capped private operator by $O(w)$. All source prefix/suffix actions, including varying cores and boundary parameter values, are stochastic contractions. Telescoping yields the original completed-row estimate with a constant independent of extra count. This requires no inverse of a core and no latent kernel observation.

The survival/coin cube gives a convergent fixed-chart subsequence, including unexposed survival-zero coordinates. Capped source polynomiality remains continuous there. The narrower finite-exposure hypotheses previously used for commonization are not extended by this ambient step.

## Compact insertion positions at a boundary body

Section 4 compresses one construction that should remain explicit in applications. Retain each bounded private equal-block gap as a labelled bookkeeping slot, even if graph simplification at the limit would erase a zero gap or merge neighboring ordinary passages. Its collapsed clock $a_j$ is at most $H$, with survivor at least $e^{-H}$. After a subsequence $a_j\to a_*$. An extra occupies
$$
0\le r,\qquad 0\le t,\qquad r+t\le a_j.
$$
Use the fixed compact slot-index set times $[0,H]^2$. Weak measure limits have support in the closed limiting triangle $r+t\le a_*$. If $a_*=0$, both coordinates tend to zero. No division by a vanishing gap length or transport through an unbounded time coordinate is needed.

Keep this bounded slot separate from any adjacent unexposed core population whose exposure can tend to infinity. Merging them and asserting compactness of ordinary-time positions would be unjustified. Finite labelled subdivisions are harmless auxiliary source bookkeeping and preserve original response polynomials.

For fixed cap, equal-arm $B(t,p)$ is analytic in $t$ and polynomial in $p=g(1-g)$, by arm symmetry. The difference $B(t,p)-E_t$ vanishes on both $p=0$ and $t=0$ and is divisible by $pt$ analytically. Its coefficient at $t=0$ is $-2pQ$. Consequently
$$
F(t,p)=\frac{B(t,p)-E_t}{p(e^t-1)}
$$
has a continuous extension on the compact rectangle, with
$F(0,p)=-2Q$ and $F(t,0)=V(t)$.
Since these extensions agree on the full zero-strength locus, uniform continuity gives
$\|F(t,p)-V(t)\|\to0$ uniformly whenever $w\to0$.

An insertion row in a fixed slot uses the continuous factors
$E_r$, $V(t)$ and $E_{a-r-t}$, composed with the fixed-template body factors. Those other factors are polynomials in survivals and coins, including boundary survival zero. Thus the original-row insertion function is continuous jointly in the compact body chart and slot coordinates, including a zero-duration slot. Coin endpoints and erased limiting vertices cause no discontinuity if their fixed template labels and state bookkeeping are retained. The limiting operator remains a proof functional, not a new physical row.

This establishes the compactness/continuity step needed to obtain one probability measure and all its fixed-row insertion limits. It is not an assumption of differentiability in the physical parameters.

## First-insertion remainder and exact constraint

The preceding uniform bound gives summed single-cell remainder $o(S_j)$ because $\max_i w_i\le S_j\to0$. For cross terms, compare each actual prefix to its all-ordinary collapsed prefix; stochastic telescoping bounds their difference by $C\sum_{k<i}w_k$. Summing against the $i$th difference gives at most
$C^2\sum_i w_i\sum_{k<i}w_k\le C^2S_j^2/2$.
This is uniform in extra count and remains valid after arbitrary original stochastic composition.

Therefore the normalized original matching equations have the stated sign
$G_o(a)+I_o(\nu)=0$. The same finite-vector subsequence and compact measure limit suffice for every fixed original row. The vector and measure come from one shared physical sequence; membership in the separate secant set and positivity of the measure do not by themselves characterize their joint physical compatibility.

Verdict: the reduction passes with the labelled bounded-slot construction above. It narrows the outstanding local problem to the actual constrained observable-secant/insertion cone. It does not prove that cone has no cancelling pair, establish a parameter Lipschitz inverse, supply a physical curve-selection theorem, or produce a target-dependent finite legal certificate. Next action: attack that constrained cone while retaining its genuine shared-source and boundary constraints.
