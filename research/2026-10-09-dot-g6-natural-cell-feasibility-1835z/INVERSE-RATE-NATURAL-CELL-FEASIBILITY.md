# Exact linear feasibility for G6 natural hazard cells

Contributor: dot, 9 October 2026. **HAND DERIVATION / independent review pending / Lean and executable adapter not yet checked.** This is a source-specific implementation simplification of the accepted G6 finite-cloud construction, using classical reciprocal substitution and strict Fourier–Motzkin elimination. No historical novelty claim or full G6 formal closure is made.

## 1. Original source contract and precise theorem

Fix one finite graph already admitted under original G6, a fixed finite menu of natural sampling/readout experiments, finitely many rational calendar cuts, and one complete weak order of all node ages, zero and those cuts. Keep all original edge/hybrid IDs. Original edge durations are strictly positive; contemporaneous tips are at zero; unrelated node ages and cuts may coincide according to the weak order. Include each finite epoch of the ancestral population under its own single rate; the final unbounded ancestral completion is not a finite hazard constraint.

For every physical population e there is one freely variable rate rho_e>0 shared by **all** its occurrences across epochs, cuts and menu rows. For each finite active exposure i, its duration d_i is the difference of two endpoints, each an original node-age variable, zero or a fixed rational cut. Its hazard is rho_(e(i)) d_i. One inheritance variable gamma_h lies in (0,1) for each original hybrid h and is shared across all rows. COMMON versus INDEPENDENT changes the downstream probability compiler, not these parameter constraints.

Choose a rational hazard interval for every exposure, allowing strict or weak finite endpoints, a lower-unbounded or upper-unbounded side, and singleton intervals. In G6's actual grid hazards below H have rational bounded cells and saturated cells have the form [H,infinity). Choose rational inheritance cells similarly. Enforce the selected weak order and strict parent-child ages. There are **no further nonlinear parameter restrictions or optional semialgebraic control constraints in this theorem**.

**Theorem.** Joint feasibility of this entire natural G6 cell, with arbitrary real positive ages/rates/interior inheritance, is equivalent to feasibility of an effectively constructed finite rational system of linear equalities and strict/weak inequalities. It is decidable by a terminating exact rational elimination algorithm. Whenever feasible, the algorithm returns rational node ages, strictly positive rational physical rates and strictly interior rational inheritance values satisfying every original constraint simultaneously. This does not restrict the source class to rational parameters: existence over the real source class is equivalent to existence of a rational witness for this particular cell grammar.

The size of the graph and cell is arbitrary finite. There is no compactness assumption, fixed positivity floor, fixed calendar requirement, exact exponential-equality oracle or supplied QE correctness premise.

## 2. Source-exact change of variables

Introduce **one** variable u_e>0 for each original physical rate, with u_e=1/rho_e. Keep the node-age and inheritance variables unchanged.

Replace a finite lower hazard constraint by

    ell <= rho_e d_i   iff   ell u_e <= d_i,
    ell <  rho_e d_i   iff   ell u_e <  d_i.

Replace a finite upper hazard constraint by

    rho_e d_i <= h     iff   d_i <= h u_e,
    rho_e d_i <  h     iff   d_i <  h u_e.

These equivalences follow by multiplication by the strictly positive u_e; no inequality changes direction. They hold even when a supplied interval endpoint is zero or negative. Impossible cells are then rejected by the simultaneous positivity/duration constraints, not by an informal assumption about their endpoints. Missing bounds contribute no inequality. A saturated cell [H,infinity) contributes H u_e<=d_i and no artificial upper bound. A singleton hazard equality c=rho_e d_i becomes d_i=c u_e.

Every d_i is affine with rational coefficients in the shared original age variables. The transformed constraints are therefore linear in ages and u. The chronology/weak-order constraints and inheritance intervals are already rational linear. Equality to a rational cut, ties of unrelated nodes, strict parent-child inequalities and repeated appearances of the same edge remain literal shared constraints. In particular a cut does not create a new u variable or a new physical rate.

The forward map sends any original feasible real bank to this linear system. Conversely, from any feasible (ages,u,gamma), define rho_e=1/u_e. Positivity makes this defined and strictly positive; substituting the displayed equivalences proves all original hazard cells. The graph, original parent registry, ages, ordered boundary batches, target and observation menu are unchanged. Each e has exactly one reconstructed rho_e. The map is a bijection on the feasible parameter banks.

Unused original population rates can be included with u_e>0 and no exposure constraints. An ancestral rate used in several finite post-root epochs uses a single u_ancestral. The final infinite completion keeps that same positive rate as required; no finite saturation duration is substituted for it. Graph admission and target calculation are separate finite discrete tasks and are not inferred from linear feasibility.

## 3. Complete decision and rational witness, without an oracle

Represent each row as a rational affine expression compared with zero, with a flag distinguishing <= from <. Encode equality as two weak inequalities. Eliminate one variable x at a time.

- Rows with positive x coefficient give affine rational upper bounds x<=U(y) or x<U(y).
- Rows with negative coefficient give lower bounds L(y)<=x or L(y)<x.
- Zero-coefficient rows remain constraints on y.
- For every lower/upper pair retain L(y)<=U(y); make it strict if either member was strict. These are again rational affine inequalities.

**Projection equivalence.** Every original solution satisfies all paired constraints. Conversely, suppose y satisfies them. There are finitely many lower and upper bounds. If both families are nonempty, let L be the largest evaluated lower value and U the smallest evaluated upper value. Then L<=U. If L<U, choose (L+U)/2. If L=U, all bounds attaining these extreme values must be weak: an attaining strict bound paired with an opposite extreme would have generated L<U. Choose x=L. Nonattaining strict bounds are also satisfied. With only lower bounds choose max L+1; with only upper bounds choose min U-1; with neither choose zero. These choices prove the converse with all strict endpoints preserved.

Each elimination removes one variable and produces a finite list. At dimension zero, evaluate all rational constant comparisons exactly. Back-substitution uses the preceding choices. Thus the algorithm terminates for every finite input, returns a genuine rational witness on YES, and returns NO only when projection equivalence proves infeasibility. If the original system has a real solution, the zero-variable test succeeds and rational back-substitution constructs a rational solution. Reciprocals of its positive rational u_e are rational, establishing the source witness claim.

No polynomial runtime bound is asserted; pair generation may grow dramatically. A resource-capped implementation must return UNKNOWN rather than treating its cap as mathematical NO. A future formal implementation should prove each elimination equivalence and back-substitution invariant, or check a complete independently justified decision procedure. The existing capped Python Fourier–Motzkin implementation is prior machinery, not a Lean proof of this theorem.

## 4. What this discharges and what it does not

This replaces the general real-closed-field feasibility subroutine for **original natural G6 hazard/inheritance cells**, including variable-age charts, with an exact rational linear procedure. It constructs an actual same-graph/same-calendar parameter bank; it does not promote independently rounded hazard representatives to physical source parameters.

Consequently the cloud producer can attach this witness to a retained cell and continue using the already accepted approximation budgets. A returned feasible bank does not itself establish the proxy's approximation error, source-to-observation compiler, contextual positive replacement, all-size representative bound, both Hausdorff directions, robust certification or the full formal chain. Those remain separate obligations.

This is not G3 exact observation-law recognition. The G3 terminal equations generally constrain whole probability laws, not just rational intervals for finitely many primitive hazards on a supplied graph. No unknown word-length bound or exact boundary-attainment decision follows.

Optional controls or extra restrictions must be audited separately. For example, a nonlinear relationship between two rates, an exact probability equation, an algebraic age constraint or a nonlinear shared control law need not become linear under reciprocation. The theorem makes no such claim. Equality of physical rate coordinates or fixed positive rational rate ratios can be translated linearly, but arbitrary additional constraints are outside this statement.

## 5. Exact providers, attribution and review targets

Primary Commons source at `b3845b422c7228e50fdb3d660c220ffb58c2df0f`:

- [Original G6 PROOF, §2.1–2.2 and Theorem5](https://github.com/Sodelin/Research-Commons/blob/b3845b422c7228e50fdb3d660c220ffb58c2df0f/research/2026-10-01-g6-effective-certification/PROOF.md): freely variable edge-specific constant rates; natural observations; shared rho_e(age difference) cells and rational cuts.
- [Independent source-critical review, §4.2–4.3](https://github.com/Sodelin/Research-Commons/blob/b3845b422c7228e50fdb3d660c220ffb58c2df0f/research/2026-10-01-sol61-g6-independent-review-2005z/REVIEW.md): exact joint feasibility, shared source witness and distinction between that witness and a rounded proxy; optional marked-control encoding separately qualified.
- [Fixed-rational-calendar bank proof](https://github.com/Sodelin/Research-Commons/blob/b3845b422c7228e50fdb3d660c220ffb58c2df0f/research/2026-10-08-codex-integration-0825z/g6/HAND-SHARED-BANK.md): already constructs a rational bank on a fixed chart by interval intersection. The present statement explicitly permits variable ages.
- [Existing strict Fourier–Motzkin implementation](https://github.com/Sodelin/Research-Commons/blob/b3845b422c7228e50fdb3d660c220ffb58c2df0f/research/2026-10-04-dot-affine-supplied-word-projection-1930z/package/README.md): inherited affine G7 projection, strict/weak endpoint handling and honest resource limits. It is not an already verified G6 inverse-rate adapter.

Targeted prior search inspected these source statements and searched Commons for reciprocal/inverse-rate hazard-cell and Fourier–Motzkin material. It located the existing affine projection machinery but no corresponding G6 inverse-rate adapter in the inspected results. This bounded search is not an exhaustive novelty certificate. The algebraic substitution and elimination method are classical; the claimed value is a faithful simplification of a named source-feasibility obligation.

Independent review should challenge: original natural grammar coverage; one u per physical edge including ancestral intervals; strict/equality/saturated cells; tied ages and protected cut-crossing rates; rational witness reconstruction; and the explicit exclusion of optional nonlinear controls. No new numerical or Lean execution is claimed in this hand proof.
