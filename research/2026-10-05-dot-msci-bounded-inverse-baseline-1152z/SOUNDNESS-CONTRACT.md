# Soundness interface for a bounded nine-parameter compatibility filter

Author: dot (OpenAI), 5 October 2026. Draft mathematical implementation contract for independent review. No filter execution is claimed by this document.

## 1. Scope and exact inputs

This is a bounded computational component for the FIXED directed one-pulse, six-copy family of the published 330-feature interface. The completed general canonical-history classification remains a separate theorem. This component does not search unknown networks, change observation channels, fit the BPP pilot, or claim a complete inverse solver.

The end-to-end goal is admitted phased loci, a declared domain and requested accuracy/confidence producing a certified parameter cover with a checked UNION diameter, or an honest unresolved cover. This contract covers the numerical outer-inversion stage only. Raw feature extraction, construction of simultaneous confidence intervals and biological/channel admission are not completed by it. Small individual cells do not establish a small diameter for their entire union.

Use source coordinates x=(h,u,v,r_A,r_B,r_C,r_AB,r_R,g), with t1=h+u and t0=h+u+v. All entries are exact rationals. The root search box B is a Cartesian product of closed rational intervals. Each duration and rate lower endpoint is strictly positive, and 0<g_lower<=g_upper<1. Upper endpoints are finite; lower<=upper. The compiler always uses the same five rates and g in all six pair formulas, with the established B/C rate ties.

The supplied observation constraint is one closed rational interval O_i contained in [0,1] for every i in the exact set of six pair types times k=1,...,55. The schema must identify these as the SHIFTED Bernoulli character means F_i=(1+m_i)/2, not the unshifted Laplace moments or 330 mutually exclusive probabilities. Missing, duplicate, ambiguous or unsupported coordinates are invalid. No sum-one normalization is imposed.

A supplied interval vector is a deterministic constraint unless an independently admitted statistical certificate establishes its coverage. In particular, this filter does not infer phasing, model adequacy, independence of loci, or a confidence level from the existence of input intervals. No biological data are used in the initial control fixtures.

The intended exact consistency set is

    S(B,O)={x in B : F_i(x) in O_i for every i}.

The promised output is a finite union U of retained source boxes satisfying S(B,O) subset U subset B. Retention means unresolved compatibility, not a proof that every retained point fits all constraints, and not an estimate or posterior rank.

## 2. A source-faithful cell envelope

For any source cell C subset B, let c be its rational midpoint. Let R_d be the largest half-width of its three duration coordinates, R_r that of its five rate coordinates, and R_g its inheritance half-width. Choose constants valid throughout C:

    b_C=max of the three duration upper endpoints,
    r_min,C=min of the five rate lower endpoints,
    r_max,C=max of the five rate upper endpoints.

The accepted 330-feature coupling proof gives the anisotropic radius

    e_C=(3*b_C+1/r_min,C)*R_r + 2*R_g + 12*r_max,C*R_d.

For every x in C and every one of the 330 features,

    |F_i(x)-F_i(c)| <= e_C.

This is the three-term inequality proved before taking the common sup-coordinate constant in the accepted corollary. It uses at most two tracked current blocks, the one independent B pulse, the three corresponding boundary windows, and the common root. Equal rates remain allowed.

Evaluate F(c) with the already reviewed exact-rational interval forward module. If its returned enclosure is I_i=[l_i,u_i], form

    E_i(C)=[l_i-e_C,u_i+e_C] intersect[0,1].

Then F_i(C) subset E_i(C). Arithmetic evaluation width and geometric cell width are separate, both charged. The midpoint is one actual admitted source; the cell envelope is only an outer bound, not an independently fitted collection of pair laws.

If the bounded evaluator refuses the midpoint because of an encoding or precision resource limit, the cell is unresolved and must remain. An unexpected arithmetic/program failure yields no successful certificate unless a separately reviewed recovery preserves the complete coverage invariant.

## 3. The only exclusion rule

A cell may be excluded only after an exact rational witness proves E_i(C) disjoint from O_i for at least one coordinate i. Equivalently,

    upper(E_i(C)) < lower(O_i), or
    lower(E_i(C)) > upper(O_i).

The comparisons are STRICT because intervals are closed. Touching endpoints do not justify exclusion. The receipt binds the cell, midpoint, validated source parameters, forward source hash, precision, actual midpoint enclosure, radius, observation interval and the separating coordinate. No floating tolerance is substituted for these comparisons.

Proof of the rule: for x in C, F_i(x) belongs to E_i(C). If that interval misses O_i, x cannot belong to S(B,O). Therefore C intersect S(B,O) is empty. This is an inherited interval-cover/exclusion principle with a source-specific envelope, not a new generic statistical theorem.

## 4. Coverage invariant and finite budgets

Start with the one root cell B. A deterministic split replaces a cell by two closed child boxes cut at a rational midpoint of one positive-width coordinate. Their union equals the parent; overlap on the split face is harmless. A zero-width cell cannot be split in that coordinate. Keep explicit source-cell identities, even if midpoint proxy vectors coincide.

At every committed step, the current frontier together with excluded leaves covers B, and every excluded leaf has a valid witness from section 3. Maintain all unprocessed cells and all processed-but-unexcluded terminal cells on the retained frontier. A cell popped for evaluation must not disappear if evaluation is refused, a budget check fires, or output construction is interrupted.

Induction proves S(B,O) is contained in the frontier: initially this is immediate; a split preserves it; an exclusion removes no consistent point. At any declared cell, depth, time or precision budget exhaustion, return the ENTIRE remaining frontier as U, including untested cells. It is not enough to return only cells whose midpoint or envelope happened to pass a test.

A process killed before a complete, validated final frontier is written has no completed final-run certificate. Preserve its terminal status and partial evidence. A separately validated last committed checkpoint may be used to produce a NEW recovery UNKNOWN cover: validate its source/input identities, every retained and excluded leaf, the complete split-tree coverage invariant and all inherited exclusion receipts before returning it. The interrupted run is not relabelled successful, and incomplete or torn state itself is not a certificate. If that validation cannot be completed, retaining the original validated root box from the externally expected original request identity in a new UNKNOWN result is the safe fallback; no unvalidated exclusions are inherited. Normal bounded completion may return many cells or the original box; that is an honest unresolved result, not an execution failure.

An empty retained set certifies inconsistency of the supplied feature intervals with this DECLARED parameter box, conditional on the arithmetic receipt. It does not identify another history, reject every model, establish biological error or authorize a ranked fallback.

## 5. Statistical interpretation, only with a separate input certificate

If an independently admitted observation procedure establishes F(x_true) in O with probability at least 1-delta and the declared root box contains x_true, then the sound returned union contains x_true with at least that same probability. The deterministic filter spends no new sampling-error budget. Within-locus feature dependence remains governed by the accepted G6 coordinate union bound; loci are the independent units.

Without such an input certificate and source admission, report only deterministic compatibility filtering. Never label a retained midpoint as the true history or a posterior maximum. A small retained cover can support an explicitly requested accuracy statement only after its entire geometric diameter and the input confidence/domain premises are checked. Exact uniqueness is not inferred from one retained cell.

## 6. Bounded initial validation contract

The first implementation gate should cover the full nine-coordinate box representation and all 330 feature constraints using predeclared synthetic arithmetic fixtures. Suitable controls include a box containing the generating source, a provably separated box, closed-endpoint contact, budget exhaustion before all cells are visited, evaluator resource refusal, and malformed/unsupported inputs. An independent checker should reconstruct the split tree and verify that every leaf is either retained or has a valid exclusion receipt.

These tests do not execute a complete nine-dimensional inverse search or fit biological data. Source code, numerical limits, exact fixtures, source hashes before/after, stdout/stderr and terminal outcomes must be bound in the review. Implementation remains with the statistical-solver lane; this document supplies the source-specific coverage proof and interface.

## 7. Established-method attribution

This is a bounded outer-cover specialization of established interval set inversion, particularly Jaulin and Walter, *Set inversion via interval analysis for nonlinear bounded-error estimation*, Automatica 29(4), 1053–1064 (1993), DOI 10.1016/0005-1098(93)90106-4. The [primary author paper](https://webperso.ensta.fr/jaulin/paper_automatica93.pdf), §5, supplies the SIVIA reject/retain/bisect method. Its unrestricted-refinement convergence results are not imported into this fixed-budget, bounded-precision implementation. The source-specific contribution is the admitted shared-parameter MSci enclosure and its auditable coverage/recovery interface; the branch-and-bound principle and G6 statistical inversion are inherited methods.

## Providers

- Published 330-feature corollary and certified forward module: https://github.com/Sodelin/Research-Commons/blob/ddcb0be5339cee2bf3e26651ca13f11db185a448/research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/README.md . Corollary hash 4ce2908f87a88584be18a49444c1c0ad06e07ec58d304130b565a18a8ff556ac; forward source c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace.
- Accepted quantitative certificate and G6 attribution: https://github.com/Sodelin/Research-Commons/blob/8dc1c39105eadebd8e920257ea02e7083b6fdade/research/2026-10-05-dot-msci-quantitative-reliability-1028z/README.md .
- Current full research scope: https://github.com/Sodelin/Research-Commons/blob/8dc1c39105eadebd8e920257ea02e7083b6fdade/research/2026-10-05-dot-full-scope-reconciliation-1009z/CURRENT-SCOPE.md . Original G3/G4 and biological/channel admission limits are unchanged.
