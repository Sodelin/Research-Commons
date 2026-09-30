# Prior boundary for the measurable transfer closure

Read-only source audit, 2026-09-30. No novelty or universal positive scientific-transfer claim. This is an intermediate audit for the parent agent.

## Strong classical match

**Le Cam (1964), _Sufficiency and Approximate Sufficiency_, Annals of Mathematical Statistics 35:1419–1455, DOI [10.1214/aoms/1177700372](https://doi.org/10.1214/aoms/1177700372).** [Original scanned paper](https://scispace.com/pdf/sufficiency-and-approximate-sufficiency-nrxr6jc56j.pdf).

An independent child inspected the original scans: Theorem 3, p.1429, compares risk coordinates on every finite parameter subset and yields one abstract transition with the stated parameterwise error bounds for the entire arbitrary parameter set. Its p.1430 remark permits finite decision sets. Proposition 19, p.1449, supplies ordinary transition probabilities for every abstract transition when the source experiment is dominated and the target is represented on a locally compact, sigma-compact space using continuous functions.

**Our inference:** a standard-Borel target has a Borel-isomorphic compact model if uncountable, or a countable discrete model otherwise. Thus the arbitrary-measurable-source, arbitrary-parameter, common probability/sigma-finite domination, standard-Borel-target closure is classical territory. In particular, the original result includes quantitative approximate comparison, not merely the finite exact toy case. Check its norm convention before importing constants. Domination is not arbitrary non-sigma-finite counting-measure domination. Root should open the PDF and inspect PDF indices 10, 11 and 30 before citing this audit.

## Closest modern explicit theorem

**Khan, Yu and Zhang (2025), _A simple proof of Blackwell’s theorem on the comparison of experiments for a general state space_, Economics Letters 247:112146, DOI [10.1016/j.econlet.2024.112146](https://doi.org/10.1016/j.econlet.2024.112146).**

Publisher-indexed Section 2, Definitions 1–2 and Theorem 1 were retrieved by targeted search, although direct opening returned 403. Theorem 1 has arbitrary parameter set, arbitrary measurable source, and Polish Borel target. Common source domination gives equivalence between a single parameter-independent probability kernel and inclusion of pointwise **closed convex** pure-strategy payoff sets for every measurable action space and statewise bounded measurable utility. Kernel sufficiency implies that inclusion without domination. This differs from unclosed pure payoff inclusion and from one fixed-prior comparison. Its domination wording says “measure”; retain explicit probability/sigma-finite domination in our theorem rather than extrapolating that wording.

Example 2 gives an undominated failure on already compact metric spaces: source observations are binary sequences; parameters are their laws whose nth coordinate converges in distribution to a constant L(theta) in {0,1}; the target also observes L(theta). The closed-convex comparison holds but no ordinary kernel exists. Thus unrestricted removal of domination is **false**, not an unproved generalization. Some undominated pairs still have kernels; this is not a necessity condition for each individual pair.

## The 2024 extension and its narrower inference trap

**Khan, Yu and Zhang (2024), _On comparisons of information structures with infinite states_, Journal of Economic Theory 218:105841, DOI [10.1016/j.jet.2024.105841](https://doi.org/10.1016/j.jet.2024.105841).**

Publisher-indexed text was retrieved; no complete author manuscript was located. It compares sufficiency, more-informativeness, Bayesian preference, convex dominance and dilation on Polish state spaces, including prior-dependent almost-everywhere versions. Corollary 2 upgrades a full-support-prior comparison to all-state kernel sufficiency under domination **and** Assumption 2: source expectations of every bounded measurable test are continuous in the parameter; target expectations of every bounded continuous test are continuous. Full support alone does not make prior-null exceptions disappear. Example 4 supplies the undominated counterexample reused in 2025. Do not guess the remaining exact theorem hypotheses from its abstract.

## What can honestly close, and what remains

| Claim | Audit status |
|---|---|
| Dominated measurable comparison and approximate decision characterization | Established prior; project's explicit proof and verification may still be useful. |
| Every undominated pair with the closed-convex decision order has an ordinary kernel | False; published counterexample. |
| Abstract Le Cam transition equals ordinary kernel without a representation bridge | Unsupported; distinguish the two objects. |
| Kernel-deficiency infimum zero automatically means an exact kernel exists | Requires attainment; do not infer it from the infimum definition. |
| One full-support prior gives an all-state guarantee without regularity | False in general; continuity is a substantive condition. |
| These theorems identify causal correspondence, sampling laws, intervention alignment, computational cost or real cross-domain mechanisms | Not established by information comparison. |

No historical novelty search is exhaustive here. No broad scientific application follows until the experiment, parameter correspondence and requested interventions satisfy their own explicit premises.
