# The strongest defensible shadows argument

- Date/session: 2026-09-30 UTC / commons-builder
- Original motivating theory: Nolan Downard.
- Formal interpretation, examples, and literature comparison: Codex.
- Label: hand-derived argument and sourced comparison; no novelty, empirical validation, or machine-verified proof claimed.

**Correction to the proposed next target:** read [the decision-certificate correction](2026-09-30-commons-builder-decision-certificate-correction.md). A general impossibility witness may require an indistinguishable set, not only a pair. The original proposal below remains visible for provenance.

## The claim worth defending

Partial observations can constrain a useful property or decision without identifying the complete hidden system. Several views help when their combination distinguishes possibilities that matter to that target. A result can transfer between scales when explicitly specified maps preserve its relevant structure.

This is a precise foundation for Nolan's intuition. Universal self-similarity, automatic transfer from biology to psychology, and resolution of a Millennium Prize Problem are stronger claims not established here.

## Identification: exactly what a shadow reveals

Let M be a model class, O:M→Y an observation map, and q:M→Q the target property. A decoder r:O(M)→Q with q=r∘O exists exactly when

$$
O(m)=O(m') \Longrightarrow q(m)=q(m').
$$

Necessity: equal observations give the same decoded answer. Sufficiency: for each realized observation, assign the shared q-value of its compatible models. Constancy makes that assignment well-defined.

The domain O(M) contains only realized observations. This avoids imposing values on impossible observations. The result is elementary and classical in character; it does not prove the assumed model class or observation map describes the world.

For multiple views use their joint observation map. Identification holds when every pair that disagrees about q is separated by at least one view. Repeating an exact redundant view supplies no new separation. With noise or a changing lens, compatibility must include admissible errors and calibration states; an exact result does not automatically become stable reconstruction.

[Kalman (1963)](https://epubs.siam.org/doi/10.1137/0301010) provides a linear-systems precedent distinguishing internal state from input/output descriptions. The accessible abstract says input/output relations identify only the completely observable and controllable portion. That is a restricted mathematical result, not evidence about psychological constructs.

## Transfer requires a preserved consequence

A causal cross-scale comparison needs a map τ from low-level outcomes to high-level outcomes and a compatible map ω between the interventions being considered. One distributional consistency condition is

$$
\tau_* P_L^{do(i)} = P_H^{do(\omega(i))}
$$

for every declared intervention i, where τ* pushes the low-level outcome distribution through τ. This expression summarizes a preservation requirement; by itself it does not include all conditions in any paper's definition.

[Rubenstein et al. (2017)](https://arxiv.org/abs/1707.00819) formalize exact transformations between structural equation models and emphasize agreement on mapped intervention effects. [Beckers and Halpern (2019)](https://www.cs.cornell.edu/home/halpern/papers/abstraction.pdf) develop stricter abstraction notions, addressing differences hidden by favorable distributions or intervention choices.

These are close precedents for the proposed direction. They also make the missing obligations concrete: identify the maps, declare permitted interventions, and establish preservation. Finding similar patterns alone supplies none of those obligations.

## A hard limit: identical observations, different causes

Let U be a fair binary variable.

- Model A: X=U and Z=X.
- Model B: Z=U and X=Z.

Both yield the same observed distribution: half (X,Z)=(0,0), half (1,1). But setting X to 1 yields P(Z=1)=1 in A and P(Z=1)=1/2 in B.

Thus even complete knowledge of this observational distribution does not identify that intervention effect. An intervention, an additional assumption, or other separating evidence is required. Calling the two observable patterns self-similar does not resolve the difference.

## A consequential extension: enough evidence for a decision

The [other chat's observability extension](https://github.com/Sodelin/Cross-Scale-Causal-Formalization/blob/fceff354221e521538938f60457ba90481c6eb45/research/nolan-scope-theory-2026-09-30/OBSERVABILITY-EXTENSION.md) already distinguishes reachable questions, compatible models V(D), and possible answers. Our extension asks whether uncertainty still matters to a chosen action.

For finite nonempty compatible model set V(D), finite nonempty deterministic action set A, and specified loss ℓ(a,m), define

$$
R_D(a)=\max_{m\in V(D)}[\ell(a,m)-\min_{b\in A}\ell(b,m)],
\qquad \rho(D)=\min_{a\in A}R_D(a).
$$

ρ(D) is the smallest worst-case regret of a fixed action. A decision is certified to tolerance δ when ρ(D)≤δ. This is a decision criterion under stated assumptions, not a claim that the loss captures all real consequences.

If an exact calibrated probe shrinks V(D) to a nonempty subset, each action's maximum regret cannot increase. Taking the minimum over the same action set therefore gives a nonincreasing ρ. It need not strictly improve. Probe costs are not included in that monotonicity result.

**Worked finite example.** Hidden θ is -1 or +1. The first view is θ²=1. Actions are a=-1 or +1, with squared loss (a-θ)². The best action in each known state has loss zero, but either fixed action has worst-case regret 4. Repeating θ² changes nothing. One permitted sign observation identifies θ, reducing regret to 0. Restricting actions to these two deterministic choices matters; randomized or continuous actions would change the calculation.

| Available view | Compatible θ | Best worst-case regret |
|---|---|---|
| θ²=1 | {-1,+1} | 4 |
| θ² repeated | {-1,+1} | 4 |
| θ² plus sign(θ) | one value | 0 |

This demonstrates useful separation in a toy model. It validates neither the universal theory nor a real-world application.

## Alignment and a concrete next target

This agrees with the other chat's fibre/singleton treatment and its warning that observable behavior need not determine hidden structure. It also addresses the [scope theory](https://github.com/Sodelin/Cross-Scale-Causal-Formalization/blob/fceff354221e521538938f60457ba90481c6eb45/research/nolan-scope-theory-2026-09-30/snapshots/theory-analysis.md): instead of making system reconstruction the sole target, generate the alternative target "certify a good decision with affordable evidence."

The next research target is **least-cost measurement or intervention selection under bounded calibration drift**. Specify a finite family of model–calibration pairs, permitted probes, costs, actions, loss, and tolerance. Produce either a probe plan guaranteeing the desired regret bound or an indistinguishable pair showing that no permitted plan can do so. Search the active-learning, experiment-design, robust-decision, and causal-abstraction literature before claiming novelty.

What currently works is the restricted logical framing and these examples. Whether this approach discovers valuable cross-domain maps more reliably than existing methods remains untested. Clinical hypotheses require their own empirical evidence; this abstract argument establishes no diagnostic mechanism.
