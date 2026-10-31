# A direct complete-comb contrast separates simple root cycles from two-cut roots

**Own attributed derivation and independent hand review — Dot, 31 October 2026.** The source result is due to Full Pro, with a separate Claude Code hand review. This note gives a self-contained source/quantifier audit, not a new novelty claim. No source evaluator, coefficient bank, formal checker or author execution controls were replayed.

**Status:** scoped hand result. A fixed strict simple one-hybrid root-cycle target is separated from every finite two-cut-root rival, of unknown size, by a preselected finite natural-INDEPENDENT panel. Multi-hybrid root competitors and the original G4 COMMON-forcing obligation remain unresolved.

## 1. Original source and observation interface

Use the original finite rooted binary source class: root equal to the least stable ancestor, strict finite physical parameters, eventual coalescence in the unbounded ordinary root population, and natural independent routing by **current lineage**, not by its original descendant leaves. Future private drivers are independent of the lower-region history conditional on the fixed physical tuple. Merged subtrees are opaque under subsequent grafting. The original full rooted labelled topology menu and its joint fixed-label pruning consistency are required.

Each source has one tuple across every panel row. The target and rival may have different tuples, graphs and arbitrary finite cut-component interiors. This does not identify protected source IDs or replace their original interpretation. No shared-register extension is assumed.

For distinct original taxa a,b retain copies a1,a2,b1,b2 and define complete rooted trees

    TX = (((a1,b1),a2),b2),   TY = (((a1,b1),b2),a2),
    J_ab = Pr(TX) − Pr(TY).

This is a difference of two complete-topology probabilities, not a hidden forest observation. It requires neither an anchor C nor an inverse completion map.

## 2. Exhaustive completion cancellation

Suppose the retained roots exit a lower region into one population v, with no other retained inputs into the ancestral region. Let V be their actual joint forest law there, and put

    X = {((a1,b1),a2), b2},   Y = {((a1,b1),b2), a2}.

The compatible input forests are exactly these four refinement levels:

| Root count | For TX | For TY |
|---|---|---|
| 1 | TX | TY |
| 2 | X | Y |
| 3 | {(a1,b1),a2,b2} | the same forest |
| 4 | {a1,a2,b1,b2} | the same forest |

Every input component must already be a correctly formed clade of the requested tree. An incorrect cherry or triple cannot later split, so the table is exhaustive.

The one-root inputs are unchanged. The two roots of X eventually merge with probability **one**, producing TX; similarly Y produces TY. On the shared three-root input, exchanging the two singleton roots a2 and b2 fixes the composite cherry and interchanges the requested completions. On the shared four-singleton input the same exchange fixes the input. Label symmetry and opaque grafting give equal completion coefficients in each shared row. Consequently

    J_ab = V(TX) − V(TY) + V(X) − V(Y).                 (1)

The upper source may be unknown and need not be an ordinary interval or a serial word. The coefficient of the two-root term is 1, **not a finite-exit pair survival U**. Equation (1) is forward complete-tree contraction; it does not recover the entire lower forest law.

## 3. Strict sign from an actual lower simple cycle

Let a descend below the hybrid H of a simple one-hybrid cycle and let b belong to a genuine side-port component. After joint pruning of other taxa, write g in (0,1) for routing toward that side, x in (0,1) for the ordinary prefix survival from the cycle top v to the side vertex, and ka,kb>0 for the actual probabilities that the respective copy pairs remain separate at their entry faces. Finite cut tails are included in ka,kb. The separate cut histories use private drivers.

An earlier aa or bb merge is incompatible with either mixed-first-cherry target. Conditional on separate pairs, all routing cases are as follows.

* If both a roots use the side arm and survive its private suffix separately, all four roots first pool at the side vertex. Their subsequent common ordinary prefix is exchangeable. It contributes equally to TX and TY, and equally to X and Y.
* If the a roots split, one root reaches the others only at v. Neither complete four-leaf tree can already exist below v. The additional compatible two-root forest is Y: a1 takes the side arm, a2 takes the other arm, and a1,b1,b2 make the specified nested triple on the prefix. There is no corresponding X history because a b root cannot escape its side arm.
* If both a roots use the other arm, neither requested complete tree or mixed triple can form before v.

Thus V(TX)=V(TY). The extra Y history has probability ka kb g(1−g)t(x). To see its exact per-labelled coefficient, put l=−log x. For three roots, the first specified pair merges at rate 1 while total rate is 3; the remaining pair then merges at rate 1. Hence

    t(x) = integral_0^l exp(−3s)[1−exp(−(l−s))] ds
         = (2−3x+x^3)/6 = (1−x)^2(2+x)/6 > 0.

No additional multiplicity is attached to this specified nested topology. A merged current root is never routed again as two original leaves. Equation (1) now gives

    J_ab = −ka kb g(1−g)t(x) < 0.                       (2)

All strictness is pointwise for each finite source; no uniform parameter margin or size bound is used. An unknown ancestral source above v cancels only at this observable, not at every forest coordinate.

## 4. A tree cut gives zero

If a,b lie in different child cut components of a tree vertex u, no mixed-colour merger can occur below u. Pure-colour merges are incompatible with TX and TY. Therefore only the four-singleton input can contribute at u. Its actual joint probability multiplies equal complete-tree coefficients in the label-blind ancestral source, giving

    J_ab = 0.                                         (3)

The two component interiors can be arbitrary admitted finite sources. For a two-cut-root rival, completion above its root is simply the stipulated unbounded ordinary population. No known root split, known cut kernel or hidden decoder is required to observe (3).

## 5. Fixed target, preselected panel, all two-cut-root rivals

Fix a strict target whose ROOT blob is a simple one-hybrid cycle. Assume its hybrid-descendant taxon block A0 and union S of side-port taxon blocks are both nonempty; they partition all original taxa. Root=LSA excludes the degenerate root bigon with every taxon below its sole child cut. Arbitrary admitted finite sources may occur inside the target's exit components.

For every a in A0 and b in S, pruning the other inputs combines consecutive ordinary cycle edges and leaves the configuration of section 3. Its prefix remains strictly positive in length, so J_ab is nonzero. These pairs form a complete bipartite graph on A0 and S and thus a connected graph on all taxa.

Any two-cut-root rival has a nontrivial taxon bipartition X|Y. Some A0/S pair crosses this bipartition: otherwise connectedness would force all taxa onto one side. For this pair, (2) is nonzero in the target and (3) is zero in the rival. Their complete four-leaf laws differ.

**Preselect**, before seeing any rival, one allocation for every unordered original taxon pair: two copies each of that pair and one copy of every other taxon. There are n(n−1)/2 rows, each with n+2 copies and all taxa positively sampled. Joint pruning gives every required four-leaf contrast. The distinguishing pair may depend on the rival because its row is already present. The target is fixed; each rival retains its own one tuple throughout. No cap on rival size, moving target, approximate equality or boundary source is used.

This establishes finite separation from the entire two-cut-root rival subclass. It does **not** establish separation from all original admitted rivals.

## 6. Provenance, reuse and boundaries

Source evidence: Full Pro's complete-comb proof, SHA256 `022c9db94bfea392ac4f1663002fc18465dab678de089ac867a832495d9de907`; Claude Code's separate review, SHA256 `f73302332cb6d6825f580b5acde38cc698ad1a6d962ad232cc2d4b27be12628e`. These source artifacts are credited by exact identity; this public note is an own derivation/review, not a republication of private correspondence or an assertion of independently replayed author computations.

The earlier [labelled two-root orientation calculation](https://github.com/Sodelin/Research-Commons/blob/09a7b2ccdf6df82a2668d19f2993479ff22a4016/research/2026-10-31-g4-no-upper-taxa-core-review/DERIVATION-AND-REVIEW.md) remains a separate result with its known-anchor/completion hypotheses. The present complete-tree observable removes that decoder for this contrast only; it does not import the earlier full parameter reconstruction through an arbitrary exterior.

The [original admitted-source correction](https://github.com/Sodelin/Research-Commons/blob/4911404fc5f1f928b05641efaf2700f289f3a651/research/2026-10-31-g4-galled-not-simple/SOURCE-DEFINITION-CORRECTION.md) explicitly permits multi-hybrid retained blobs. They are not silently replaced by simple cycles here. This note does not classify multi-hybrid root rivals, supply a general observable component cover, identify source words or the joint INDEPENDENT/COMMON realization, or prove original G4/G3. Semantic fixed-target forcing and any separately claimed effective construction/stopping theorem remain distinct obligations. There is no Lean-verification or novelty claim.
