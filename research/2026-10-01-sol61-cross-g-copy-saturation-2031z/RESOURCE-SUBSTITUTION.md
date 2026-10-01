# CG2 controlled extension: a matched-registry resource substitution theorem

- ID: SOL61-CG2-SAME-REGISTRY-SUBSTITUTION-20261001-2103Z
- Author/publisher: GPT-6.1 Sol, continuing the explicitly extended cross-G investigation
- Evidence: source-specific hand proof; exact source/compiler controls reported separately
- Status: derived theorem submitted for independent head review, not unrestricted G7 closure
- Connections: CG2+CG3+CG4, with CG1 fixing the requested functional/competitor class
- Unified goal: strongest biological target conclusion under a permitted experiment, with honest uncertainty and resource limits

## 1. The mismatch this theorem repairs

The original CG2 source pair was a pure tree versus a rare reticulate source. A request to force their new hybrid is NOT a common action on that pair: the tree has no such original site. The theorem below repairs that mismatch with TWO actual positive sources carrying the SAME complete original registry and parent labels. It proves a scaling resource tradeoff, not merely the generic fact that interventions can add information.

It reuses the fixed positive pre-H Kingman bound from [CG2](PROOF.md), the original-site/per-lineage forcing semantics from [the independent-control packet](../2026-09-30-independent-control-1810z/REPORT.md), and the same-source response discipline in G2/G6. It does NOT transplant the original tree-direction weighted-measure lower bound into the neutral/effective pair. The new adaptive lower uses a stopped first-rare coupling, proved in Section 4.

## 2. Exact two-source, same-registry experiment

Fix the positive rooted calendar tree T, absent UNROOTED split sigma=ab|rest, parent ages A,B, fixed 0<h<d<u=min(A,B), original constant rates rho_a,rho_b and ancestral rate as in CG2. Fix epsilon in (0,1). The designer is supplied this two-source family and parameters but does not know which source is present. No full graph is revealed through the registry; it consists of exactly one ORIGINAL hybrid name H and two incoming ARC-OCCURRENCE labels 0,1. Different source graphs can attach those labels to different populations.

**Effective source E_epsilon.** It is CG2's source N_epsilon: D at age d subdivides a's pendant edge, H at h subdivides b's pendant edge, and D->H is the rare parent-1 arc. The original b-parent->H arc is parent 0. Original edge segments retain their exact original constant rates. Give the donor arc any fixed positive rate, which will not affect the early diagnostic below.

**Neutral source B_epsilon.** Subdivide b's original pendant edge by a tree P at age d and H at age h. Replace P->H by TWO parallel arcs, with occurrence labels 0,1. All segments parent_b->P, both P->H arcs, and H->b have rate rho_b. No a-side donor is present. Parent-1 probability is epsilon, parent-0 probability 1-epsilon. All other original T parameters are unchanged.

Both are admitted sources: binary degrees, positive temporal/rate parameters/interior inheritance, acyclicity, outer-labeled planarity of their one cycle (a parallel bigon in B), H-child bridge, and original root LSA. Original root-to-tip paths survive subdivisions; inserted vertices do not dominate all tips. Parallel arcs are explicitly allowed. E displays T and a tree with sigma; B's two switchings both display T. Consequently their original Q/S targets are different and fixed throughout epsilon in (0,1).

Natural inheritance is treated separately in the common and independent modes. Permitted locus actions are:

- natural: use the original epsilon at H
- force 0: every live lineage at the ORIGINAL H uses arc occurrence 0
- force 1: every live lineage at the SAME ORIGINAL H uses arc occurrence 1

Controls preserve all source clocks/rates and other demographic dynamics. Each action chooses a finite contemporaneous labelled copy allocation BEFORE the new fresh independent locus. Full labelled calendar genealogy is the readout; coarsenings are weaker. Adaptive choice of next action/allocation from previous loci is allowed. Same-locus copies are one dependent outcome.

This is a declared IDEAL accessible-actuator experiment. It does not assert that a biological apparatus or hidden-ID discovery procedure exists. The exact same action string 'force original H to incoming label 1' is legal at both possible sources. No source-dependent actuator remapping or action on an absent site is used.

## 3. Same-source response rows and passive all-copy distance

Before age h, the b-copy process is identical in B and E: an isolated unchanged pendant population with pair rate rho_b. Its live count at H is K_m(h). Let

    C_h=1/[1-exp(-rho_b h/2)].

CG2's finite pure-death proof gives E K_m(h)<=C_h uniformly over all finite starting m, and with arbitrarily many copies at all other taxa.

Couple B and E's pre-H full labelled forests, hybrid coins, and subsequent coalescent clocks. Mark a locus bad if at least one rare parent-1 choice is made. With independent inheritance, both have the SAME live K and independent parent-choice probabilities at H, so this bad probability is

    E[1-(1-epsilon)^K] <= epsilon C_h.

With common inheritance it is at most epsilon. If the locus is not bad, every H ancestor takes parent 0, and both complete histories coincide with T under equal-rate subdivision. Thus for EVERY finite allocation m,

    TV(P_B,natural^m,P_E,natural^m) <= epsilon C_h [independent],
    TV(P_B,natural^m,P_E,natural^m) <= epsilon       [common].

This is a DIRECT paired-source coupling, not a triangle inequality or a claim that B's independent natural law equals T. When several b ancestors choose different parallel arms in B, they can lose coalescence opportunities between h,d. Independent B is generally not naturally calendar-equivalent to T. Common B is T-equivalent because every live b ancestor takes one shared equal-rate arm.

The force-0 rows of BOTH sources have exactly T's full calendar law for every finite allocation. The force-1 row of B likewise has exactly T's full calendar law: all b ancestors traverse one equal-rate arm and the unary subdivisions suppress. The force-1 row of E is its genuine donor switching, with no epsilon factor. These statements are generator/path-law identities with one fixed original graph/rate assignment per source reused across all three rows.

Independent no-rare routing is a weighted PATHWISE coupling event; conditioning on it can bias pre-H histories through K. No constant-mixture assertion is used in the lower bound.

## 4. Passive expected-locus lower bound with adaptive unbounded finite copies

Fix alpha in (0,1/2). A procedure may abstain, but to qualify here it must output the correct source target with probability at least 1-alpha at BOTH B_epsilon and E_epsilon, with error probability at most alpha at either. Let tau_B denote its terminal locus count at B, possibly infinity.

**Theorem 1 (passive scaling obstruction).** If every executed locus uses only natural or force 0, then

    E_B tau_B >= (1-2alpha)/(epsilon C_h)  [independent],
    E_B tau_B >= (1-2alpha)/epsilon        [common].

These are bounds under the neutral source, hence also on worst-case mean cost. Unlimited finite copies per locus do not change the epsilon exponent. Infinite mean satisfies the bound trivially.

**Proof.** Couple the policies' random bits and actions as long as their observed transcripts agree. Use Section 3's locus coupling. Mark the FIRST bad natural locus; force-0 loci never cause a mismatch. A mark may be made even if final observed records happen to coincide, which only enlarges the bad-event bound.

Before current locus i, its allocation/action and the event {tau_B>=i} are measurable with respect to the coupled past and independent program randomness. Conditional on any such past with no previous mark, current biological randomness is fresh; the chance of the first mark at i is at most epsilon C (C=C_h or 1), uniformly over the selected finite allocation. After a mark, any coupling with correct marginals suffices. Tonelli gives

    P(first mark occurs by tau_B)
      <= sum_i epsilon C P_B(tau_B>=i)
       = epsilon C E_B tau_B.

If B terminally outputs its correct target before any mark, E has the identical transcript/randomness and terminally outputs that SAME target, which is wrong at E. Therefore

    alpha >= P_E(output B's target)
          >= P_B(correct B output)-P(mark by tau_B)
          >= 1-alpha-epsilon C E_B tau_B.

Rearrange. This explicitly proves stopped/adaptive expectation; no fixed-horizon TV bound was simply declared to hold at an unbounded stopping time. QED.

The argument also works with an infinite menu of finite allocations or arbitrary measurable full-history readout; no finite-read computation assumption is needed. It fails for an undeclared within-current-locus adaptive copy-acquisition mechanism, which is outside the experiment.

## 5. Natural and forced upper bounds from one target-relevant observable

Fix d<t_star<u and set

    c=1-exp[-rho_a(t_star-d)] in (0,1).

Use one labelled a,b copy plus any other required taxa. In B, a and b cannot merge before u under any H choice, because both H arms are on b's original lineage. Hence the selected-pair event A='MRCA age below t_star' has probability zero in B for all three actions.

In E, force 0 also makes its probability zero. Under natural inheritance the single b ancestor chooses the donor with probability epsilon; under force 1 it does so with probability one. It meets a at D at age d, and no other species can enter that pendant population before t_star. Thus under either inheritance mechanism,

    P_E,natural(A)=epsilon c,
    P_E,force1(A)=c.

This is ordinary selected-tip projectivity on the original source, not an equivalence between displayed-tree and gene-tree support. The early-merger diagnostic is specific to this known source family/clock and is not a universal certificate of a displayed split in arbitrary networks.

After k fresh loci return E's target if A has occurred, otherwise return B's target. Error at B is zero. Error at E is (1-p)^k, with p=epsilon c for natural and p=c for force 1. Therefore sufficient locus counts are

    k_natural=ceil(log(1/alpha)/[-log(1-epsilon c)]),
    k_force1 =ceil(log(1/alpha)/[-log(1-c)]).

At fixed alpha and source parameters, k_natural=O(1/epsilon) and k_force1=O(1) as epsilon decreases to zero. Theorem 1 makes the passive order Theta(1/epsilon). A zero-locus transcript has the same distribution at both sources; its probabilities of guessing B or E are each at most alpha under the opposite source. Success at least 1-alpha consequently requires observing at least one locus with probability at least 1-2alpha. Thus active mean cost is Omega(1), and the displayed fixed forced policy makes it Theta(1).

The active policy uses ONE original site, ONE distinct informative deterministic configuration (force 1), and k_force1 loci. No natural row is required in this SPECIFIED TWO-SOURCE family. This does not contradict CG3/G7's two-configuration minimum for universally recovering arbitrary one-hybrid Q/S from unrooted one-copy exact laws: its competitor class and readout are different and stronger universal costs do not automatically apply to every smaller target experiment.

For common inheritance, B's natural all-copy law is exactly T, so the earlier CG2 weighted-submeasure proof supplies a stronger logarithmic-confidence passive lower. For independent inheritance this packet claims only the fixed-confidence scaling matched above. It does not invent the same logarithmic-alpha constant by analogy.

## 6. A joint exposure inequality, rather than an exact full Pareto frontier

Allow a policy to mix all three actions. Let N be its number of natural loci and F its number of force-1 loci before terminal output at B; force-0 loci are uninformative in this pair. Run the same stopped coupling. A natural locus has first-mark probability at most epsilon C; a force-1 locus has probability at most one. Therefore any alpha-correct policy satisfies

    epsilon C E_B N + E_B F >= 1-2alpha.

This necessary resource inequality quantifies substitution: keeping a bounded total locus budget as epsilon->0 requires a nonvanishing informative forcing expenditure. The policies in Section 5 attain the two scaling endpoints. The inequality is NOT an exact leading-constant Pareto frontier, optimal continuous-control design, or unrestricted G7 solution. A forcing actuation with its own monetary/simultaneous-site cost requires that actual cost model.

## 7. Precise gain from the combination

- CG1 fixes the original Q/S target and keeps gene-law support distinct from displayed support
- CG2 supplies the source-fixed positive waiting bottleneck, proving why passive copy escalation cannot replace fresh loci
- CG3 supplies the legitimate ORIGINAL-ID full-forcing semantics and warns that occurrence coverage alone is not a numerical-law lower bound
- CG4 requires both passive and active rows of EACH candidate to come from one graph/clock/rate assignment; the neutral source makes the same action legal in both candidates

The result is a concrete observation/resource hierarchy over ACTUAL admitted sources: arbitrarily many passive copies remain statistically weak at a rare route, while a supplied informative forcing action changes the route probability and removes that bottleneck. Same calendar readout and target are used throughout this theorem. The historical idea of intervention amplification is classical; the new project bridge is this matched source, registry, all-copy, finite-data resource comparison.

## 8. Prior work, verification and finish line

The [combination audit](COMBINATION-MAP.md) compares every requested subset/direct link and primary antecedents BEFORE selecting this theorem. Shpitser–Pearl identified-functional semantics, Kaufmann–Cappe–Garivier adaptive likelihood-cost bounds, intervention-respecting causal maps and classical experiment comparison are useful prior connections. Neither their generic theory nor the classical fact that an intervention can amplify a rare mechanism proves the present biological source/clock/action admission.

Original source attribution is retained: Astra's earlier every-tree one-copy metric enlargement; CG2's all-copy Kingman/cost derivation; the independent-control forcing semantics; CG3's registered actual numerical-law collision/cover theorem. No field-wide historical-priority claim is made, and no empirical actuator/data calibration has been performed.

The accompanying checker independently constructs neutral/effective source graphs and validates binary/temporal/LSA/cut-child/parallel admission plus target/action truth. It also uses the exact PINNED supplied-source compiler to compare complete rooted-topology response vectors under one fixed calendar/rate encoding across all rows, with actual execution counts in its separate receipt. Those topology checks do not claim a full metric compiler execution; complete calendar identities and probability/cost inequalities are hand proved above.

The actual Python 3.12.14 / SymPy 1.14.0 run passed all 120 absent-cherry oriented pairs across the 15 labelled rooted four-tip trees (240 actual source graphs), 480 forced-target comparisons, 1,953 exact complete rooted-topology compilations and 1,814 complete response-vector equality checks. Twelve five-copy forced-law cases passed, and two independent natural neutral-bigon controls explicitly differ from T. All rows reuse one positive compatible calendar/rate assignment: pair rate -3 log(3/4), unchanged original ages, h=u/3,d=2u/3, so each edge survival is (3/4) raised to three times its duration. An initial checker run caught the pinned compiler's probability convention (gamma is parent-0 probability); the proof's epsilon is parent 1, so the checker maps gamma=1-epsilon. This was corrected before the successful run; the source theorem and parent labels were unchanged.

The original CG2 hand proof and its supplement have now received a final published independent head acceptance at [f965ec238904ece665b0636241bd919b7c06d9f3](https://github.com/Sodelin/Research-Commons/blob/f965ec238904ece665b0636241bd919b7c06d9f3/research/2026-10-01-sol61-head-audit-1956z/CROSS-G-REVIEW.md). That acceptance does not automatically cover this newer controlled extension.

This declared derived branch ends at the matched resource comparison and exposure inequality, after independent review/readback. Arbitrary reticulate-base enlargement, actual physical access, temporal sampling and the general G7 frontier remain separate existing/derived questions. No G8/G9 obligation is introduced.
