# 0. Decision brief

**The proposed sequence 14,17,20,23 is a reasonable finite-size conjecture, but it cannot be the exact answer for every larger size.** It extends the reported values Q*(5)=5,Q*(6)=8,Q*(7)=11 by the rule Q*(n)=3n-10. A classical tree-count lower bound already contradicts that rule at n=34: at least 93 queries are necessary, whereas the rule gives 92. This does not locate the first actual departure; it could occur much earlier.

Contributor/publisher: Codex Work, QUERY-GROWTH-PATTERN-20260930. Source snapshot: Research Commons 6f1c4bfda8277c0ac666d8e252d64b81e912d237. MASTER-CLOSURE-STANDARD-20260930 accepted. This responds to Nolan's pattern, runtime and interpretation questions without taking over ASTRA-ENUMERATION-20260930-1430Z.

Scope: deterministic adaptive complete displayed-quartet support queries, no supplied circle or blob tree; output full nontrivial displayed-split union and any compatible circle, throughout the admitted finite source class. The tree subfamily alone suffices for the new obstruction. Evidence bands: high mathematical confidence in the elementary counting implication, with exact integer checks; author-reported computer-assisted finite values conditional on the existing source premises; no evidence for an eight-taxon runtime estimate. These are mathematical evidence descriptions, not clinical GRADE scores.

Highest-leverage findings: (1) three answer options do not imply three extra queries per taxon; (2) a linear number of output splits can still require superlinear identification queries; (3) the all-size +3 rule is refuted without eight-taxon optimization; (4) eight taxa remains a useful finite benchmark; (5) preserving the existing archive and obtaining a benchmark precedes any runtime commitment.

Next action: recover the owner's existing catalogue/certificate archive and streaming-replay handoff. After source validation, test the concrete depth-14 upper/depth-13 lower hypothesis, or prioritize a structural all-size bound; do not restart a census merely because a chat stopped. No large run is started by this note.

# Query patterns, tree counts and the eight-taxon benchmark

## 1. Abstract

We interpret the observed +3 sequence as a hypothesis about exact query complexity, distinguish it from experimental settings and tree split counts, and give an elementary all-size obstruction. There are (2n-5)!! distinct labeled unrooted binary trees. On this admitted subfamily every quartet query has only three possible answers; a depth-q decision tree has at most 3^q tree-input leaves. Hence Q*(n)>=ceil(log_3((2n-5)!!)), which is Omega(n log n). Exact integer comparison first rules out 3n-10 at n=34. The eight-taxon catalogue is reported complete but its minimax optimization and independent census replay are unfinished in the inspected checkpoint. No published timing supports a hours/days estimate.

## 2. Introduction

The master asks for an optimal strategy and matching impossibility argument at every finite size. A few consecutive exact values can suggest a valuable hypothesis, but they do not establish a recurrence. Eight taxa tests one next instance. It neither validates an all-size formula nor completes the biological observation-to-answer bridge.

## 3. Method

Read the current owner checkpoint, earlier checkpoint, committed certify.py and exact-minimum specification at the pinned Commons head. These are primary project records. No large catalogue or query certificate was rerun here. Independently derive the classical labeled-tree recurrence and its decision-tree consequence; execute integer comparisons with two different formulas for the tree count. This is targeted mathematical/source review, not an exhaustive literature review or a historical-novelty claim.

## 4. Findings and proofs

### 4.1 What each three counts

| Quantity | Meaning | Consequence |
|---|---|---|
| Three tree-quartet answers | ab|cd, ac|bd, ad|bc | At most 3^q transcripts for tree inputs after q queries |
| n-3 internal tree splits | Number of nontrivial edge bipartitions in one binary unrooted tree | Output size; does not count queries needed to locate those splits |
| Three controlled environments | Conditional graph-informed support protocol from the previous packet | Several or many quartet queries may be estimated within each environment |
| +3 between computed Q* values | Observed finite numerical difference | Hypothesis; not a consequence of the other three quantities |

For example, there are 945 seven-taxon binary trees. Six queries give at most 3^6=729 transcripts, so even the tree subfamily needs at least seven. The full admitted network minimum is reported as eleven. Thus the tree count is a lower bound, not an equality formula for the full class.

### 4.2 Counting admitted tree inputs

Let T_n be the number of labeled unrooted binary trees on n taxa. T_3=1. Such a tree with n-1 leaves has 2n-5 edges. Subdivide any one edge and attach leaf n; deleting leaf n and suppressing its former attachment uniquely reverses this operation. Consequently T_n=(2n-5)T_(n-1)=(2n-5)!!.

Every one of these trees is admitted: there are no reticulations, galledness is vacuous, a plane tree has all leaves on its exterior, and a rooting subdivision with taxon-bearing sides gives the required binary LSA-rooted partner. Different binary trees have different required split unions. A correct learner must distinguish them even though the output also permits any compatible circle.

Restricted to tree inputs, each query produces exactly one of three quartet topologies. Adaptive choice of the next quartet does not increase the answer branching factor. Any strategy using at most q queries has at most 3^q distinct tree-input leaves. Padding shorter paths if necessary gives the same bound. Therefore

    3^Q*(n) >= T_n,
    Q*(n) >= ceil(log_3((2n-5)!!)).

The mixed-network oracle can have more answer types; that does not weaken the restriction to tree inputs. By the factorial expression T_n=(2n-4)!/[2^(n-2)(n-2)!], log(T_n)=n log n+O(n), so this is an Omega(n log n) lower bound. No universal linear formula with a fixed slope can hold.

### 4.3 The proposed +3 pattern

| n | Owner-reported Q*(n) | Candidate 3n-10 | Tree-only counting lower bound |
|---|---:|---:|---:|
| 4 | 1 | 2 (does not fit) | 1 |
| 5 | 5 | 5 | 3 |
| 6 | 8 | 8 | 5 |
| 7 | 11 | 11 | 7 |
| 8 | Uncomputed | 14 | 9 |
| 9 | Uncomputed | 17 | 11 |
| 10 | Uncomputed | 20 | 14 |
| 11 | Uncomputed | 23 | 16 |
| 34 | Uncomputed | 92 | 93 |

Exact integer checks establish 3^92 < T_34 <= 3^93. The first contradiction from this particular counting bound, for n>=5, is n=34. Actual Q* could depart sooner. Neither this calculation nor the three observed matching terms establishes a finite range of validity. The universal assertion Q*(n)=3n-10 for all n>=5 is REFUTED; the n=8 conjecture Q*(8)=14 remains OPEN.

### 4.4 Importance and runtime of eight taxa

The owner's source checkpoint reports 145,845 seven-taxon profiles and 6,955,830 eight-taxon profiles, approximately a 47.69-fold increase. Available four-taxon queries increase from binomial(7,4)=35 to binomial(8,4)=70. Seven-taxon lower verification inspected 44,599,186 branches; this is a work count, not an elapsed-time measurement. The code reports elapsed seconds to result-n.json, but those result files and the full authored source/archive are absent from the inspected repository.

Minimax optimization searches possible query policies and adversarial branches. Runtime need not scale proportionally to catalogue size or to the three additional conjectured query levels. No trustworthy eight-taxon time estimate follows from these counts. Establishing a policy and lower certificate is also different from executing that policy once on an unknown input. A low-query policy can be much cheaper to use than to discover.

Q*(8)=14 would require both a depth-14 policy covering the complete admitted census and a lower certificate ruling out every depth-13 policy. A depth-13 policy or an impossibility certificate for depth fourteen would refute that conjecture. The existing exact procedure guarantees eventual finite termination in principle, not a practical wall-clock bound.

## 5. Conclusion

Pattern recognition was a valid first step. The observed linear rule is plausible locally and impossible globally. An eight-taxon optimum would add one exact benchmark and could expose hard configurations, but it is not a prerequisite for using the previously proved conditional experiment-count component. The full exact function and biological master remain open.

## 6. Deconstructive analysis

Separate source size, output size, oracle queries, experimental environments, loci and optimization runtime. The same number appearing in two of these quantities supplies no theorem relating them. An O(n)-sized split union can encode n log n bits through its labeled composition.

## 7. Reconstructive analysis

An all-size formula needs a uniformly valid upper strategy and matching admitted hard instances. A proposed +3 extension would need both directions of such a recurrence. The tree count proves that a universal upper strategy spending only three extra queries per taxon cannot exist under this information contract. It does not prove a specific lower bound on every individual increment Q*(n+1)-Q*(n).

## 8. Middle-out synthesis

Use finite exact runs to discover adversarial structures and test candidate strategies; use structural proofs to control all sizes and avoid endless brute-force escalation. Recovering the existing handoff is the immediate computational step. Structural growth analysis is a complementary proof route, preserving the enumeration owner's lane.

## 9. Glossary

- Taxon: one labeled terminal; n counts terminals, not hybrids.
- Q*(n): smallest worst-case deterministic adaptive exact quartet-query budget for the declared output.
- T_n: number of labeled unrooted binary trees on n taxa.
- Double factorial: (2n-5)!!=1*3*5*...*(2n-5).
- Transcript: sequence of observed answers along an adaptive query path.
- Certificate: replayable upper policy or lower impossibility proof.

## 10. Bibliography and evidence

- [Owner seven-taxon certificate and eight-taxon status](https://github.com/Sodelin/Research-Commons/blob/6f1c4bfda8277c0ac666d8e252d64b81e912d237/research/2026-09-30-astra-exact-enumeration/SEVEN-TAXON-CHECKPOINT.md). Author-reported actual execution; primary project record.
- [Earlier six-taxon checkpoint](https://github.com/Sodelin/Research-Commons/blob/6f1c4bfda8277c0ac666d8e252d64b81e912d237/research/2026-09-30-astra-exact-enumeration/CHECKPOINT.md). Superseded on seven-taxon status by the record above.
- [Committed solver/checker](https://github.com/Sodelin/Research-Commons/blob/6f1c4bfda8277c0ac666d8e252d64b81e912d237/research/2026-09-30-astra-exact-enumeration/certify.py). Inspected, not executed without its catalogue.
- [Exact finite minimum specification](https://github.com/Sodelin/Research-Commons/blob/6f1c4bfda8277c0ac666d8e252d64b81e912d237/research/2026-09-30-query-resumption/EXACT-MINIMUM-THEOREM.md). Conditional uniformly computable minimax; not an efficient runtime theorem.
- [Controlled experiment and normalization packet](https://github.com/Sodelin/Research-Commons/blob/6f1c4bfda8277c0ac666d8e252d64b81e912d237/research/2026-09-30-normalization-effects/REPORT.md). Different resource and additional control-map assumptions.

The labeled-tree recurrence and transcript bound above are elementary classical arguments, derived in full here; no novelty or new general lower-bound technique is claimed.

## 11. Process-integrity assessment

Verdict: high fidelity for this bounded source/arithmetic question; external proof review remains pending. Current primary records were pinned and read, stale seven-taxon status was superseded, and reported execution was separated from checks run here. Both recurrence and factorial tree counts were compared using exact integers. The source review was targeted rather than systematic; AMSTAR-2 and trial RoB instruments do not score this combinatorial derivation. Fixes: obtain the full archive, verify its census/certificates, and retain measured timing and resource metadata before predicting runtime.

## 12. Robustness assessment

Verdict: the all-size linear conjecture fails independently of the network census and its expensive optimizer. A source-class change excluding many labeled trees, supplied topological side information, or an observation that conveys more than the declared quartet answers would change the counting problem. Adaptive query selection does not evade it. A mistake in a finite numerical scan would not remove the asymptotic Omega(n log n) obstruction; the scan only locates this bound's first finite crossing. Meta-analysis effect-size models, I-squared and funnel tests are inapplicable. No claim about the exact eight-taxon value or its runtime is inferred.

## 13. Zotero integration

Save this Markdown as a research note linked to the owner checkpoint and exact-minimum specification. Tags: phylogenetics, exact-query, decision-trees, hypothesis-refuted, computational-status. Relate the environment-count packet under a separate resource-comparison link. Do not label the next conjectured values as observed results. Commons is the current shared workspace; no retired notebook or Zotero database is modified here.

## 14. Appendix and checkpoint

Run `python growth_check.py` from this packet. It checks two exact tree-count formulas through n=100, records the first contradiction and the displayed lower bounds, and reports the profile-growth ratio without turning it into a runtime estimate. `growth-checks.json` is the actual execution receipt. No census, minimax, certificate replay, Lean run or background job was performed here.

Component completed: interpretation and universal +3 refutation. Master unresolved: exact Q*(n), Q*(8), complete archive handoff and biological downstream inference. One next action: recover/preserve the original enumeration archive and then benchmark its proposed streaming replay.

### Latest steering: bounded enumeration rather than more pattern analysis

Nolan subsequently clarified that the immediate question is how far a reportedly restarted enumeration should run. The pattern analysis above is preserved as completed work, not a request to allocate more computation. Recommended endpoint: preserve the existing through-seven certificates and eight-taxon census, validate the eight-taxon handoff, and optionally certify Q*(8); do not automatically escalate to nine taxa. Eight-taxon optimality is required to claim an exact answer at eight, but not to use the completed conditional normalization/control component or the existing asymptotic query theorem. An all-size exact formula cannot be established just by indefinitely enumerating successive sizes. No elapsed-time prediction is justified by the available records. The running owner should preserve elapsed time, memory, explored states, best lower/upper bounds and exported checkpoints so continuation can be assessed without losing progress. No new enumeration was launched here.
