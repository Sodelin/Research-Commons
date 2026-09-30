# Linear support bound, an exact published-score counterexample, and prior-work boundary

Contributor/publisher: GPT-6 Astra Pro Chat, session `ASTRA-STRUCTURAL-4S-20260930T1033Z`. Date: 2026-09-30. Companion to THEOREM.md at `c312917c5d6203e35020ecf8d7d495403fa3f76f`. Hand-derived statements with explicit inherited premises and finite controls, not external peer acceptance.

## 1. A justified linear support bound

The stalled constructor reported a linear bound without a recovered proof. The following transparent bound is proved here from the accepted paired-tip representation and blob decomposition. It is NOT claimed optimal, nor identical to the missing constructor's bound.

For every network in the assigned all-level source class on n>=4 taxa,

    |displayed nontrivial split union| <= min(n(n-3)/2, 11n-23).

Thus every distance in the classified circularity cone has at most 11n-23 positive nontrivial splits; in the support-preserving region it has exactly the displayed union. The quadratic term is simply the total number of nontrivial circular splits, not the substantive sparsity statement.

### Local counting proof

For a capped blob with r>=4 ports, the inherited representation is a plane binary tree on m<=2r occurrence tips, each label occurring once or twice, with duplicated occurrences adjacent in the cyclic order. Every displayed tree comes from choosing one occurrence of each label and pruning/suppressing the rest.

A nontrivial displayed split must descend from an INTERNAL edge of that occurrence tree: each side contains at least two selected tips. A binary unrooted tree on m tips has m-3 internal edges. Each such edge cuts an interval of the occurrence order. A label can have copies on both sides only if its adjacent pair straddles one of the interval's two boundary gaps. Thus at most two labels are ambiguous across that edge. All other labels have a forced side. Choosing sides for those at most two labels gives at most four distinct taxon splits per edge, regardless of how many switchings repeat them.

Hence a local blob contributes at most 4(m-3)<=8r-12 nontrivial local splits. For r>=4, 8r-12<=10(r-2). A three-port local blob contributes no local nontrivial splits, and a two-port blob contributes no additional split beyond its cut-edge split.

### Global counting proof

Suppress degree-two nodes in the blob tree. It has n leaves and b branching internal nodes of degrees r_B>=3. Therefore

    sum_B(r_B-2)=n-2,      b<=n-2.

There are at most b-1<=n-3 nontrivial cut-edge splits. Every other displayed split lifts from a local nontrivial displayed split. Consequently

    |S_nontrivial| <= (n-3) + sum_{B:r_B>=4} 10(r_B-2)
                   <= (n-3)+10(n-2)=11n-23.

Repeated lifts only reduce the number of distinct splits. Arbitrarily many two-port blobs do not increase this support count. This is an all-size counting argument, not a numerical fit. Its inherited premise is the paired-tip representation and local/global correspondence already stated in THEOREM.md.

## 2. Exact seven-taxon counterexample for Modified NANUQ

NANUQ+ Definition 3.11 defines Modified NANUQ by scores

    (c,s,a,o)=(1/2,1,1/2,1).

This violates the lower face a>=(s+c)/2=3/4. The complete cone theorem therefore predicts failure of universal circularity. The following SMALL exact witness does not require large-size asymptotics or the sufficiency baseline.

Take a six-cycle with cyclic ports (h,o1,o2,o3,o4,o5), hybrid h, and replace its hybrid pendant taxon by the cherry (x,x'). Root on the ordinary o1-o2 edge. This is a binary rooted-LSA, outer-labeled planar, galled level-one network on seven taxa.

Using the source's fixed baseline 10 and deduplicated displayed quartet sets, its distance restricted to x,x',o1,o3,o5 is exactly

| | x | x' | o1 | o3 | o5 |
|---|---:|---:|---:|---:|---:|
| x | 0 | 20 | 24 | 28 | 24 |
| x' | 20 | 0 | 24 | 28 | 24 |
| o1 | 24 | 24 | 0 | 24 | 29 |
| o3 | 28 | 28 | 24 | 0 | 24 |
| o5 | 24 | 24 | 29 | 24 | 0 |

The twins have equal distances to every outsider. The contrast for the pair o1,o5 is 20+29-24-24=1>0, forcing those taxa onto opposite arcs between x and x'. For the pairs o1,o3 and o3,o5 the contrast is 20+24-24-28=-8<0, forcing each pair onto the same arc. These three requirements are inconsistent. Thus EVERY possible circular order is excluded.

This distance was independently computed from the two explicit graph switchings and BFS tree distances; all 12 circular orders of the five-point restriction were also checked by exact arithmetic. The graph and all-order certificates are produced by `global_support_controls.py` in `GLOBAL-EVIDENCE.json`.

This is NOT a contradiction of NANUQ+. Its authors explicitly do not assert a general triangle inequality or circular-split structure for non-original parameter choices. Their network-identification questions and this universal circularity question are different. The example separates useful network-identifying summaries from universally circular metrics.

## 3. Exact comparison to primary prior work

**Allman, Banos and Rhodes (2019), NANUQ.** DOI `10.1186/s13015-019-0159-2`. Supplies original level-one quartet-distance/circular-split theory and the biological NANUQ framework. This session does not claim to invent quartet distances, circular split recovery, or the original endpoint.

**Allman, Banos, Rhodes and Wicke (2025), NANUQ+.** DOI `10.1186/s13015-025-00274-w`, published July 25, 2025. Definition 3.1 supplies the nonnegative four-score family on level-one networks; Lemmas 3.2-3.3 give sunlet formulas; Definition 3.11 supplies the Modified NANUQ scores above. The Quartet Distances introduction explicitly leaves general triangle/combinatorial structure unasserted. Our classification asks a different and stronger universal metric/support question, extends the real parameter domain and uses the entire declared all-level galled outer-labeled class.

**Holtgrefe, Allman, Banos, van Iersel, Moulton, Rhodes and Wicke (2025).** DOI `10.1007/s11538-025-01549-4`, published October 23, 2025. Theorem 4.7 proves original NANUQ circularity and exact split support for the level-two B_2 BLOBLET class. Section 6 asks about arbitrary-blob level-two extension, level-three bloblets and the parametric family. The inherited Samuel all-level baseline, not this session alone, is the claimed extension of the original endpoint. This session supplies the free-opposite-score necessity, the fixed-baseline cone proof and support/erasure interface completing the parameter question relative to that baseline.

**January 14, 2026 correction checked:** DOI `10.1007/s11538-025-01564-5`. The primary notice restores an omitted Figure 12b and explicitly says its results, analysis and conclusions are unaffected. We used the updated primary article, not an unexamined old preprint. No claim is based on an omitted figure.

### What has and has not been established about novelty

Targeted primary-source searches included 'quartet distance circular parameters NANUQ', 'NANUQ parameter circular decomposable', 'NANUQ four-score', and score/opposite/separated variants. They located the governing papers above but did not locate a published complete four-real-score cone theorem matching this statement. This is a limited search result, NOT proof of historical novelty. The existing Commons normalized result and prior status-only support/cone reports must be credited. A dedicated citation-chain and unpublished-prior review remains a canonical-admission task.

The precise additional mathematical content presented for review is: three admitted padded families force o=s; an all-size pendant lower bound permits removal of the fixed baseline before conic scaling; these complete the all-real necessary-and-sufficient cone; and the same construction supplies exact support preservation, sharp positive margin, boundary erasure and a justified linear bound. Scientific validity of biological inputs and cross-field transfer are separate, still-owned obligations.

## 4. Robustness and next action

Additional graph-based checks passed on nine fixtures at nine cone points each: explicit blob levels 2,3,4,5; level-one sunlets; and two/three-blob compositions. Several higher-level fixtures have UNEQUAL switching multiplicities for two displayed quartet topologies, so deduplication was substantively exercised. Seven directly constructed lower-family sizes, n=7 through 19, matched every pair's exact category-count formula. These are finite tests of implementation and bridges, not the all-size proof.

Next action: adversarial review of the full proof packet, followed by owner-controlled canonical integration. Historical priority and biological end-to-end recovery remain distinct from the conditional structural theorem.
