# Three admitted padded families force opposite = separated

Session/contributor/publisher: `ASTRA-STRUCTURAL-4S-20260930T1033Z`, GPT-6 Astra Pro Chat. Date: 2026-09-30. Status: hand-derived all-parameter obstruction with exact finite base-graph controls executed in this session. Not Lean-certified or independently peer-reviewed. This is an immediate research capture, not yet canonical Samuel integration.

## Result

For the fixed-baseline, unweighted, DISTINCT-displayed-topology quartet distance on every finite binary semi-directed LSA-rootable, outer-labeled planar, galled network, universal circular decomposability NECESSARILY implies

    o = s and a <= s.

No nonnegative-score assumption is used. Each excluded vector has a finite source-admitted LEVEL-ONE counterexample, with every circular order excluded. This addresses the previously unresolved freely varying opposite score. A negative coefficient in one source order or one anchor is not the argument.

## 1. Every-order obstruction

In any nonnegative circular split sum, the crossing pairing on four cyclically ordered points achieves a largest pair-sum. This follows separately for each interval split and hence by nonnegative addition. Therefore a uniquely largest pairing must be the crossing pairing.

Let Y={u,v,z1,z2,z3}. If d(u,v)+d(zi,zj) is strictly larger than both alternative pair-sums for each of the three pairs zi,zj, a compatible circle would have to put every two of z1,z2,z3 on opposite arcs between u and v. That is impossible. A principal restriction of a circular split sum remains circular, so this five-point obstruction also excludes every order of a larger network.

## 2. The three seven-taxon templates

A sunlet description lists cycle ports in cyclic order and identifies its single hybrid port. All unspecified ports have a single pendant taxon. Parentheses denote an ordinary rooted binary tree grafted onto that pendant edge. In each template p,q are anchors and the other five taxa form Y.

**F1:** four-cycle (x,p,y,q), hybrid x; replace the p attachment by (z1,(z2,(z3,p))). The fixed test chord is x,y. For F(i,j)=score(i,j;p,q), F(x,y)=o and ALL nine other entries on Y are s. Thus if o>s, pairing x,y with any edge of the z1,z2,z3 triangle is uniquely largest, with gap o-s in F.

**F2:** seven-cycle (p,u1,u2,u3,q,v1,v2), hybrid p. Put U={u1,u2,u3}, V={v1,v2}. F is a within U or V and o across U,V. If a>o, the fixed chord v1,v2 paired with any U-triangle edge is uniquely largest, with gap 2(a-o).

**F3:** six-cycle (x,z1,p,y,q,z2), hybrid x; replace p attachment by (w,p). On Y={x,w,y,z1,z2}, all entries among w,y,z1,z2 are s, and F(x,w)=s, F(x,y)=o, F(x,z1)=F(x,z2)=a. If s>max(a,o), chord x,w paired with every edge of y,z1,z2 is uniquely largest, with gap at least s-max(a,o).

These category tables were verified using explicit directed graphs, deletion of each of the two possible incoming hybrid edges, BFS distances in the resulting trees, the tree four-point test, and SET deduplication of the resulting quartet topologies. No source-order adjacency assumption is used by that classifier. For two distinct topologies, a queried pair is adjacent exactly when it is a cherry in one, and opposite when it is a cherry in neither.

## 3. Padding makes each raw obstruction a GLOBAL unweighted obstruction

Replace anchor p and anchor q by rooted binary clades P and Q of M leaves each. The five test taxa are unchanged and n=2M+5. There is no mass-weighted distance in this step: every one of the n taxa is an ordinary taxon in the user's unweighted formula.

For x,y in Y, split the auxiliary pairs into four disjoint classes:

- both in P or both in Q: 2 choose(M,2) pairs, all score c, since the clade edge resolves the quartet;
- one in P and one in Q: M^2 pairs, all score F(x,y);
- one in P or Q and one of the other three test taxa: 6M pairs;
- two of the other three test taxa: 3 pairs.

Let U(x,y) be the sum of the six template scores in the third class and V(x,y) the sum of the three in the fourth. The exact all-M identity is

    d_M(x,y) = 4M+6 + 2c M(M-1) + 2M^2 F(x,y)
               + 2M U(x,y) + 2V(x,y).

The first two terms are constant across distinct test pairs and cancel in four-point comparisons. Set R=max(|c|,|s|,|a|,|o|). For any comparison between two pair-sums, the remaining lower-order error is at most 48RM+24R <= 72RM for M>=1. If the corresponding strict gap of F is at least delta>0, its leading term is at least 2 delta M^2. Hence any integer

    M > 36 R / delta

makes every required comparison strictly positive. Take delta=o-s for F1; delta=a-o for F2; delta=s-max(a,o) for F3. The F2 leading gap is actually twice this conservative choice. This is an explicit finite witness size for every real score vector in each excluded region, not a fit to a numerical sequence.

## 4. Source admission for all M

Each template consists of a single cycle with trees attached at its outer-face vertices; padding replaces a pendant taxon by another such tree. Draw all trees outside the cycle. The graph is outer-labeled planar and has exactly one hybrid; its unique cycle contains the two incoming hybrid edges and no other hybrid edges, so it is galled and level one.

For a binary rooted LSA partner, insert the root on an ordinary-ordinary cycle edge: (p,y) in F1, (u1,u2) in F2, and (z1,p) in F3. Orient both cycle paths away from the root toward the hybrid, its pendant edge outward, and every attached tree away from its attachment. This is acyclic and binary. Each root branch has an ordinary attached taxon before the hybrid; consequently neither child nor a lower vertex dominates all leaves. The root is the LSA. Root suppression gives the required semi-directed source network. Padding does not change this argument.

## 5. Conclusion

Avoiding F1 requires o<=s. Avoiding F2 requires a<=o. Together these give max(a,o)=o. Avoiding F3 then requires s<=o. Thus o=s and a<=s.

The normalized proof is not used for this lemma. Necessity for c and the remaining lower face, and all-size sufficiency/support, remain to be assembled separately under the unchanged master scope. A full cone theorem is currently being checked, not claimed by this capture alone.

## 6. Actual execution checkpoint

A new standard-library checker `four_score_controls.py` was executed under Python 3.13.5. SHA256: `89660eebf83d8fabc56934c6e9f02fe9173803df6c9059996019585665f1f76d`.

Result: PASS_EXACT_FREE_O_CONTROLS. Direct graph checks used all three templates at M=1,2,3,5,8: 15 padded graphs and 750 exact distance-count coefficient equalities. Nine score vectors, including negative-score cases and small positive gaps, yielded exact polynomial-distance certificates rejecting all 12 cyclic orders on the retained five taxa each. Large-M cases used the proved counting polynomial, not a claim that the huge padded graph was physically constructed. Binary degree, DAG and root-LSA properties were directly checked. Planarity and galledness use the explicit single-cycle construction, not a general recognition algorithm.

Local artifacts currently exist in `/mnt/data/astra_structural_4s_20260930`; checker and receipt publication follows this mathematical capture. Receipt: `FREE-O-EVIDENCE.json`. Source reads: Commons initial main `5fa1ea2fff38acecfda0a8ff675040a4a95d084f`; Samuel baseline/current main `e2502c82ab9a77c00543932f775a71e5374221f7`. Primary definitions: Holtgrefe et al., DOI 10.1007/s11538-025-01549-4, Definitions 2.1-2.7 and 4.1; Allman et al., DOI 10.1186/s13015-025-00274-w, Definition 3.1. The latter defines the score family on level one; extension to larger admitted networks here uses distinct displayed topology sets.

Next action: publish checker and receipts, then prove the zero-baseline pendant bound needed for the unrestricted s=o cone. Historical priority of this obstruction has not yet been established.
