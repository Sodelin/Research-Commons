# G3 v4: joint five-copy shape covariance, beyond the quartet hierarchy

**New result:** One full-support rational law on 16 same-taxon copies passes every earlier quartet screen through v3 and has the exact ordinary Kingman four-copy marginal, but the joint law of two disjoint five-copy shapes yields a sound original G3 NO. In a 34-block hypothetical extension, all three coordinate frequency variances are individually positive; a mixed shape contrast nevertheless has negative variance.

This is a source-universal partial rejection screen at the given natural observation interface, not complete G3 recognition, physical sufficiency, a strict-boundary result, or a Lean proof. The probability argument is standard; the distinguishing fully specified topology fixture and exact checks are this packet's advance. Prior G3 notes include scalar quartet upper and lower-modulus constraints and Hankel/rank work; this packet does not assert historical novelty or passing every such published scalar restriction.

## Exact observations

Use a supplied natural, completed, rooted unranked labelled topology-response row resolving the restriction to 16 same-taxon copies. Retain other original taxa and observations unchanged; as in the [original-observation quartet NO](https://github.com/Sodelin/Research-Commons/blob/f4ba57788564192f4705309b0aeb2cce404e35db/research/2026-10-06-dot-g3-original-quartet-whole-fibre-no-0454z/README.md), only a same-taxon projection is read. The v4 checker actually needs only the joint three-by-three shape probabilities on **two disjoint groups of five**, and uses 16 on the fixture so the preceding four-quartet checks can be applied to the very same input. No five-copy shape data may be inferred if the supplied observation map hides it.

The three rooted nonplane shape classes on five leaves are: (0) comb; (1) root singleton plus balanced four-tip subtree, denoted 1+(2+2); (2) root split 2+3. A random four-leaf restriction inside one five-group balances with respective probabilities 0, 1/5, and 3/5. These are different summaries: the vector retains which five-copy shape occurred, not just its average balanced quartet contribution.

## Covariance certificate and finite witness

Under a purported original source and one fixed physical tuple, let the indicator vector X_i mark the shape of group i. Write p for its marginal probability vector and J for the observed two-group joint probability matrix. Natural within-taxon equivariance and [same-source unranked all-panel projectivity](https://github.com/Sodelin/Research-Commons/blob/e43167ff700bd101ecdf581764c870c2f3308edf/research/2026-10-11-dot-accepted-connected-union1591-1247z/source-store/4936fb211505d9c5961256ba4f1a4c63db0065c7c94ccadf3fcd67a320f270c3.lean) hold separately in either natural inheritance mode. They force E[X_i]=p and E[X_i X_jᵀ]=J for distinct groups i,j in **every** larger hypothetical sample from the same source. This does not require independent grouping, a changed graph/root, or a copied or independently fitted physical tuple.

For N groups, write their shape frequency vector as Y_N. Diagonal group terms contribute diag(p), off-diagonal terms contribute J, so
```
Cov(Y_N) = J − ppᵀ + (diag(p) − J)/N.
```
This matrix must be PSD for every N; taking the limit forces J−ppᵀ PSD. A negative principal minor in the limit implies a finite negative minor, so once the limiting screen fails the implementation only doubles hypothetical N until a rational finite witness is found. A pass is UNKNOWN. Generalization to any finite rooted-topology shape alphabet on equal disjoint same-taxon groups is immediate from the vector calculation; this implementation checks three shapes exactly.

For the fixture at **N=34**, every individual variance is positive, but the contrast −Y_N[comb]+22 Y_N[1+(2+2)] has variance
```
−86858988034997/301850452178730000 < 0.
```
That contradiction concerns a hypothetical extension to 170 copies, not additional observations or a lab procedure. It proves a finite multivariate improvement over testing only the three coordinates at that same N, separate from the improvement over the earlier four-copy balanced-only hierarchy. The latter's PSD tests can pass because they consume a different statistic.

## Full-support rational fixture

Uniformly relabel the leaves in each shape-based component. Use weights:
 
* u=1/1000 on the uniform distribution over all labelled rooted nonplane binary 16-tip trees;
* w=394513/1830375 on the tree made by taking a 7-tip core (a 3-tip comb joined to a 4-tip comb) and attaching nine singletons successively above it;
* (1−u−w) times 7/13 and 6/13 on two comb-pair trees, with root sizes 7+9 and 8+8, respectively.

The uniform component makes all 6,190,283,353,629,375 labelled topologies strictly positive. These are mathematical input distributions, not preparations. Every compatible lower row is specified by literal restriction of this same distribution. In the core component, balance of four leaves needs a 2+2 split inside the seven core leaves, so its balanced probability is 18/C(16,4)=9/910. The five-tip shape 1+(2+2) needs four balanced core leaves and one of the nine outer leaves, hence has probability 18·9/C(16,5)=27/728. Two disjoint such groups would use eight core leaves and are impossible. Neither comb-pair base component has this five-tip shape. Thus its pair probability comes solely from the small uniform component, while its marginal gets a positive contribution from the core.

The core weight was chosen to give one-quartet balanced probability exactly 1/3; permutation symmetry then identifies its entire four-copy distribution with the ordinary Kingman four-copy topology law. The actual 4-group moments also satisfy all prior scalar v1/v2 inequalities and all v3 principal minors, **strictly**, as the saved output shows. Meanwhile the five-shape marginal of 1+(2+2) is 120469/14805700, and its same-shape joint probability is only 223/10210200. Covariance is negative. The finite mixed-contrast bound above is stronger at its fixed copy count because even this indicator's own finite variance is still positive at N=34.

## Replay

From workspace root:
```sh
set -o pipefail
python -B g3_obstructions_v4/obstruction.py | diff -u g3_obstructions_v4/fixture_result.json -
```

The standard library checker uses exact fractions and a generalized v2/v3 root-split count. The uniform law on 16 labelled topologies restricts to the uniform law on 10 because each lower tree has the same number of edge/stem-insertion extensions; this allows compressed count on two groups of five. Component-specific checks enumerate group allocations, not all labelled trees. Replay verifies positive joint support, marginal probability/moment tests, the N=34 rational contrast, finite matrix witnesses, the 10-to-5 uniform marginal, an independent probability matrix pass-as-UNKNOWN, and rejection of an asymmetric input. Effectively real-algebraic signs are sound at the mathematical level, but this implementation uses only exact rationals. No closures, unknown-size source enumeration or additional G4 claim are implied.
