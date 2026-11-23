# Original G3: an exact all-source disjoint-quartet NO screen

Status: bounded hand derivation with an executed exact rational fixture/checker, not Lean-verified, not a full recognizer or novelty claim. No network, parameter, or source-word search is performed.

## Input and admitted setting

Use one supplied natural, completed, rooted **unranked** topology-response row that resolves the labelled restriction to eight same-taxon copies of $A$. One permitted allocation is eight copies of $A$ and one each of $B,C,D$ with the observation map discarding $B,C,D$; it is the same labelled restriction adapter as in the prior four-copy [original-observation quartet NO](https://github.com/Sodelin/Research-Commons/blob/f4ba57788564192f4705309b0aeb2cce404e35db/research/2026-10-06-dot-g3-original-quartet-whole-fibre-no-0454z/README.md), with more copies. If the row is uncoarsened one can simply compute the restriction; if the supplied observation cannot resolve the two specified event masses, do not infer them or add observations. Other supplied rows and fixed-ID constraints are unchanged. This screen applies to either natural inheritance mode separately.

Use the original [finite-input G3 reduction](https://github.com/Sodelin/Research-Commons/blob/ca0076c5603f46f02eb0d4065de9f482f928fbbc/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md): each alleged source is one finite strict original network (binary rooted-LSA, labelled outer-planar cut-child galled, parallel original arcs admitted) and one original physical tuple shared across its rows, with finite positive lengths, interior inheritance and original root completion. No restriction on source size. The inherited [same-source unranked all-panel projectivity](https://github.com/Sodelin/Research-Commons/blob/e43167ff700bd101ecdf581764c870c2f3308edf/research/2026-10-11-dot-accepted-connected-union1591-1247z/source-store/4936fb211505d9c5961256ba4f1a4c63db0065c7c94ccadf3fcd67a320f270c3.lean) is crucial. Natural routing, coalescences and root completion are equivariant under permutations of starting copy labels within a taxon: independent routing uses the same probabilities anew for each current root, COMMON uses its one shared draw, and exchangeable Kingman pair rates do not distinguish starting sample labels. No mixed-mode, time-dependent, or copy-sensitive controlled row is needed.

## Certificate and proof

On two disjoint four-copy blocks, let $X_1,X_2$ indicate that their respectively restricted rooted trees have a balanced root split of $2+2$. Compute $p=Pr(X_1=1)=Pr(X_2=1)$ and $q=Pr(X_1=X_2=1)$ from that one eight-copy table. Any admitted source satisfies $\mathbf{q\ge p^2}$.

Indeed, fix a purported source and keep its entire graph, root completion, and tuple unchanged. The natural sampling rule on the same source is defined at any finite copy count. For any integer $N\ge2$, consider $N$ disjoint four-copy groups in a hypothetical same-source experiment. Within-taxon equivariance and all-panel projectivity give the same $p$ to each indicator and the same $q$ to each distinct pair. Thus
$$
0\le\operatorname{Var}\bigl(\textstyle\sum_{j=1}^N X_j\bigr)
= Np(1-p)+N(N-1)(q-p^2).
$$
If $q<p^2$, it suffices to take $N=2+\lfloor p(1-p)/(p^2-q)\rfloor$, when the right side is negative. This is a finite witness to the impossibility of a compatible continuation of the observed row. It does not require measuring that continuation, infinite sample data, conditional independence, adding any original ID, or running either mode on different fits. This rejects every possible core and word at once. If the inequality passes, return UNKNOWN, not YES.

## Strictly positive rational fixture; the four-copy test cannot see it

Let $L$ be the row law mixed from two mathematical distributions on eight labelled rooted binary trees, not two claimed physical source preparations:

1. With weight $7/12$, relabel all eight slots uniformly on a fixed tree whose root has two comb subtrees of sizes three and five.
2. With weight $5/12$, choose uniformly from all 135,135 rooted, nonplane, leaf-labelled eight-tip binary trees.

Uniform admixture makes every labelled topology strictly positive. In the fixed shape, an induced quartet is balanced iff the four chosen leaves split 2+2 across the original root: a quartet within one comb is never balanced. There are $\binom32\binom52=30$ such four-subsets out of 70, and its complement cannot be balanced because only one leaf remains on the side of size three. Therefore $p=3/7,q=0$ in this component. The uniform component has $p=1/5, q=6327/135135$, by exact enumeration (delete the newest leaf to invert edge insertion, including the root stem). The mixture gives $p=1/3, q=703/36036$, forcing variance $-1895/9009$ already at $N=4$.

The entire four-copy marginal reproduces the ordinary single-taxon Kingman topology law: it is exchangeable, so each of three balanced labelled topologies has probability $1/9$ and each of twelve comb topologies $1/18$. These are the Kingman probabilities because after the first pair merges, the next merger chooses the pair of remaining singletons with probability $1/3$. In particular the previous upper bound $p<5/12$ alone cannot exclude it. The eight-copy law is permutation-invariant and its prescribed lower rows may be generated by literal restriction, hence it already passes finite exchangeability and consistency of those supplied rows. The obstruction exploits the extension forced by a single physical source, not an incompatibility among observed rows.

## Replay

Run `python -B g3_obstructions/obstruction.py` from the workspace root. It independently counts the fixed shape via subsets and all $8!$ slot labellings, enumerates all distinct nonplane labelled binary trees, compares exact counts, checks the variance certificate, and checks that an equality control is UNKNOWN. See `fixture_result.json`. Code uses arbitrary-precision fractions; rational strings are accepted while floats are rejected. The mathematical inequality also applies to effectively real-algebraic data with an exact sign decision; this script does not implement algebraic arithmetic or a general observation parser.

This screen is a standard covariance consequence of projective exchangeability, newly packaged here for the task rather than claimed as a new principle. Because it is closed, it never rejects an input in the source-image closure. It does not decide boundary nonattainment, fibre membership, general G3 termination, or any G4 forcing problem. A natural extension is higher moment-matrix tests when more disjoint observable groups are actually available, not a completeness claim.
