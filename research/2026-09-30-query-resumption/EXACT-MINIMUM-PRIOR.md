# Exact finite-n quartet-query optimum: focused primary audit

Contributor: Codex delegated primary-prior researcher, QUERY-RESUMPTION-PRIMARY-20260930. Date: 2026-09-30 UTC. Requested follow-up: the actual minimum worst-case query count `Q*(n)` for every finite `n`, rather than an asymptotic order or a better example algorithm. Status: primary-source audit and elementary decision-tree distinctions; no exact all-n formula, hardness reduction, or historical-completeness claim.

## 1. Result of the audit

**No exact finite-n minimax quartet-query formula was found for the full admitted source class, arbitrary circular binary-tree families, or even unrestricted adaptive reconstruction of a single unrooted binary tree.** The inspected reconstruction theorems give asymptotic bounds and explicit algorithm budgets. These are not equality theorems for the smallest integer query count at each `n`.

There is positive primary evidence that a substantially weaker precision question was already nontrivial: Emamjomeh-Zadeh & Kempe's SODA 2018 paper explicitly leaves open the leading constant for noiseless **rooted binary-tree ordinal queries**. Its reported upper bound is `N log_2 N`, whereas its counting lower bound is `N log_3 N−O(N)`. This is a dated open question in that specific query model, not a proof that the present all-n network optimum is computationally hard or that no later result exists.

The August 2026 full-quartet consistency paper inspected below still reports exact reconstruction only up to constant factors; its concrete anchored query budget is an upper bound. A bounded follow-up search located no exact integer refinement. The new Commons `Θ(n log n)` result therefore does **not** satisfy the user's stronger exact-minimum request by itself.

## 2. Primary texts and exact precision

| Primary source, full text inspected | Relevant theorem or passage | What it establishes |
|---|---|---|
| Emamjomeh-Zadeh & Kempe (SODA 2018), *Adaptive Hierarchical Clustering Using Ordinal Queries*, DOI [10.1137/1.9781611975031.28](https://doi.org/10.1137/1.9781611975031.28), [primary preprint](https://arxiv.org/pdf/1708.00149) | Section 4 gives a deterministic noiseless rooted-binary-tree learner with at most `N log_2 N` triplet queries. Section 6 explicitly asks whether this leading constant is correct, after contrasting the lower bound `N log_3 N−O(N)`. | Asymptotic optimality, with a leading-constant gap explicitly acknowledged in 2018. No exact finite-`N` minimum. Rooted ordinal queries simulate anchored unrooted quartets by adding a fixed outgroup; unrestricted unrooted quartet queries are a different access model. |
| Kannan, Lawler & Warnow (1996), *Determining the Evolutionary Tree Using Experiments*, Journal of Algorithms 21:26–50, [primary paper hosted by university](https://ics.uci.edu/~goodrich/teach/cs262P/notes/SequentialEvolutionaryTrees.pdf) | Section 2.2 counts rooted binary trees as `(2N−3)!!`, obtains the ternary information lower bound, and gives logarithmic-query leaf insertion. | Establishes the classical experiment model and `Ω(N log N)` information bound, not matching finite integer minima. Results permitting unresolved responses concern another class and can have quadratic complexity. |
| Brodal, Fagerberg, Pedersen & Östlin (ICALP 2001), *The Complexity of Constructing Evolutionary Trees Using Experiments*, [primary BRICS report](https://www.brics.dk/RS/01/1/BRICS-RS-01-1.pdf), [author proceedings version](https://cs.au.dk/~gerth/papers/icalp01.pdf) | The binary case has a budget `N(log N+O(1))`; degree-dependent upper/lower bounds are presented as tight asymptotic bounds. | Separator-tree reconstruction and improved constants/order, not an exact finite-`N` optimal decision-tree depth. |
| Lin (August 2026), *Testing Full Quartet Consistency: Adaptive Reconstruction, Random Verification, and Constant-Query Testability*, [primary full HTML](https://arxiv.org/html/2608.00987v1) | Lemma 1 gives anchored exact learning within `L(n)=ceil((n−1)lg(n−1))`, by reducing to the 2018 rooted learner. The reconstruction conclusions and lower-bound statements explicitly say optimal **up to constant factors**. | A concrete integer algorithm budget and an asymptotic optimum. `L(n)` is not asserted to equal the minimum. Property-testing verification counts have an additional error/distance contract and cannot answer the noiseless source minimax question. |
| Frohn, Holtgrefe, van Iersel, Jones & Kelk (2025), *Reconstructing semi-directed level-1 networks using few quarnets*, DOI [10.1016/j.jcss.2025.103655](https://doi.org/10.1016/j.jcss.2025.103655), [primary full text](https://arxiv.org/html/2409.06034v2) | Theorem 14(c) gives `O(n log n)` displayed-quartet reconstruction of most of a semi-directed level-one network; Proposition 15 gives asymptotic optimality. | A different source/output contract and matching asymptotic order; no all-n exact quartet-query function. |

The term “exact reconstruction” in these papers means the recovered topology is correct. It does not mean the number of queries is the exact mathematical minimum. Likewise “optimal” accompanied by `O`, `Ω`, or `Θ` can mean optimal up to constants.

## 3. Single-tree finite-n bounds are not a formula

**Elementary deduction from the oracle contract and classical tree count.** Let `R_tree(n)` be the smallest worst-case number of deterministic adaptive unrooted quartet queries needed to reconstruct every labeled binary tree on `n≥4` leaves. There are `(2n−5)!!` possibilities. On this subclass each four-set returns one of three singleton topologies. A decision tree of height `h` has at most `3^h` leaves, so

`R_tree(n) ≥ ceil(log_3((2n−5)!!))`.

This is a lower bound only. It does not prove a query with sufficiently balanced realizable branches exists at every transcript. Conversely the anchored learner gives

`R_tree(n) ≤ ceil((n−1)log_2(n−1))`,

and querying all four-sets is another finite upper bound. These inequalities do not coincide in general. Minimizing the queries used by one insertion step also need not minimize the full unknown-tree decision tree, which may ask different global questions.

For the full Commons output of common circle **and full split union**, ordinary binary trees form an admitted subclass, and their split union uniquely determines the tree. Therefore `Q*(n)≥R_tree(n)` is a valid subclass lower bound. It does not imply that knowing the larger-class function `Q*(n)` would determine `R_tree(n)`, nor does an unresolved tree optimum prove a hardness theorem for the larger source class. Common-order-only output would require a different argument because one circle can be compatible with several trees.

Do not replace the ternary tree-subclass lower bound by a generic seven-answer count: the subclass answers are singleton masks. Nor does the entropy bound for the number of source profiles automatically give a tight query strategy.

## 4. What an exact all-n result would need

For fixed `n`, complete support observations are finite: each of `binom(n,4)` four-sets has one of at most seven nonempty masks. The admitted sources induce some finite subset `P_n` of these profiles, even if their graph descriptions are not bounded a priori. This finite observation bound alone does not identify which profiles belong to the admitted source class.

A concrete exact minimax computation needs a sound **and complete** description of `P_n`, plus the permitted outputs for each profile. Exhausting arbitrary circular binary-tree families can enlarge the source domain; it does not become an admitted-profile census without a realization theorem. Conversely finite enumeration of selected galled graphs can omit admitted profiles unless graph-size completeness is proved. None of the inspected prior theorems supplies this classification for the exact Commons source contract.

For deterministic worst-case queries, once the complete source-profile domain is known, the exact value obeys the standard finite decision-tree recurrence. For a residual profile set `H`, stop at depth zero exactly when one permitted output is valid for **every** profile in `H`. Otherwise,

`D(H)=1+min_q max_{a: H_{q,a} nonempty} D(H_{q,a})`,

where `H_{q,a}={p∈H:p(q)=a}`. The initial value is `D(P_n)`. This recurrence is a characterization or an exhaustive method, not a solved closed-form `Q*(n)`. It cannot be instantiated with a guessed source domain and called the exact admitted optimum.

If a randomized model with expected rather than worst-case query cost is intended, it needs its own definition; the deterministic recurrence above is not automatically its value. The existing exact-support deterministic task naturally gives the stated worst-case model, so no additional ambiguity is required to avoid the mathematical work.

## 5. Search limits, receipts, and safe conclusion

Focused strong-engine searches included `phylogenetic tree reconstruction quartet queries exact optimal number worst case`, `"quartet queries" "optimal"`, `"quartet" "queries" "decision tree" reconstruction`, `"optimal" "quartet queries" reconstruction number exact`, and `"exact query complexity" "phylogenetic"`. Further searches covered exact rooted triplet/ordinal queries and later noiseless leading-constant work. Search results often mixed reconstruction accuracy, noisy sample complexity, distance queries, supplied quartet compatibility, and phylogeny score optimization; these were not transferred to the requested minimax problem.

Primary retrieval receipts: 2018 full PDF `turn55view0`, exact Section 6 passage `turn57view5`/`turn57view6`; Kannan paper `turn55view1`; Brodal report `turn57view0`; Lin full text `turn52view0`, Lemma 1 and asymptotic scope therein. The Lin full text became accessible in this follow-up; earlier notes explicitly recorded failed retrieval and abstract-only scope, which this new receipt supersedes for this audit.

The correct report is: **the asymptotic master is closed under the accepted proofs, while the exact finite-n minimum has not been solved by the current argument, and no primary exact formula was found in this focused audit.** The 2018 rooted-model open question is supporting context, not a reduction-based impossibility claim. Continue work on admitted-profile classification and exact adversary/strategy equality if the user requires the actual integer `Q*(n)` for all `n`.
