# Independent review: hidden-answer recovery interface

Reviewer: `/root/current_sparse_scope_audit`. Date: 2026-09-30 UTC. Reviewed actual `scientific-interface.md`, SHA-256 `bc3d57557467eb8057ebd9cae1b1190bd3f2755c4a64a537b162c987befcdf3d`.

**Verdict:** no fatal mathematical gap found. The positive characterization and all stated obstructions hold at the declared scope. The note correctly leaves scientific model admission and observation-law identification to the application owners. This is a hand-review, not machine verification or a novelty claim.

## 1. Exact law simulation really is exact answer recovery here

For any probability law R on the nonempty standard-Borel answer space, `TV(R,delta_a)=1-R({a})`: singleton and complement events attain the bound, and every other event discrepancy is bounded by it. Consequently the Dirac-target comparison has precisely the proposed randomized-estimator interpretation. No assertion that an arbitrary non-Dirac target experiment already identifies a hidden answer is smuggled into this interpretation.

The randomized-to-deterministic iff is sound for arbitrary measurable X and arbitrary parameter sets. The probability-law space of a standard-Borel A, with its evaluation sigma-algebra, is standard Borel. The Dirac embedding is Borel and injective, so its image and inverse are Borel by the Borel isomorphism theorem. The measurable default-filled inverse thus gives one deterministic decoder on all X. The nonnegative integral equal to one forces `K_x({a(theta)})=1` for each parameter almost everywhere; a probability with that property is the relevant Dirac law. Different parameter-specific null sets are harmless because the decoder was constructed once from K, rather than constructed separately and pasted across uncountably many full-measure sets.

An alternative direct check is to embed A as a Borel subset B of [0,1]. The function `x -> integral b(a) K_x(da)` is measurable. Apply the Borel inverse on B and a fixed default outside B. At every source-almost-sure Dirac law this yields its unique answer. Thus the existence claim does not depend on choosing a measurable decoder separately for each parameter.

The disjoint measurable inverse-image regions form the actual exact-recovery partition. Pairwise singularity of differently answered source laws is necessary but does not imply that this partition is measurable for arbitrary uncountable families. The non-Borel-label point-mass example correctly distinguishes these conditions. Under one dominating probability, every realized answer's region has positive dominating mass; disjoint positive-mass regions are countable. The resulting countability obstruction concerns exact realized answers, not approximate real-valued estimation.

## 2. Quantitative lower bounds

For r distinct answers, contraction compares each simulated singleton probability under its source law and under the common reference. Summing the r disjoint reference singleton probabilities gives the stated average-separation bound. Passing from the average error to the supremum error has the correct direction. Replacing a negative lower bound by zero is legitimate. Identical r-state source laws attain `1-1/r` by uniform guessing, which supports exactly the stated zero-separation sharpness claim; no unsupported all-family attainment claim is needed.

The two-state triangle inequality uses different Dirac targets at distance one, estimator errors equal to their corresponding Dirac discrepancies, and contraction of the intervening source distance. Hence `sup error >= (1-TV(P_1,P_2))/2` holds for every measurable kernel regardless of computational resources. The bound alone need not be attained by every asymmetric two-state experiment, and the text does not claim that.

## 3. Uniform finite-sample obstruction and continuity

For a fixed finite N, source TV convergence implies IID product TV convergence through the proved common-submeasure product bound. The sequence of binary lower bounds then tends to 1/2, so the supremum error over the full admitted class is at least 1/2. This argument requires no estimator attaining its infimum. If exactly two answers are possible, an answer coin independent of the observations attains that worst-case baseline. More answers retain the lower bound without an unjustified optimality claim. Pointwise consistency and additional or altered observations remain separate questions.

A TV modulus tending to zero for Dirac targets forces locally constant answers: choose a sufficiently small radius whose bound is strictly below one, then every nearby Dirac target must be identical. On a connected parameter domain, a locally constant answer map is constant. Thus a compact-net certificate requiring such a modulus cannot silently cover a changing support label across a zero-weight boundary. The note correctly separates smooth source probabilities from the much stronger continuity required of this discrete target, and it does not claim compactness alone resolves the boundary.

## 4. Closure boundary

The results establish a complete exact measurable-partition criterion and general estimator lower bounds. Their applications still require an admitted scientific parameter class, its actual observation measures, a defined answer map and any necessary intervention semantics. In particular, the rare-mechanism lemma does not validate a biological sequence until actual law convergence and answer changes are proved. Distinct quartet support, genealogy, sequence and distance experiments remain distinct until explicitly connected. These application dependencies are correctly retained rather than declared solved by the generic theorem.
