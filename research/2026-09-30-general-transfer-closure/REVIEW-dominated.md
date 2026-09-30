# Independent full proof review: dominated source, standard-Borel target

Reviewer: /root/current_sparse_scope_audit. Date: 2026-09-30 UTC. Reviewed the actual transfer_closure/dominated.md, Sections 1–6, not merely the earlier finite-output lemma.

Reviewed SHA-256: 96fce4108be5b37db90b87c6bf56617a742f796509c05d26c13d9866e3026066.

## 0. Verdict

No fatal mathematical gap found. Under one common probability dominating the entire source family, arbitrary measurable X, arbitrary nonempty parameter class Theta, and nonempty standard-Borel Y, the manuscript's minimum-deficiency and all-finite-action Bayes-gap characterization is supported by the full proof.

The extension genuinely removes finite Y within its declared class. The argument does not establish nondominated comparison, arbitrary pathological target sigma-algebras, a computable simulator, historical novelty, or the biological application premises. A general theorem remains distinct from classifying the biological observation fibers.

## 1. Operator compactness at full scope

For compact metric C, the product indexed by continuous real functions f has weak-star compact coordinates {g∈L∞(mu):||g||∞≤||f||∞}. This is Banach–Alaoglu compactness, not assumed sequential compactness. Linearity, positive-function inequalities and T1=1 are intersections of weak-star closed conditions, tested against L1 functions. Their intersection is compact and convex. Positivity and unitality supply the necessary operator norm bounds.

For each theta, p_theta=dP_theta/dmu is an L1 test functional; no countability restriction on theta is needed. Product topology allows all continuous-function coordinates at once. The source measure is finite, so the L1/L∞ dual identification used here is valid even when X is not standard Borel.

## 2. A genuine measurable kernel survives the limit

The countable dense rational subspace D containing 1 is available because C is compact metric. Countably many representative functions and countably many rational linearity, normalization, positivity and norm relations permit one measurable mu-null repair set.

Outside that set, the bounded rational-linear functional extends uniquely to a bounded real-linear functional on all continuous functions. Positivity extends by uniform approximation and small positive rational constant shifts. Riesz representation then gives a probability K_x on C.

For every continuous f, its K_x-integral is a pointwise limit of measurable D-evaluations. Open-set masses are measurable using continuous approximations to indicators; the resulting Dynkin/monotone-class argument covers all Borel sets. A fixed point mass on the one exceptional set completes a kernel on the original Sigma, without disintegration or a standard-Borel hypothesis for X.

For an arbitrary continuous f, uniform approximation also proves equality of the recovered operator and T in L∞. Although different f can have different equality exceptions, operator equality is all that is needed for each pushforward integral. Common source domination makes every repair null for every P_theta; there is no illicit union over uncountably many parameter-specific null sets.

## 3. TV lower semicontinuity and simultaneous compatibility

Borel probabilities on compact metric C are Radon. Continuous functions in [0,1] determine their TV distance through the stated supremum. Each continuous-test integral is continuous in the pointwise weak-star operator topology; hence each TV constraint is lower semicontinuous and has closed sublevel sets. Continuity of TV itself is neither claimed nor needed.

The uniform supremum is lower semicontinuous on the compact operator set, so it attains a minimum. Defining d as the supremum of finite-parameter restricted minima gives a finite-intersection property at the same threshold d. Compactness then yields one parameter-independent kernel across the entire arbitrary parameter class. This is the required compatibility step, not a collection of unrelated finite-subproblem simulators.

## 4. All finite-action losses, beyond finite Y

The dual feasible set of (lambda,v), with continuous v_theta and 0≤v_theta≤lambda_theta, is convex; it need not be compact. The payoff is affine and separately continuous in that norm topology and the compact weak-star operator topology. Sion's one-compact-side theorem therefore applies.

For a fixed finite-parameter dual tuple, the pointwise supremum of source utility is the supremum over a countable dense set in C, hence measurable. Choosing the first dense point within eta of that supremum gives a measurable eta-optimal source action; no unsupported exact measurable-argmax assumption on X is introduced.

The finitely many continuous utilities u_theta=v_theta/lambda_theta are uniformly approximated by a finite grid of action values. The target identity-rule utility loses at most eta after selecting the first qualifying grid point. The source finite-grid optimum cannot exceed its unrestricted optimum. The finite-action Bayes gap consequently approaches the dual value. The universal TV risk inequality supplies the reverse inequality.

Thus the decision-gap formula is a supremum over finite-action problems; it need not be attained by a single finite-action witness. The manuscript correctly distinguishes that supremum from the attained kernel minimum. TV normalization remains correct: losses in [0,M] incur at most M times TV.

## 5. Compactification and escaped mass

The Borel embedding i:Y→B⊆C and fixed measurable repair J:C→Y satisfy J∘i=id_Y. Kernels into Y embed into C, preserving TV; kernels into C repair into Y with no greater TV by data processing. Therefore the two deficiencies are exactly equal.

Repairing an attained compact-target optimum gives an attained optimum on Y. This argument remains valid at positive deficiency when the compact kernel puts mass outside B. A closed-image or zero-escaped-mass claim is not required. Finite-action decision rules restrict and extend through the embedding without changing risks under target laws supported on B, so the all-loss characterization also survives.

## 11. Process integrity

Reviewed the complete universal argument and the actual file hash. Checked infinite-dimensional closure, representation, null repair, measurability, Radon/TV assumptions, minimax quantifiers, finite-action approximation and compactification. No finite test is being substituted for these proofs. The independently inspected Sion primary publisher text supports the one-compact-side interchange; the instructor's general Banach–Alaoglu passage confirms compactness without separability. No Lean verification or exhaustive priority review is claimed.

## 12. Robustness and closure boundary

The proof's strongest scope depends on common domination of the whole source family, standard-Borel target structure, unrestricted measurable kernels and all bounded finite-action losses. Dropping these premises is outside this review, not an automatic impossibility result.

This passes the hand-review gate for the mathematical extension. It does not pass the separate downstream biological closure gate: identifying the observation law, validating the target/model correspondence, discharging biological fiber invariance or ambiguity, and supplying any registered computation/noise/cost guarantees remain application obligations.

