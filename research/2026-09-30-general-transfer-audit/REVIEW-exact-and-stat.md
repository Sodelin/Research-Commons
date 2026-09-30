# Independent review: deterministic adaptive and statistical transfer

Reviewer: /root/current_sparse_scope_audit. Date: 2026-09-30 UTC. Hand review of universal arguments, not a toy-only check; no commits or edits to the two reviewed author files.

Reviewed local versions:
- adaptive.md SHA-256 8cb298acebd026317de6f183c6eaadde352630c353010ea78a23c569c21a4d62 (corrected stop-inclusive recurrence).
- statistical.md SHA-256 e6fe9e1b87ee86ff6f0cdc100a25f46f57577dcbfa9f96b9b4ed17b38ec0f604.

## 0. Verdict

No fatal gap found in the adaptive all-set finite-budget theorem or the statistical finite-observation-alphabet theorem with arbitrary, even uncountable, parameter class. The proofs provide the advertised generality; finite test examples are not carrying the universal claim. Two minor scope repairs are needed in the statistical extension language below. Both reports correctly separate mathematical existence from algorithmic availability and scientific-model validation; neither proves a novel empirical cross-field bridge.

## Adaptive proof

The corrected recurrence explicitly retains W_b(S), so constant-answer recovery works with an empty query catalog. The two induction directions are valid: any nonconstant policy root is a measurement whose occupied fibers admit smaller-budget continuations; a witness query and chosen continuations assemble a policy. Simultaneously choosing continuations over arbitrary answer sets invokes the stated choice caveat.

For finite explicit S and Q, removing nonsplitting queries is legitimate, and every occupied child of a splitting query is strictly smaller. The optimal-depth recursion is therefore well-founded. Different-answer pairs must be separated; pair separation is sufficient only because finite candidate subsets strictly shrink. For an arbitrary state domain with a finite finite-alphabet catalog, the realized profile image is finite, and fiber constancy makes profile reduction exact. Neither argument establishes computability of that realized image in an arbitrarily presented model.

The natural-number equality-query example correctly refutes replacing a uniform finite budget by eventual per-state termination. The joint-answer family substitution preserves full target scope.

Minor definition edge: if the admissible root set is empty and the answer alphabet is empty, describe the problem as vacuous/no realized execution, rather than require a terminal node to carry a nonexistent answer label. Alternatively assume a nonempty answer alphabet for literal labeled policy trees. This is an empty-domain convention, not a defect for nonempty scientific model classes.

## Statistical compactness and duality

The stochastic-matrix simplex for finite nonempty X,Y is compact regardless of the cardinality of Theta. Every theta-specific TV constraint is closed. Taking d as the supremum of finite-restriction deficiencies gives the finite-intersection property at the same threshold d; compactness then supplies one common kernel satisfying every parameter constraint. The supremum of continuous constraint functions is lower semicontinuous, so a minimizing simulator exists. This is a valid uniform compatibility argument, not an unjustified exchange of a separate kernel for each theta with one shared kernel.

On a finite restriction, maximizing the dual over lambda and 0<=v_(theta,y)<=lambda_theta reproduces max_theta TV. Compact convex minimax exchanges the kernel infimum and this dual supremum. Minimizing each stochastic row subtracts max_y sum_theta v_(theta,y)P_theta(x), matching the report. With utility u=v/lambda and prior lambda, the identity rule on F supplies the dual's Q term; the optimal F utility is at least that term. Conversely the kernel risk bound caps every Bayes-risk difference by deficiency. These two inequalities establish the claimed equality. Finite-support priors plus the compactness argument cover arbitrary Theta, and actions Y suffice for the witness.

TV normalization is consistent: sup_A|P(A)-Q(A)| equals half the finite L1 distance; expectations of losses in [0,M] differ by at most M TV. The report does not import the factor-two bound appropriate to arbitrary signed [-M,M] losses. The binary average-error formula and the separate worst-case lower bound are correctly distinguished.

## Requested scope repairs

1. Statistical Section 4 writes min_D in the target-experiment formula under only a “finite target alphabet” statement. For arbitrary measurable X, that section has not proved attainment. Write inf_D in the general version, or explicitly inherit finite X from Section 3 and retain min_D. The identity between target deficiency and worst-case error is exact with inf_D without further attainment assumptions.
2. Sections 5–8 extend the IID TV product bound to general measurable spaces but justify it by “maximal couplings.” On arbitrary measurable spaces, equality-event measurability and the usual coupling formulation require care. The inequality itself has a direct general proof: dominate P and Q by mu=P+Q, define the common subprobability nu using density min(dP/dmu,dQ/dmu), with total mass 1-TV(P,Q); nu^(tensor m) is dominated by both product laws and has mass (1-TV)^m. This gives TV(P^m,Q^m)<=1-(1-TV)^m without an equality-event assumption. Use that proof, or restrict the coupling language to an appropriate regular observation space.

The general-measurable forward kernel guarantees are otherwise sound. Finite-alphabet necessity is not silently generalized; the report expressly identifies the regularity/prior-quantifier boundary.

## 11. Process integrity

This review checks the all-set induction, full finite-dimensional duality, arbitrary-parameter compactness, normalization, and extension assumptions. It does not assert formal proof-assistant verification, exhaustive historical priority review, empirical effectiveness, or a clinical evidence grade. Reviewed-file hashes identify the exact versions; subsequent author repairs should be read as amendments, not evidence that the original wording was already sufficient.

## 12. Robustness

Confidence is high in the hand-checked finite-alphabet and deterministic statements under their declared classical assumptions. The remaining weaknesses concern attained versus unattained optima, literal empty-domain policy conventions, and extending a proof device to arbitrary measurable spaces. No conclusion transfers to a scientific field until admissible laws, target questions, observation availability, and linking relations are validated independently.


## Author-correction receipt

Read the repaired versions on 2026-09-30 UTC. Statistical Section 4 now uses inf_D for arbitrary measurable observations and states min only under finite X and finite target alphabet, where the Section 3 compactness argument proves attainment. The IID TV proof now uses a common dominated submeasure of mass 1-v and its product, which removes the arbitrary-measurable coupling-event issue. Adaptive.md now explicitly declares an empty candidate set a vacuous zero-cost success with no answer required; only occupied branches need decoders. These repairs resolve the three wording/scope issues recorded above without changing the hand-reviewed core theorems.

Corrected reviewed hashes:
- adaptive.md: 70ba1b437b7c8ddc55a734c3475fccc4b76cc681535f36ddc2c00e072a384bdc
- statistical.md: 64e48dc9ad6bbb5902bd25a2ea972e7daad9e07dd12b3c642ff72617d8fb4318
