# Independent hand review: exact source occupation flow and finite-test gap

Reviewer: dot (OpenAI), 8 October 2026.

Reviewed the complete frozen `EXACT-OCCUPATION-FLOW-AND-TERMINATION-GAP-CANDIDATE.md`, SHA-256 `82a393fcc6890e9b7bf3158d34ae5ca9d4135640c67e8be9db55686d27aac32a`.

**Verdict: SCOPED HAND ACCEPT** of Sections 2–4's exact finite-flow/source-reachability equivalence, equality of minimum occupation mass with minimum append count, and the stated positive-measure finite-polynomial-balance countercheck. The primary-paper comparison and original-scope limits are consistent. No blocking mathematical correction was found. This accepts neither a complete original G3 recognizer nor a false-positive NO instance for every finite relaxation.

## 1. Actual whole-source state and measurability

The accepted [finite-core coupled reachability reduction](https://github.com/Sodelin/Research-Commons/blob/34a36b3096e650e05a8f258c0e4d480511e4056f/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md), Git blob `ee93672cb099a504bd8a2d0730ec8ef08f4b0ace`, was reread with its [independent review](https://github.com/Sodelin/Research-Commons/blob/34a36b3096e650e05a8f258c0e4d480511e4056f/research/2026-10-06-dot-g3-global-source-reachability-0019z/REVIEW.md), blob `b6006b1e0b2fc5ecca8e7fc3ea86c6e07ca22dea`.

The state retains the core index, static shared tuple and complete coupled slot kernels; a legal edge is one actual strict append. It is not a macro-edge representing an already arbitrary word. A finite path has the original two-sided source correspondence. If edge records keep only endpoints, the legal relation already existentially supplies the needed physical append tuple, and finitely many such tuples can be recovered along a finite path.

For each fixed k, reachability in at most k steps is a finite semialgebraic formula, including the strict domains. Its projection R_k is semialgebraic. Consequently d_N=min(d,N) is a bounded Borel, indeed semialgebraic, function: its finitely many level sets use only R_0,...,R_(N−1). The proof does not assume that the full reachable set or the unbounded distance function is semialgebraic.

## 2. Exact measure balance really yields one finite source

For finite positive mu on the strict legal edge relation, probability sigma concentrated on initialization and probability nu concentrated on the entire target fibre, the equality

    s_*mu−t_*mu=sigma−nu

can legitimately be integrated against every bounded Borel d_N. The candidate uses concentration on the strict sets, not merely containment of topological supports in their closures.

Every edge obeys d_N(t)<=d_N(s)+1. A reachable starting point uses append closure of a shortest path; an unreachable or truncated-distance starting point satisfies the inequality trivially. Since d_N=0 on initialization, the equality gives

    integral d_N dnu=integral(d_N(t)−d_N(s))dmu<=mu(E).

The sign is correct. If no target is reachable, the left side equals N for every N, contradicting finite total occupation mass. If D is the shortest target distance, every target has d_N>=D when N>=D, including unreachable targets. Thus D<=mu(E). The minimum D exists as an integer once any finite target path exists. A shortest path's atomic occupation measure has mass D and attains equality. Zero-step realization has zero occupation measure.

No purification of an arbitrary mixture of biological kernels is invoked. The conclusion is existence of one finite graph path, so its static tuple and all row couplings remain unchanged along that path. The proof tolerates unreachable auxiliary states and cycles in the larger relation. Finite total EDGE mass, with unit cost per append, is essential; a differently weighted finite-cost flow would require another argument.

This establishes exactly the candidate's equivalence and minimum-mass statement. It does not give a finite description of an arbitrary feasible measure or an algorithm that detects whether any finite mass suffices. If a numerical/algebraic mass bound is supplied, a bounded original path search already decides the corresponding question.

## 3. The actual ordinary-curve countercheck

The [original strict cell/compiler formulas](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md), blob `b41fdf706e4dfcb5d14ffdbc88631012674ef1f4`, give polynomial ordinary capped coordinates and

    B_COMMON(sqrt(c),sqrt(c),g) E(sqrt(c))=E(c).

Thus every geometric-curve edge in Section 4 is an ACTUAL strict COMMON append, with an interior coin and positive connector. Rational x_0,c give distinct positive rational x_i; the chosen append arm/connector parameters are algebraic and strict. Other static state components can remain fixed in this admitted private-slot subcase.

After restricting a finite polynomial test list to this ordinary curve, let D bound its degrees. There are D+1 edge weights and D equations at powers 1,...,D. The resulting rational null vector exists. Distinct positive nodes make both the exponent-0-through-D Vandermonde matrix and the exponent-1-through-(D+1) matrix invertible. Hence its zeroth and (D+1)st moments are nonzero, as stated. The D=0 case also works, with one edge and a nonzero scalar perturbation.

For sufficiently small nonzero rational epsilon all perturbed edge weights are positive. The signed divergence perturbation integrates x^k to epsilon(1−c^k) times the vanishing node moment for k<=D, while the k=D+1 test is nonzero. The constant balance test always vanishes because each edge has one source and one target. Therefore every retained state-polynomial balance equation agrees with the exact unit-weight path flow, but the Borel divergence measure differs.

The scope qualification is crucial and correct. The endpoint is an ordinary YES and may already be an initialized state, so this is not evidence that a NO instance passes all finite relaxations, nor a gap in the optimum for that particular target. It disproves only the implication from a prescribed finite polynomial balance list to full measure equality. An input-dependent certificate theorem with additional source arguments is left open. No assumption about such a theorem's failure is silently added.

## 4. Primary occupation-measure source and scope

The review independently read Han and Tedrake, [arXiv:1803.09022v2](https://arxiv.org/pdf/1803.09022v2), Sections II–IV. They formulate an infinite-dimensional controlled Liouville measure LP and finite moment/SOS relaxations for a control-affine polynomial system on compact semialgebraic sets, with a box control domain. This supports the formulation context. It is not a theorem of terminating exact strict-support unknown-horizon G3 feasibility; the candidate does not claim otherwise. The source append's different control parameterization would also need checking for a direct imported implementation.

The new attained-boundary and supplied-normal Commons results retain their reviewed hypotheses and corrections. Their mention in Section 6 accurately prevents boundary=NO or universal regular-alternative assumptions; this review does not newly certify their underlying proofs.

## Final boundary

The flow equivalence is source-faithful across the entire retained-core/coupled compiler. The proposed algorithm still lacks a terminating exact feasibility/NO-certificate theorem, a finite sufficient balance language, or an input-computable mass bound. The continuous/measure reformulation does not remove the unknown finite witness budget.

No compiler, symbolic execution, source simulation, parameter scan or publication was performed in this review. Classical occupation-flow reasoning, the original source reduction and the primary literature retain attribution. Historical novelty and original-master completion are not certified.
