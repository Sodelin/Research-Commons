# Independent proof review

Reviewed REPORT.md §§2–8 and 10 on 2026-09-30. This is a hand proof challenge, not formal verification, source-class classification, or implementation verification. No root artifacts were edited.

## Required correction: the experiment in §2

The positive separation theorem needs only fixed marginal IID row streams for its union bound. The negative theorem needs more: conditional on the whole observed history and the predictable environment choice, the next observation must have that environment's fixed row law. Arbitrary dependence between row blocks is not harmless for the claimed necessity or iff characterization.

Counterexample: two binary row streams have Bernoulli(1/2) marginals under both targets. Under target 0 let Y_i=X_i; under target 1 let Y_i=1−X_i, with independent X_i across i. Every row is IID and the row-array separation is zero, yet one paired observation identifies the target. The negative theorem must therefore use fresh conditional row draws/independent row experiments, or encode the full joint observable law rather than only row marginals. Fixed-prefix reused data remain admissible for the positive coverage argument; their correlations cannot be discarded in a general impossibility claim. The one-row source witness in §10 is unaffected.

## Exact abstract boundary: accepted

The stated H_m formula is correct for all legal nonempty masks of size at most two.

For differing masks choose t absent in p and present in q. In a witnessing row, the contrast difference is at least Delta, so TV is at least Delta/2. Also p_t≤1/3 and q_t≥Delta, giving Delta−1/3. When m=1, the absent coordinate is the row baseline a; at least one supported coordinate is a+Delta or greater, hence 1≥3a+Delta and a≤(1−Delta)/3. This gives (4Delta−1)/3. If Delta>1/2, a two-support row would require 1≥3a+2Delta>1, so only singletons remain. Different singleton laws differ by at least Delta in a supported coordinate.

All attainment constructions in §4 are legal, including Delta=2/5, 1/2, 2/3, and 1. For m≥2 the shared first row witnesses target 1; the second row alone witnesses target 2 in the alternative provider. Additional common rows preserve both masks. The three-category identity TV=max_i|p_i−q_i| is valid, including zero differences.

The homogeneous contamination boundaries also check. TV observed-class separation is at least H_m−2epsilon. Huber separation is at least (1−eta)H_m−eta by the reverse triangle inequality. At the stated boundaries the attained clean pair has common observed laws row by row. Huber intersection is exactly (1−eta)(1+TV)≤1 because the minimal dominating vector is (1−eta)max(p,q). Compactness follows from finitely many closed mask/witness constraints inside a product of simplices. These are exact abstract-provider statements; they do not prove biological realizability of the attainment arrays.

## Other sections

- §§2–3: the fixed-time constants, strict good events, nearest-target infimum argument, TV and Huber contrast bounds are correct. The finite target minimizer does not require an attained nearest member. Computability remains a separate obligation, as stated.
- §5: the TV subset inequalities are the correct expansion of the lower/upper box-sum conditions. Huber elimination additionally requires sum_i u_i≥1 and valid coordinate intervals; make explicit that inconsistent-box preprocessing checks this. Its displayed subset inequalities alone do not imply sum_i u_i≥1. The compact planar-polytope vertex argument and witness-subset coverage argument are sound. law_feasibility.py was not present at initial review, so its implementation has not been checked here.
- §6: the anytime allocation and conditional Hoeffding argument are correct. Replace “the two-sided Hoeffding tail equals” with “the two-sided Hoeffding upper bound equals.” Unique fixed within-row prefixes and predictable fresh draws are substantive requirements.
- §7: the first-error ideal-transcript composition is correct under the stated certificate soundness, query bound, and computation/termination contracts. Finite fixtures remain fixtures, as the report explicitly says.
- §8: the normalization interface is appropriately conditional. Clarify that a certified TV discrepancy rho adds to the TV error budget; it does not automatically add to a Huber mixture fraction while preserving that contract.
- §10: the graph switchings and arithmetic check: H←U gives AB|CD with internal U–V of length ln4, while H←W gives AD|BC with internal V–W of length ln2. Their weighted laws yield (2/3,5/48,11/48), and the stated TV/Huber common laws and contaminant coordinates are exact. Source admission still rests on the declared network/coalescent parameter contract; these checks do not classify richer menus.

## Target scope

The negative theorem concerns mutually exclusive declared answers. A fixed decoder-chosen compatible order is a valid target for a sufficiency theorem. If the original task permits any compatible order, different selected orders alone need not imply incompatible correct outputs. To transfer necessity to that relational task, show disjoint valid-output sets or differing split unions. The §10 witness has differing split unions and is safe on this point.

The report properly limits the finite feasible model to the abstract provider class. The required fixes above concern the declared statistical experiment and target relation, not a missing proof that every feasible law is biological.
