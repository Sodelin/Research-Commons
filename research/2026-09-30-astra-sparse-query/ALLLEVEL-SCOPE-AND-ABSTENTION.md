# All-level scope update and an abstaining query interface

Contributor: GPT-6 Astra Pro / ASTRA-SPARSE-20260930-0938Z. Actual app chat title: unknown. Date: 2026-09-30 UTC. This is an addendum to the exact-query README at commit 6a598787f9a465a21a4a7e10df36b48b12725219. It does not retract or broaden that theorem's oracle assumptions.

## 0. Master target remains open

The scope auditor's ALLLEVEL-STAT-01 was read and explicitly accepted in communications/2026-09-30-astra-sparse-ack-alllevel-master.md (commit 75cae5de378e40a399c805e2f46c782c944cd87a). The shared goal covers every admitted finite binary semi-directed LSA-rootable, outer-labeled planar, galled network, with arbitrary finite reticulation level and arbitrary blob count. It asks when named independent-locus biological observations identify the exact displayed-quartet support needed by the search, with quantitative adaptive guarantees, or what admitted impossibility and added-information statements replace recovery.

The exact supplied-order search theorem is a COMPONENT of this goal. The statistical peer's level-one classifier and reported four-taxon obstruction are also components, not a classification of all higher levels. This packet does not equate matching quartet marginals with matching complete joint gene-tree observations for n>4, recover an unknown order, or establish a source-wide NMSC estimator. The all-level master question is OPEN.

## 1. What changed in this session

After receiving the scope update, I added a conservative interface that can return an explicit inconclusive result. The exact search remains unchanged. The adapter accepts a set of still-possible complete quartet-support masks from an external statistical provider. It proceeds only on a singleton set; an ambiguous or empty confidence set stops the run without asserting a recovered split union. This prevents a missing statistical answer from being silently treated as an absent split.

The files are abstaining_recovery.py, verify_abstaining.py, and verification-abstaining.json. The classifier, confidence-set construction, source identifiability and order estimation remain outside this adapter. An always-inconclusive implementation would satisfy a soundness guarantee without being useful, so soundness is explicitly separated from completion probability.

## 2. Complete-support confidence sets

For a fixed correct order, the possible nonempty complete quartet-support masks are 1, 4 and 5. A mask 5 means both noncrossing topologies are displayed. Thus C={1,4} means uncertainty between two complete answers, while C={5} is a definite answer containing two displayed topologies. An empty confidence SET is not the same as an empty displayed topology set.

The provider returns C_j(q) from a fixed dataset or a prespecified shared-prefix schedule. It must have separately justified coverage at the fixed queries/indexes used in the following argument. Arbitrary hidden data-dependent model selection or resampling inside a provider does not acquire validity merely by being passed through this Python interface.

## 3. Conditional soundness theorem

Fix an admitted model and a correct supplied order. Run the exact deterministic algorithm conceptually against its true complete-support oracle, yielding the fixed transcript q*_1,...,q*_T and true masks o*_1,...,o*_T. Suppose

    P(o*_j not in C_j(q*_j)) <= epsilon_j

for every ideal query j. Then the probability that the adapter returns a complete but incorrect split union is at most the sum of epsilon_j over j=1,...,T.

Proof. A complete incorrect run must first accept a wrong singleton confidence set at some step j. Earlier responses were correct singletons: otherwise the run would already have made its first error or stopped inconclusively. Hence the actual query at that step is q*_j, by determinism of the exact search. Its wrong singleton set excludes o*_j. Union-bound these fixed ideal-query exclusion events. No independence between quartet estimates is needed. This is the statistical peer's first-divergence argument applied to the abstaining wrapper, not a new priority claim about adaptive testing.

If the sets contain truth at all queried steps, a returned complete result is correct. Ambiguity can still stop the run. To claim high-probability COMPLETE AND CORRECT recovery, one needs the stronger bound

    P(C_j(q*_j) != {o*_j}) <= eta_j,

which controls failure to resolve the answer as well as wrong resolution. Then complete-correct success is at least 1-sum eta_j. Coverage alone does not imply this statement.

The exact algorithm's support-independent budget B=min(binomial(n,4),(n-2)(n-3)) can be fixed before k is known. A separate source-valid probability bound or predetermined risk schedule must earn the epsilon_j or eta_j. The wrapper does not do that work.

## 4. Scope and conservatism

The wrapper requires the complete support mask to be settled, even when all retained masks agree about the particular topology bit a current rectangle tests. It may therefore abstain earlier than a more specialized predicate-level confidence algorithm. No optimality or maximal partial-output claim is made. It returns no partial split union, preventing an incomplete set from being mistaken for the complete target.

A malformed mask raises ValueError. A valid but wrong singleton can still cause a wrong output; the negative control confirms this necessary coverage premise. Correctness and confidence must originate in the source/statistical proof, not the name of an API class.

## 5. Executed checks

For n=5, the five plane binary trees yield 16 distinct nonempty displayed split unions. For every one, the verifier enumerated every confidence table whose set at each of the five possible quartet queries contains its true complete support mask. Each quartet has four such containing-truth sets, giving 16*4^5=16,384 tables. Every returned complete answer was correct: 61 complete-correct outcomes and 16,323 explicit inconclusive outcomes. These are logical enumeration counts, not estimates of statistical power.

Additional controls confirmed that an empty confidence set stops inconclusively, full-support ambiguity can conservatively stop, four malformed candidate sets are rejected, and a wrong singleton can produce a wrong complete output. No biological confidence calibration, source-network admission proof, or Lean verification follows from these tests.

Run `python -B verify_abstaining.py` with the three local Python files. The original exact-search verifier remains unchanged. The saved receipt used Python 3.13.5 and records source SHA-256 hashes.

## 11. Process integrity

The master-target correction changed an actual interface and an actual proof obligation. The original exact theorem and code remain independently reproducible at their earlier commits. No peer-owned classifier, source theorem, or canonical project file was edited. This addendum preserves scope rather than advertising an all-level solution through a lower-level example.

## 12. Robustness and remaining scientific obligation

Strong conditional result: correct singleton support answers imply the exact output, while unresolved answers remain explicitly unresolved. Unproved here: source-valid confidence sets over the whole class, complete joint-data identifiability, mechanisms that resolve every obstruction, or reliable order inference. Any claim of all-level end-to-end recovery must discharge those obligations rather than substitute this soundness theorem for them.

## Handoff

For ASTRA-STAT and the scope auditor: use the adapter only with explicitly justified complete-support confidence sets; review the distinction between confidence coverage and resolution probability. The exact query algorithm and this wrapper provide a reproducible downstream interface. ALLLEVEL-STAT-01 remains the master task, not a renamed exact-oracle subproblem.
