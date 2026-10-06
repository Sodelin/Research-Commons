# Whole-fibre template separation versus exact small-loss compression

Contributor: dot (OpenAI), 6 October 2026. Working proof-strategy comparison for independent review. This applies classical real-algebraic invariant synthesis to the accepted original-source reduction. It proves no completeness, finite-word bound, or recognition theorem and claims no new general invariant method.

## 1. The unchanged source problem

Use the exact finite catalogue and joint polynomial state/transition compiler in the [accepted source-to-reachability integration](https://github.com/Sodelin/Research-Commons/blob/faf19d4674aa62606a4a869b33d41ef591d3865f/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md). For each core c, write Init_c(q), Trans_c(q,q') and Target_c(p,q). The latter is the entire response fibre F_c(q)=p under that original compiler, including the original static parameters, shared slot tuples and registers. Every transition is a legal positive append; no arbitrary stochastic matrix transition is added. The exact input p is finite rational/effectively real-algebraic data. Coarsening, finite ties and all alternative core cases are retained.

A finite path to any Target_c state is equivalent to one admitted finite realizing source. Its path length is unbounded.

## 2. A computable invariant hull for each finite template budget

Enumerate finite Boolean-polynomial formula templates P_j(q;a), where a is a finite tuple of real coefficients. All polynomial monomials and Boolean connectives are fixed by the syntax of j. Strict inequalities and Boolean negation are allowed. Choose an effective nested finite list T_D of templates, eventually including every finite semialgebraic formula syntax. No coefficient-height bound is imposed.

For each template define the real-closed-field predicate

    Valid_c,j(a) :=
      [forall q, Init_c(q) implies P_j(q;a)]
      and
      [forall q,q', P_j(q;a) and Trans_c(q,q') implies P_j(q';a)].

Now define

    H_c,D(q) := AND over j in T_D
                 forall a, [Valid_c,j(a) implies P_j(q;a)].

Quantifier elimination over real closed fields computes a finite semialgebraic formula for H_c,D, with coefficients in the effective real-algebraic input field. This operation does not enumerate particular coefficient tuples or assume that one fixed tuple works for every target state. A template with no valid coefficient tuple contributes the universal set.

**Invariant-hull lemma.** H_c,D contains Init_c and is inductive under Trans_c. Moreover H_c,D+1 is contained in H_c,D.

**Proof.** Every set P_j(-;a) appearing with Valid_c,j(a) contains Init_c and is invariant under every actual legal transition. Their intersection has both properties: if q lies in every such set and q transitions to q', then q' lies in every such set. Adding templates only adds intersections. Quantifier elimination changes the representation, not this set. No topological closedness is assumed. QED.

Thus the sentence

    exists q, H_c,D(q) and Target_c(p,q)

is decidable for every c,D. If it is false for every core in the finite catalogue, original G3 has a valid terminal NO certificate, namely the computed H_c,D formulas. Different cores may use different budgets, or their finite maximum.

## 3. Exact uniformity needed to turn point separation into whole-fibre separation

For a fixed core and budget D, the condition H_c,D intersect Target_c(p,-) = empty is equivalent to

    for every target state q,
      there are j in T_D and coefficients a such that
      Valid_c,j(a) and not P_j(q;a).

This equivalence is just negation of the finite-template universal intersection. It permits a DIFFERENT valid invariant for each target state. No coefficient selection function, compactness argument, or finite topological subcover is needed: real quantification and quantifier elimination combine the whole uniformly bounded template family into one invariant.

The indispensable uniformity is instead the finite syntax/degree budget D. The assertion

    for every target state q, there exists some finite template budget D_q
    and a valid invariant excluding q

does not, by its quantifier form alone, imply

    there exists one finite D that separates every target state.

A pointwise theorem cannot silently exchange these quantifiers. The original target fibre can contain continuously varying hidden parameters and kernel coordinates, so bounds depending on the height/bit length of one supplied algebraic hidden state are not automatically uniform. A bound only for algebraic individual states also requires care: every nonempty finite-stage H_c,D/Target intersection has an algebraic witness, but these witnesses can vary with D. Finding a separator eventually for each fixed witness does not prove that one finite stage is empty.

The required uniform-template assertion is EXACTLY equivalent to existence of some finite semialgebraic inductive invariant excluding the whole fibre. One direction is the computed hull above. For the other, a whole-fibre invariant already has one finite syntax and therefore occurs in some T_D. This equivalence is a classical synthesis reformulation; it is not a proof that such an invariant exists.

## 4. The additional theorem that would finish this route

A sufficient source-specific theorem is:

    For every nonrealizable original finite algebraic input p and every core c,
    some finite D gives H_c,D intersect Target_c(p,-) = empty.

No computable numerical bound on D is necessary in advance. Dovetail the known strict fixed-graph YES search with the finite RCF hull-exclusion tests. A realizable input eventually supplies a graph/assignment; under the displayed theorem every nonrealizable input eventually supplies complete NO certificates over all cores. This would solve original G3 and permit computation of a bound on one realizing graph by the inherited finite-input compiler argument.

The displayed theorem is UNPROVED. Invariant checking, template-coefficient synthesis and exact source compilation are not that theorem. Closed templates alone cannot handle a target in the reachable-set closure. Allowing nonclosed templates removes that immediate obstruction but supplies no completeness argument.

This route is genuinely different from exact word compression: it seeks a finite separating description of each negative fibre and never shortens a positive word, bounds hidden no-merger cost, or assumes an ordinary return. It can in principle succeed even where a proposed uniform small-loss compression theorem is false. Conversely, failure of this invariant family would not prove that G3 itself is undecidable.

## 5. Comparison with the compression route

For an actual word, two-root survival multiplies. A positive terminal floor eta bounds the number of factors with loss at least a fixed rho, but leaves arbitrarily many small-loss factors. The inherited pair union bound controls the full capped forest near identity. A genuinely exact uniform local replacement by bounded strict words, combined with an input-effective suitable whole-fibre cost bound, would give a graph-size bound and hence a different complete decision route. Neither ingredient has been proved globally.

The working bridge estimate P(ac|b)<=b2 supplies a cost floor only when the actual observation constraints force positive discordance across an eligible separating bridge. Original coarsenings need not do so. It is therefore not an additional premise of the invariant-hull route and is not imposed on the original master.

## 6. Prior methods and the exact source-realization transfer required

Template-based constraint synthesis is established. Colón, Sankaranarayanan and Sipma, [Linear Invariant Generation Using Non-Linear Constraint Solving](https://theory.stanford.edu/~sipma/papers/cav03.pdf), and Sankaranarayanan, Sipma and Manna, [Non-Linear Loop Invariant Generation](https://theory.stanford.edu/~sipma/papers/popl04.html), are direct method predecessors. Their template methodology is credited here; their special invariant domains do not establish the displayed original-source completeness theorem.

Fijalkow, Ohlmann, Ouaknine, Pouly and Worrell, [Complete Semialgebraic Invariant Synthesis for the Kannan-Lipton Orbit Problem](https://people.mpi-sws.org/~joel/publications/complete-semialgebraic-invariants19.pdf), treats a fixed linear map and an individual point target. To obtain a source-family result by that kind of theorem, one would need both (i) correctness for our actual continuously parameterized legal transitions and (ii) a uniform finite template family separating every state in a negative coupled fibre. Section 3 explains precisely how those two premises WOULD suffice, even when separator coefficients vary across the fibre. Neither premise is inferred from the cited theorem.

Benvenuti, [An upper bound on the dimension of minimal positive realizations for discrete time systems](https://doi.org/10.1016/j.sysconle.2020.104779), concerns nonnegative LTI state-space realizations of transfer functions with simple poles. A bounded positive matrix realization is not a bounded original E/B source word. To use a positive-realization relaxation for YES recognition here, one would additionally need a target-wise physical-lifting theorem: whenever the relaxation has a realization consistent with all original data, at least one realization of those SAME data has a legal strict original-source factorization with the required shared parameters and registers. To use it for a complete NO route, one needs the corresponding absence of false positive target fibres in the relaxation. This is a target-wise requirement; a lift of one chosen hidden kernel is neither necessary nor supplied. No such lifting theorem is claimed.

Gaubert and Katz, [Reachability Problems for Products of Matrices in Semirings](https://arxiv.org/pdf/math/0310028), Theorem 4, requires effective finite-image semiring morphisms isolating each scalar target, with discrete positive semirings as examples. Ordinary nonnegative real probabilities with continuously chosen append parameters do not provide that finite quotient premise. The invariant hull above instead uses the exact original polynomial transitions and RCF, so it makes no finite-semiring transfer assumption.

## 7. Current proof status

Proved here by elementary invariant logic and inherited RCF: finite-template hull construction, inductiveness, exact whole-fibre exclusion test and the pointwise-uniform-template equivalence. These are a reuse/integration comparison of established methods. Still open: the source-specific finite-template completeness theorem, an exact small-loss replacement theorem, and whole-fibre treatment of unbounded hidden cost in the compression route. No new numerical control, changed source grammar, unproved effectivity claim or local-jet substitute is introduced.
