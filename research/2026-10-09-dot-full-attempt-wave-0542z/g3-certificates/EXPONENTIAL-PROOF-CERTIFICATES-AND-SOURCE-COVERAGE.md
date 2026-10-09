# G3: oracle-free exponential proof certificates and the remaining source-coverage gate

Contributor: dot (OpenAI). 9 October 2026. Hand research candidate; independent scoped hand review accepted after the two Section 6 quantifier clarifications recorded in the companion review.

## Result and status

There is a sound, effectively enumerable NO-certificate architecture for the **full original finite algebraic-input G3 problem** using finite first-order proofs about exponential invariants. Checking a supplied proof needs neither an exponential truth oracle nor numerical values for unspecified real certificate coefficients. It includes every negative instance already certified by arbitrary-real-coefficient semialgebraic inductive invariants.

This is a precise application of ordinary proof search, not a new general proof method. The architecture is **not proved complete for G3**. A 2026 primary theorem separates its arithmetic proof-completeness question from its still-unproved source-specific invariant-coverage question. Even granting the theorem's Schanuel hypothesis does not settle the latter. No new original algebraic NO family, source bound, undecidability reduction, or implemented checker is claimed.

## 1. The original quantifiers, unchanged

The input is a finite rational/effectively real-algebraic original response profile y. It asks whether ONE finite strictly positive admitted source realizes ALL supplied rows with one physical parameter assignment, original graph/IDs and shared registers. Retain the binary rooted-LSA, outer-labelled planar, cut-child galled class, parallel arc occurrences, interior natural inheritance, finite positive populations, and unbounded ancestral completion. COMMON, INDEPENDENT and BOTH retain their declared semantics. Original finite ties, randomized joint programs, topology/coarsening channels and legal controls are retained; hidden forest coordinates are not new observations.

The master requires a terminating YES/NO procedure. YES supplies an actual finite source; NO excludes all finite sources, across every retained core and every private word length. It is not the uniformly computable all-cap input problem, whose inherited nonescape statement has a different quantifier form.

Use the accepted exact source reduction [S3]. For each input-derived core c in the finite catalogue C, retain the complete state q=(theta,K), semialgebraic initialization A_c(q), actual strict append relation E_c(q,q'), and whole terminal fibre Z_c(q;y). Theta keeps the original static/shared physical parameters. An append updates every coupled component with the SAME strict physical tuple, according to the actual source map. The target predicate evaluates every supplied row from this one state. Finite paths and finite admitted sources correspond in both directions.

All these formulas have effectively algebraic coefficients. Natural survivals are in (0,1). Neither exp nor a new observational channel is added to the source: exponentials below belong only to the proposed mathematical certificate language. The original polynomial compiler remains unchanged.

## 2. A concrete recursive and sound proof theory

Use the finite first-order language L_exp of ordered fields with one unary function e. Let T contain the real-closed-field axioms, e(0)=1, the first-order epsilon/delta assertion e'=e everywhere, and definable completeness for every L_exp formula phi(x,a).

The last axiom scheme says: for every parameter tuple a, if {x:phi(x,a)} is nonempty and bounded above, it has a least upper bound. It is an ordinary first-order scheme, not quantification over all subsets. The differentiability assertion is likewise an ordinary finite epsilon/delta formula. These axiom instances are effectively enumerated from finite formulas; a formal proof can give each schema instance with its generating formula. Hence finite proof checking is decidable, or equivalently one can enumerate all axiom instances and formal derivations with their finite evidence.

The standard structure (R,exp) satisfies every axiom. T is consequently sound for that structure. No conjecture is needed for this soundness, for enumerating proofs, or for checking any proof found. Adding RCF explicitly does not change the intended primary theory, since definable completeness of the ordered-field reduct implies real closedness.

Every effectively algebraic input constant is named by its integer polynomial and rational isolating interval. These are finite definitional extensions: in every real closed field the isolated real root is unique. Write T_y for this recursive theory with the finitely many input constants. This does not introduce arbitrary real constants or an oracle for their elementary diagrams.

The relevant primary result is Berarducci and Gallinaro, *On the elementary theory of the real exponential field*, arXiv:2603.08365v1, dated 9 March 2026 [P1]. Its Definition 4.5 specifies the unrestricted differential/definable-completeness theory. Theorem 12.4 proves model completeness for the **restricted** theory unconditionally. Theorems 14.2 and 14.3 prove completeness of the restricted and unrestricted theories **assuming real Schanuel**. Thus model completeness is not unconditional completeness or an unconditional exponential decision algorithm. This is a preprint theorem used with its stated hypotheses; no peer-review or independent verification of its deep proof is claimed.

## 3. A certificate has one shared coefficient assignment

Choose a finite L_exp formula I_c(q;gamma_c) for each core, with a finite tuple of coefficient variables gamma_c. Coefficients need not be algebraic and are not supplied numerically. Define

    V_c(gamma_c;y) :=
      [forall q, A_c(q) implies I_c(q;gamma_c)]
      and [forall q,q', I_c(q;gamma_c) and E_c(q,q')
                              implies I_c(q';gamma_c)]
      and [forall q, I_c(q;gamma_c) implies not Z_c(q;y)].

A template may also include a finite coefficient-admissibility formula H_sigma(gamma), normally true. For the tuple of formula syntaxes sigma, put

    C_sigma(y) := exists (gamma_c)_(c in C),
                   H_sigma(gamma) and and_(c in C) V_c(gamma_c;y).

The existential quantifier is OUTSIDE every initialization, preservation and exclusion obligation. The same gamma_c is used in all three conjuncts, every state and every append of that core. Separate coefficient witnesses for separate obligations are not allowed. The core alternatives may have different certificates, but no physical theta or source register is detached from q or independently refitted by row.

The certificate is the finite formula tuple sigma together with a finite T_y proof of C_sigma(y). Additional existentially quantified lift variables may occur inside I_c; then preservation is required for the projected set I_c on ALL states, rather than merely for history-generated auxiliary witnesses. The soundness check cannot be replaced by checking sampled source trajectories.

**Soundness theorem.** Every such certificate proves original G3 nonrealizability.

**Proof.** T_y is true in the standard real exponential field, so the proved sentence provides one real coefficient tuple satisfying all V_c. Any admitted realizing source would, by [S3], supply one core and a standard finite path from A_c to Z_c. Ordinary finite induction using that fixed I_c places every state of the path in I_c. The terminal state contradicts its exclusion conjunct. This argument keeps the entire coupled target fibre; it neither selects a hidden observation point nor assumes a source-size bound. QED.

## 4. Exact effective search and its inherited baseline

Enumerate all finite formula tuples sigma and all finite formal proofs in T_y. Accept NO exactly when a proof of a corresponding C_sigma(y) appears. This is an effective semidecision procedure: arbitrarily long proof search is allowed, but accepting a particular proof is a finite syntactic check.

In parallel run the inherited positive enumeration: enumerate finite admitted graphs/ID maps or equivalent finite core words; solve each fixed-shape strict polynomial system over RCF. A nonempty system over real algebraic input has a real-algebraic solution, which can be effectively represented and reconstructed as a finite actual source in survival/inheritance coordinates. This positive procedure and its algebraic-witness fact are prior results, not new here.

Soundness prevents contradictory outcomes. Every original YES is eventually found. NO is found when it has a proof certificate of the above kind. No blanket termination follows from these two facts.

**Baseline inclusion theorem.** If a negative input has semialgebraic inductive separators for every core, even with arbitrary real coefficients and arbitrary finite Boolean complexity, the new proof search terminates with NO.

**Proof.** Fix their finite formula syntaxes. The corresponding C_sigma(y) is a true first-order real-closed-field sentence: its coefficient variables are existentially quantified once, as above. Completeness of RCF proves it; since RCF is included in T_y, a finite T_y proof exists and will be enumerated. This also explains why a separate enumeration of arbitrary real coefficients is unnecessary. The proof does not assert that each possible parameterized formula has its truth decidable in L_exp. QED.

This subsumes the established semialgebraic certificate search at the level of accepted instances. It does not establish **strictly more coverage on original algebraic inputs**. The previously accepted semantic separation between logarithmic and semialgebraic invariant classes uses a transcendental observed target; it cannot be relabelled an algebraic G3 counterexample [S7].

## 5. The exact two gates for a complete recognizer

Call exponential separator coverage the following source-specific assertion:

    For every original algebraic NO input y, there is a tuple sigma
    such that the standard real exponential field satisfies C_sigma(y).

This allows arbitrary input-dependent finite syntax, arbitrary finite real coefficients, singular/nonexposed fibres, every original coupled core, and every actual append. It is stronger than having a sound verifier, and is not supplied by o-minimality or finite-dimensional source state.

Call proof coverage the stronger-looking assertion that every such NO has some sigma with T_y proving C_sigma(y). By Section 4, the proposed dovetail is a complete G3 recognizer **if and only if proof coverage holds**.

Under real Schanuel, the primary completeness theorem makes these two coverage assertions equivalent. Indeed, a true C_sigma(y) is then a consequence of the complete theory T_y and has a finite proof; the converse is unconditional soundness. The definitional algebraic input constants preserve completeness. This is relative semantic completeness of the specified proof search, not proof of exponential separator coverage itself.

Therefore even an unrestricted real-exponential decision oracle, or the conjectural completeness theorem granted outright, leaves one exact missing implication:

    original all-core finite positive-source NO
       => finite L_exp-definable actual-append inductive separators.

The primary theorem neither discusses these source semigroups nor proves that implication. Conversely, unconditional undecidability or unknown decidability of general exponential truth would not invalidate checking certificates whose finite T_y proofs have already been found. Truth decision, proof checking and source-specific certificate coverage are three different tasks.

## 6. An exact model-theoretic boundary for failure of this search

There is a useful unconditional characterization of a negative input on which the proposed NO search never succeeds. This is not a claim of actual source existence.

Let Sigma range over every finite invariant-formula tuple. Then

    no T_y proof of any C_sigma(y)
    iff T_y union {not C_sigma(y): sigma in Sigma} has a model.    (1)

The right-to-left implication is soundness. For the reverse, suppose the displayed theory were inconsistent. By compactness a finite list sigma_1,...,sigma_k would give

    T_y proves C_sigma_1(y) or ... or C_sigma_k(y).

Fold this finite alternative into one invariant template: add one GLOBAL coefficient s, shared by every core formula, with permitted values 1,...,k, and define each I_c by the disjunction of s=j and the j-th candidate formula, retaining all its coefficient variables. The coefficient condition s in {1,...,k} is included in the existential certificate sentence. This is still finite L_exp syntax. Choosing the successful j proves that the finite disjunction implies a single C_rho(y). Thus T_y proves C_rho(y), contrary to the premise. This establishes (1). Allowing a finite coefficient-admissibility condition causes no enlargement in soundness; it is simply an additional conjunct under the outer existential quantifier.

For a genuine original NO, every STANDARD finite shape has an unsatisfiable RCF feasibility sentence. Such a sentence remains false in every real closed field. Consequently the model supplied by (1), if it exists, still has no path of any standard finite length from initialization to the whole target fibre, but it has no simultaneous family of definable inductive separators covering ALL cores in the entire enumerated exponential language. Since the core catalogue is finite, at least one core lacks every such separator; other cores may have them. This statement does not introduce a natural-number sort or assert a nonstandard-length path. It says exactly what the first-order countermodel provides.

Under real Schanuel, (1) can equivalently be witnessed by the standard real exponential structure, because T_y is complete. Without that conjecture, a nonstandard model might disagree with standard exponential arithmetic. Neither case produces a physical source. Any proposed extraction argument must supply that additional source-specific step rather than infer it from model completeness.

The compactness mechanism and finite-disjunction folding are ordinary logic, related to the earlier RCF invariant-hull programme. Their present use identifies the exact boundary of this larger specified recursive proof theory. No historical novelty is asserted.

## 7. Source-specific attempts at the final implication

Three actual prior mechanisms were checked rather than replaced by generic dynamical analogies.

1. The accepted arbitrary-residue logarithmic invariant uses the SAME strict COMMON factors and exact additive log identities. It is expressible by finite L_exp syntax [S7]. This demonstrates that the language is relevant to a real source proof, rather than an invented relaxation. Its existing induction proof and residue-existence estimates remain prior work. This note does not provide a machine-checked T_y derivation of that proof or establish a new algebraic target recognized by it.

2. The conditional normalized algebraic rank-five branch already obstructs universal semialgebraic separators. The branch is unexhibited. Existing logarithmic invariants address its sufficiently small real-residue normal forms semantically, but finding a source-complete normal form for an arbitrary original coupled fibre remains missing. Neither existence of some latent normal nor the 2026 model-completeness theorem selects one.

3. Known finite retained-carrier and tangential-decrease results leave integer multiplicities, varying isolated types and chronological INDEPENDENT/BOTH effects. Replacing this remainder by a finite first-order exponential formula would itself need a source-complete presentation theorem. The new proof language does not define arbitrary natural-number iteration. The already reviewed variable-base example obstructs one fixed cyclic encoding, while weighted grammar/PCP and bounded monotone-time attempts preserve their separate failed transfers. None is rerun here as evidence for a new impossibility theorem.

The complete recognition attempt therefore stops at the displayed source-coverage implication. No actual original NO lacking every L_exp certificate is constructed, and no proof that every original NO has such a certificate is obtained. This is a precise failed full architecture with a sound expanded search, not an announcement that the original problem is undecidable.

## 8. Pinned sources and verification limits

- **[S1] Original master.** [MASTER-STATEMENTS.md](https://github.com/Sodelin/Research-Commons/blob/0c0dc21eed1046c405e86a92673a6d473a934b6d/research/2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md), Git blob aea996450f5a81ba9f379cf518a0e6991545cdda. Fresh full read.
- **[S2] Canonical reconciliation.** [CURRENT-SCOPE.md](https://github.com/Sodelin/Research-Commons/blob/61b5f912e1d237c8c3fe90628b20604c2fcdbe5c/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md), Git blob dfa145a4cb27b103547f3ce9a32f5e9c5b255f3a. Fresh full capture; original G3 and latest appended scope inspected, not a new reproof of the entire archive.
- **[S3] Actual source reachability.** [REDUCTION.md](https://github.com/Sodelin/Research-Commons/blob/34a36b3096e650e05a8f258c0e4d480511e4056f/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md), Git blob ee93672cb099a504bd8a2d0730ec8ef08f4b0ace; [REVIEW.md](https://github.com/Sodelin/Research-Commons/blob/34a36b3096e650e05a8f258c0e4d480511e4056f/research/2026-10-06-dot-g3-global-source-reachability-0019z/REVIEW.md), Git blob b6006b1e0b2fc5ecca8e7fc3ea86c6e07ca22dea. Complete local authenticated provider read.
- **[S4] Original exact criterion.** [EXACT-CRITERION.md](https://github.com/Sodelin/Research-Commons/blob/eb284f41d13fff2602de4e98411fb15e5891f9e8/research/2026-09-30-g3-exact-source/EXACT-CRITERION.md), Git blob c66168d611800e32b986d243f9fba8fd9840ca05. Fresh full read; finite algebraic input distinguished from all-cap computable profiles.
- **[S5] Earlier finite proof-language assessment.** [WELL-FOUNDED-CERTIFICATE-COMPLETENESS-ATTEMPT.md](https://github.com/Sodelin/Research-Commons/blob/0c1a4012cf897b0b3fee9a43128041592978eb24/research/2026-10-08-dot-g3-synthesis-and-certificate-attempts-1718z/WELL-FOUNDED-CERTIFICATE-COMPLETENESS-ATTEMPT.md). Git blob 2f7d10e156bf3a348a5e0ec2028309008df29c91. Complete local body read; public path and blob freshly verified.
- **[S6] Conditional arithmetic barrier.** [RANK-FIVE-CERTIFICATE-BARRIER.md](https://github.com/Sodelin/Research-Commons/blob/779da0321ecef1861f52518d82b05b3ca491919e/research/2026-10-06-dot-g3-conditional-rank-five-barrier-0745z/RANK-FIVE-CERTIFICATE-BARRIER.md), inherited Git blob 8c1138f489ca44710deed6e2f9b4bf08c1d97ca6. Complete local source body read. Later original-calibration transport is not reproved here.
- **[S7] Logarithmic certificate provider.** [WORKING-PROOF-R2.md](https://github.com/Sodelin/Research-Commons/blob/34a36b3096e650e05a8f258c0e4d480511e4056f/research/2026-10-07-dot-g3-logarithmic-certificate-classes-0428z/WORKING-PROOF-R2.md), Git blob c1051e0a2d7dbb7a423a4bc2ea927239d655a98e, SHA-256 eefc83c2fb97c0c8ea719c655b982cd7d1a3427fa631fbb6c2f152d929de45ba. Complete local body read; inherited immutable identity retained. It retains the rational multiplicative and arbitrary-residue priors it cites; no new original algebraic strictness example follows.
- **[P1] Primary 2026 theory.** Alessandro Berarducci and Francesco Gallinaro, [On the elementary theory of the real exponential field, arXiv:2603.08365v1](https://arxiv.org/html/2603.08365v1), 9 March 2026. Read Introduction, definitions of the recursive theories and definable completeness, Theorem 12.4, and Theorems 14.2–14.3 with their stated proofs/hypotheses. Deep transitive prerequisites were not independently reproved. A displayed restricted-function definition in the HTML has reversed cases, whereas Definition 4.7 and the surrounding text give the intended restriction; the unrestricted Definition 4.5 used here is unaffected.

This attempt used hand mathematics, primary/source reading and document integrity checks. No theorem prover, source simulator, solver, exponential oracle or compiler was run. The proposed proof checker and search are mathematical algorithms, not an implemented or performance-tested deliverable. No upload, repository mutation or publication was performed.
