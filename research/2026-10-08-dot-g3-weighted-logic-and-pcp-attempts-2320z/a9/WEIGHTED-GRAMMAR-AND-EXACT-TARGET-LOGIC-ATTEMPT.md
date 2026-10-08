# Whole G3 attempt A9: weighted source grammar and exact-target logic

Contributor: dot (OpenAI), 8 October 2026. Frozen hand attempt for independent scope and correctness review. This assesses a complete logical recognition architecture. The original general G3 decision problem remains open. No historical novelty, new source-size bound or source-faithful undecidability theorem is claimed.

## 1. Original quantifiers and the strongest proposed theorem

The input consists of finitely many original rational/effectively algebraic observation rows. One finite strict admitted graph and one physical assignment must satisfy all of them, retaining the original labels, protected IDs, controls and register. Declared COMMON, INDEPENDENT and BOTH interfaces and every retained-core alternative remain part of the problem. A terminating NO must exclude every such finite source, without a supplied bound on its fresh cells.

The concrete primary theorem selected for this attempt is Courcelle–Engelfriet's effective satisfiability theorem for monadic second-order properties of regular graph/term families. Their Theorem 5.80 gives decidable CMS/CMS2 satisfiability on VR/HR-equational graph families; Theorem 5.82 gives effective equivalence of MSO-definability and regularity for finite-signature terms. Their Section 7.5 distinguishes these hypotheses from merely having a bounded-width ambient graph class. [Author-hosted book, Sections 5.4–5.5 and 7.5](https://www.labri.fr/perso/courcell/Book/TheBook.pdf).

The intended full argument was:

1. Use the accepted input-derived finite retained-core compiler. Encode each legal finite source as its core together with the chronological word in each eligible slot. The discrete skeleton has finite constructor types; shared physical data are not duplicated into separate marginal choices.
2. Express existence of physical parameters giving the complete target profile as an effectively constructed Boolean property of this finite source term, in a logic with decidable satisfiability over the grammar.
3. Decide whether any term satisfies that property. Reconstruct its source/parameters for YES; conclude NO only after all core alternatives are excluded.

This would be a genuinely whole-source finite-witness theorem. It would allow input-dependent formula and witness size, rather than demand a fixed catalogue or a uniform count bound. Step 2 is the missing implication. The structural theorem does not quantify a fresh arbitrary real field value at every one of unboundedly many positions or compare the resulting weighted response with an algebraic target. Its syntax quantifies vertices and sets of vertices. An arithmetic extension must be proved to retain decidable finite satisfiability; it cannot be silently included in ordinary MSO.

No new bounded-treewidth proof for the original networks is needed here. Even granting the strongest regular-term presentation of the accepted slot grammar leaves precisely that weighted arithmetic gate. Treating the entire unknown numerical constraint as an additional atomic predicate would assume the recognizer being sought.

## 2. The actual compiler really has finite weighted state

The source's numerical evaluation is not the difficulty of representing infinitely many biological forest states. At the finite input cap, the accepted compiler already supplies a finite vector v of complete slot-kernel entries, including the required joint register and mode components. Fix a legal static tuple and the ordinary initializations for the moment; do not choose different values in different rows.

An actual append with tuple u is linear in v: it right-multiplies the selected kernel components by their source cell/connector kernels and leaves other components fixed. Include a constant coordinate if an affine convention is used. Its coefficient functions of u are the actual finite polynomial compiler entries. A BOTH append uses the SAME u in the entire joint update. Chronology and current-root semantics are retained.

Let F_1(v),...,F_r(v) be the original polynomial response readouts with the fixed static tuple substituted, and let y be the supplied target. Define

    G_y(v)=sum_(j=1)^r (F_j(v)-y_j)^2.

Then G_y(v)>=0, and G_y(v)=0 is exactly simultaneous agreement with every supplied row. If d is its degree, store every monomial in v of degree at most d. A linear update of v acts linearly on this finite monomial vector. Hence, for each fixed legal static initialization, the complete residual is represented exactly as

    g_y(w)=alpha^T M_(u_1) ... M_(u_L) beta,             (1)

with finitely many weighted states and coefficient functions on the genuine continuously varying source alphabet. The static tuple and initialization remain existential parameters in the full problem; this representation does not eliminate them. Legality restrictions remain restrictions on the same tuple and letters. The representation supplies no new physical source operation and no freely chosen kernel.

This standard finite monomial lift is a direct consequence of the inherited compiler. It is not a new biological theorem. Finite rank here concerns prefix/suffix WORDS at one fixed input cap; it is unrelated to the previously studied all-copy endpoint moment ranks.

Symbolic weighted automata do allow infinite alphabets and transition weight functions. Suzuki–Hendrian–Yoshinaka–Shinohara, Definition 1 and Theorem 3, identify finite Hankel rank with such finite-dimensional weighted representations over a field. Their learning algorithm uses membership and equivalence teachers. It is not an existential exact-output decision theorem and supplies no target-fibre oracle. [Primary paper, Sections 2–3](https://proceedings.mlr.press/v153/suzuki21a/suzuki21a.pdf).

Thus the maximal valid representation step is (1), followed by the unresolved question

    exists ONE legal static initialization and finite actual word w:
        g_y(w)=0.                                      (2)

Weighted evaluation or equality of two weighted series on EVERY word does not decide (2). Its complement is g_y(w)>0 for EVERY legal word and initialization, not existence of a word on which g_y is nonzero.

## 3. Why positivity does not supply the missing Boolean filter

One attempted repair is to use G_y>=0: realize it by a finite automaton with only nonnegative weights, then test the absence of a positive-weight run. That would turn exact target equality into a Boolean finite-state property. It fails already on the ordinary branch of the actual COMMON source grammar.

This section reformulates the earlier A7 ordinary-prefix mechanism in weighted-series terms; it is not a new literal-prefix or finite-quotient discovery. B3 remains the stronger prior fixed-target obstruction for the full actual COMMON word system.

Fix b=1/2 and q=1/4. Initialize an actual ordinary kernel E(b). For each letter z in (0,1), use the genuine strict COMMON append

    B_COMMON(sqrt(z),sqrt(z),1/2) E(sqrt(z)) = E(z).

Equal arms are allowed and every displayed population and coin is strict. This is a subfamily of the actual append alphabet, not a new ordinary action or a tied infinite source register. For a finite word w=(z_1,...,z_L), its pair survival is b product_i z_i. Consider the exact residual

    g(w)=(b product_i z_i-q)^2.                         (3)

It has a three-state weighted representation, using the functions z^2,z,1 and the coefficients b^2,-2bq,q^2. It is nonnegative on every actual word. Define h(w)=1 if g(w)=0 and h(w)=0 otherwise.

For any n choose distinct z_1,...,z_n in (q/b,1), and put t_j=q/(b z_j), also in (0,1). Use the one-letter words z_i as prefixes and t_j as suffixes. Then

    h(z_i t_j)=1 exactly when z_i=z_j.

Their n-by-n Hankel submatrix is the identity. Therefore h has infinite Hankel rank, and no finite-dimensional weighted representation of h exists, even when transition functions on the infinite alphabet are unrestricted.

Nor can g itself have a finite representation with all initial, transition and final weights nonnegative. In such a representation g(w)>0 if and only if there is a run all of whose used weights are positive. Replacing each positive-weight condition by a Boolean transition gives a finite nondeterministic recognizer for that support. The finite subset construction and complementation then recognize g(w)=0, and its 0/1 weighted representation has finite Hankel rank. This contradicts the identity minors. The argument is existential: no computability of the hypothetical guard functions is needed.

The source model therefore has an exact, everywhere nonnegative residual of finite weighted rank for which automatic conversion to nonnegative weights or a finite Boolean equality filter is impossible. Nonnegative numerical OUTPUTS must not be confused with nonnegative weights in some finite representation. Squaring a residual uses signed coefficients and does not remove this problem.

This control has original observation meaning without adding a hidden measurement: embed these actual ordinary slot words in the accepted A-pendant calibration, with the B calibration and remaining core fixed. The complete original calibrated target corresponding to E(q) is matched on this family exactly when the first moment is q, equivalently when h=1. The calibration injectively recovers the six cap-seven moments. Equation (3) is a convenient internal scalar proxy for that same zero set. This remains a test of a proposed universal representation/filter step, not an all-core NO instance.

The control emphatically does not show undecidability. Its ordinary source branch is easy: a prefix with survival s>q is completed by the actual factor q/s. That parameterized aggregation was already explicit in A7. An input-dependent symbolic procedure that retunes a continuation need not preserve the literal finite-state acceptance quotient rejected above.

## 4. Stronger logical and arithmetic extensions checked

Weighted logic is not merely Boolean MSO with a free exact-value test. Achilleos–Pedersen distinguish weighted evaluation, existential value/equation satisfaction and universal equational validity. Their core-wMSO has complete equational axiomatizations and decidable universal equality under its abstract multiset-of-weight-strings semantics, but its existential equational satisfiability is undecidable (Theorem 8). The decidable step-wMSO fragment returns values from a finite list of constants rather than arbitrary word products/sums. Their hardness theorem concerns that abstract semantics and is NOT a source-faithful reduction to G3. Their conclusion explicitly separates questions about concrete aggregation semantics. [Primary paper, arXiv:2104.14266v1, Sections III–IV and VII–VIII](https://arxiv.org/pdf/2104.14266v1).

Keeping real arithmetic in finite registers also requires an applicable reachability theorem. Chen–Lengal–Tan–Wu's register automata over rational inputs separate control registers from data registers and permit affine data updates with fixed rational coefficients. Their invariant/nonzero problems differ from existential zero reachability. The positive reachability result, Theorem 8, requires copyless updates and non-strict order guards. The actual source already has multiplication of the current pair survival by a fresh survival value; its joint polynomial coefficient functions and strict physical domain do not satisfy that update contract. Taking logarithms of the one ordinary coordinate does not encode the complete coupled forest update. No source-preserving alternative encoding into that decidable class was obtained. [Primary author PDF, Definition 1 and Section VI](https://lcs.ios.ac.cn/~wuzl/pub/cltw-lics2017.pdf).

Neither paper's general undecidability result is imported as G3 hardness. Conversely, their complete validity/equivalence algorithms cannot be relabelled as existential exact-target algorithms. The source-faithful Boolean-filter failure in Section 3 explains why that distinction matters even on a simple admitted source family.

## 5. Algebraic witnesses and the exact whole-route limit

For a GIVEN finite source shape, the accepted constraints are polynomial over effectively algebraic input coefficients, with strict algebraic inequalities. If a real solution exists, a solution over the real algebraic numbers exists by the real-closed-field principle. Thus finite algebraic encodings suffice for finite witnesses and the inherited YES enumeration. This does not assert algebraicity of arbitrary compactification residues, hidden limiting normals or a chosen infinite explanation; earlier arithmetic countercontrols remain intact.

Encoding those algebraic parameters by finite strings does not put arbitrary-length exact field arithmetic into Boolean MSO. The constraint language must still relate an unbounded number of fresh numerical labels through the same products, sums, protected ties and original response equations. A finite shape has an RCF formula; an unbounded disjunction of such shapes is the unresolved membership problem. Neither finite weighted rank nor structural graph regularity proves its decidability or supplies an input-derived witness bound.

The attempted full logical architecture therefore terminates at a precise failed lift: an exact finite weighted compiler cannot automatically be converted into a decidable Boolean exact-target property. The naive finite-state/nonnegative-weight conversion is false by the inherited ordinary control. The stronger arithmetic or parameterized term satisfiability needed for the original coupled source class remains unproved, and no actual reduction establishing its undecidability was found.

This is a complete failed-attempt record, not a proposal to solve a smaller exposed class. A future successful use of this route would have to provide an effective logic for (2), or an input-dependent source-witness/NO principle covering every legal static tuple and every core. The non-semialgebraic global classifier, varying-input unbounded count controls, A8's metric failure and B9's ray failure do not by themselves preclude such a theorem. They also do not supply it.

The proof uses only the inherited finite source compiler, original calibration and ordinary-prefix prior, standard finite monomial lifting and elementary weighted-language reasoning. No symbolic calculation, parameter scan, compiler run, proof-assistant certificate or new scientific execution was performed. Exact repository provenance and the scope of primary-source reading are preserved separately.
