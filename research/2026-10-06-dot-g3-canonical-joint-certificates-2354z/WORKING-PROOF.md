# Canonical one-slot invariants are cofinal for whole-fibre semialgebraic certificates

Contributor: dot (OpenAI), 6 October 2026. Hand candidate for independent review. This strengthens the accepted set-theoretic product-hull identity to a uniform statement about finite certificates. It does not prove that every negative input has such a certificate or supply a general G3 recognizer. No QE or certificate hierarchy has been executed.

## 1. Fixed source system and finite templates

Fix cap M and the one-slot carrier C=(0,1)^(M−1), with exponents λ=binom(j,2), j=2,...,M. Initializations are all x_λ=A^λ, 0<A<1. The full append menu is

    U(x;s,p,q)_λ=s^λ(1−p+p q^λ)x_λ, 0<s,p,q<1,
    V(x;s)_λ=s^λ x_λ, 0<s<1.

These are the exact independent fresh COMMON transitions of the accepted method audit. Their finite reachable set is S_M. All data in this transition system are polynomial over Q. The source normalization and ordinary/equal-arm case retain their previously proved physical meaning.

For a positive integer n, let F_n be the finite collection of Boolean FORMULA SHAPES using at most n polynomials of total degree at most n in the slot coordinates. For each polynomial, include all monomials of that degree range and leave every coefficient as an independent real parameter. One explicit finite encoding enumerates Boolean truth tables on the three signs of n polynomials; zero coefficients and ignored atoms allow smaller formulas. This covers every semialgebraic set of the stated atom/degree complexity with arbitrary real coefficients. Arrange the classes nested by padding with ignored zero polynomials.

For shape σ write P_σ(c,x), relative to C, where c is its finite real coefficient vector. Let Valid_σ(c) be the conjunction that P contains every ordinary initialization and is preserved by BOTH append families at every carrier point. This is a finite first-order RCF formula over Q. It contains no target data and no enumeration of word lengths.

Define

    J_n={x∈C: for every σ∈F_n and every real c,
                    Valid_σ(c) implies P_σ(c,x)}.          (1)

Thus J_n intersects all valid invariants of these finite shapes, including an infinite continuum of coefficient choices.

## 2. Effective canonicalization and coefficient elimination

Each J_n is an effectively computable semialgebraic set over Q. Formula (1) has finitely many quantified coefficient variables for each of finitely many shapes; RCF quantifier elimination produces a finite quantifier-free formula with rational coefficients. This is an algorithmic theorem, not a performed computation or a practical complexity claim. The resulting formula may have much higher degree and atom count than n.

Every J_n is itself an inductive invariant containing every initialization. Indeed each valid member of the intersection has these properties, and arbitrary intersections preserve them. Equivalently the quantified formula proves preservation directly. Empty valid-parameter sets contribute the whole carrier. Also J_(n+1)⊆J_n.

If P is ANY one-slot semialgebraic invariant with arbitrary real coefficients, then P is represented by some shape in F_n for sufficiently large n. Consequently J_n⊆P. In particular, any real-coefficient separator can be strengthened to a rational-coefficient semialgebraic invariant without referring to its target, even if that target is transcendental. The strengthening may increase formula complexity. This is stronger than same-template coefficient transfer on an algebraic target, and uses the universal coefficient intersection rather than an unjustified algebraic approximation of the given coefficients.

Writing H for the intersection of all real-coefficient semialgebraic one-slot invariants,

    H=intersection_(n≥1) J_n.                             (2)

The equality provides no finite stabilization, semialgebraicity or computability assertion for H itself.

## 3. Uniform product cofinality

Now use e independently appendable copies of the same slot system, and static legal parameters θ∈Θ, with Θ semialgebraic over the exact input field. Initialization ranges over every θ and every ordinary tuple. Each append changes one slot, leaving θ and the others fixed. Let P⊆Θ×C^e be ANY semialgebraic joint invariant containing these initializations, with arbitrary real coefficients and arbitrary polynomial coupling between its variables.

**Theorem.** For some finite n,

    Θ×J_n^e ⊆ P.                                         (3)

Choose a finite Boolean polynomial description of P and let n bound the atom count and degree of every one-slot section obtained by fixing θ and the other slot coordinates. This choice is uniform over the specialized values. Specialization may make coefficients transcendental or zero, but (1) ranges over all real coefficients and permits zero polynomials.

For any fixed θ*, the section P_(θ*) contains S_M^e by physical induction. Fix all but the first coordinate at actual source words. The first-coordinate section is a valid one-slot invariant of a shape in F_n, so contains J_n. Therefore P_(θ*) contains J_n×S_M^(e−1).

Inductively suppose P_(θ*) contains J_n^k×S_M^(e−k). Fix the first k coordinates at arbitrary points of J_n and the last e−k−1 at actual words. The next one-slot section contains every actual word by this maintained inclusion, hence every initialization; it is invariant because P is invariant. Its formula still has the same uniform complexity bound. It therefore contains J_n. After e steps, P_(θ*) contains J_n^e. The choice of n did not depend on θ*, proving (3).

This is a finite uniform cofinality statement, not merely the earlier equality of pointwise intersections. The product may be a strict subset of P; this is a sound strengthening because it still contains all source tuples and remains invariant.

## 4. Exact consequence for one coupled target fibre

For any target set T⊆Θ×C^e, the following are equivalent:

    (i) Some semialgebraic joint inductive invariant P excludes ALL T.
    (ii) For some finite n, T∩(Θ×J_n^e) is empty.           (4)

The forward implication is (3). For the reverse, Θ×J_n^e is itself a joint semialgebraic inductive invariant. The logical equivalence does not require T to be algebraic. When T is the faithfully compiled algebraic/semialgebraic joint fibre, each finite test in (ii) is an RCF decision. All static constraints, shared registers and observed equations remain together in that test.

Thus the finite-template NO-certificate search can be organized with one canonical sequence of one-slot invariants. It loses no expressive power from ANY cross-slot polynomial invariant in this class. This does NOT authorize independent rowwise feasibility tests: the intersection in (ii) is the ENTIRE coupled target fibre against one product set. The disjointness of separate projected fibres is a different question.

For a finite valid core catalogue, apply the same test to every surviving core with its complete target equations and licensed slots. If all cores have semialgebraic certificates, sufficiently large finite stages reject them all; a common stage can be taken by increasing n because the sequence is nested. This remains relative completeness for the certificate class, subject to the original source/compiler interface. No general catalogue or hierarchy was run here.

## 5. Precisely what remains unproved

The result does not infer (4) from pointwise disjointness T∩(Θ×H^e)=empty. Taking an infinite descending intersection and excluding an entire target fibre need not admit a finite stage by compactness alone, because the invariants need not be closed. It also does not prove that every negative algebraic fibre avoids Θ×H^e in the first place.

The already accepted prefix/transcendental-residue obstruction and H nondefinability remain unchanged. In particular the canonical sequence cannot be replaced by an exact single o-minimal exponential description of H. The new rational-residue certificates ensure that the old small-loss family is eventually rejected at finite stages, but the stage may grow without a cap-only bound, consistently with the old denominator-degree obstruction.

The next master obligation is now exact: for every genuinely negative admitted algebraic fibre left after cut-cover elimination, prove the finite-stage emptiness in (4), or exhibit a negative fibre for which no such stage exists and pursue another certificate class. Neither alternative is settled by this note. No input-computable actual source bound, universal SC, arbitrary recognizer impossibility or INDEPENDENT mechanism result follows.

## 6. Attribution and evidence

This is a direct combination of classical RCF quantifier elimination, universal coefficient elimination and the previously accepted section argument. The method audit has proof67320d246b3c29fd6769c284e02f4917266b571f11250e227dbb593b73a4e7db / review084acec1f5d1f75c9931cb19fbc1435248ddda7815e6c7b3541c22773bc96714. The pointwise product-hull predecessor is proof4237815f84b50c7674d9a2b3b87a62a1fb6030d1d5cda2bad924898977158f72 / review256e0d4d75c68c1b3bf42c0a38d8e94a2d8ed9116afc28326364b0ab5e0caa9b.

Classical invariant-template synthesis is already credited in those notes to Colón–Sankaranarayanan–Sipma and the precise fixed-matrix work of Fijalkow–Ohlmann–Ouaknine–Pouly–Worrell. Their specialized completeness results are not being imported. The addition here is the target-independent canonical intersection and finite uniform product cofinality for this source-defined certificate system. Historical novelty is unresolved.

No coefficient synthesis, quantifier elimination, source enumeration, execution or formal verification was performed. The statement remains a hand candidate until the separate independent review is saved.
