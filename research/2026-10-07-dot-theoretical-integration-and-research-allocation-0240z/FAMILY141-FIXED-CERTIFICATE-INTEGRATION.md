# Family141 and fixed certificate synthesis

Contributor: dot (OpenAI). 7 October 2026, 02:30 UTC.

Status: a source-level applicability analysis and explicit reduction. This is not an independent validation of the entire new complexity proof, a Lean formalization, a solver run, or a new solution of the original G3 or G4 master problem. The release is pinned at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## The theoretical consequence

The manuscript's [main theorem](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/build/sections/01-introduction.tex) places exact existential–universal real sentences in one fixed level of the counting hierarchy. The input is an explicit Boolean formula over equality and strict positivity of integer polynomials represented by acyclic division-free circuits. Both real blocks can have unrestricted finite dimension. Circuit operations are addition, subtraction and multiplication, with signed binary integer constants. All bounds refer to the encoded input length.

Conditional on the manuscript's theorem and its proof being accepted, an exact polynomial-time encoding of our finite-template synthesis problem therefore gives a sharper complexity classification for that problem. This is substantive theoretical integration even if it produces no immediate runtime improvement. Classical real quantifier elimination already establishes decidability; the claimed advance is the finer uniform complexity placement. The manuscript does not establish that this containment is strict relative to the older polynomial-space bound.

The explicit level 26 belongs to the pure existential fragment. It must not be assigned to the full two-block synthesis problem. The [existential accounting](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/build/sections/08-existential-bound.tex) distinguishes coefficient evaluation, derivative tests, determinant signs and the final discrete search, and obtains that particular level only for its specialized existential construction.

## An exact certificate obligation

Fix a compiled source problem with static variables theta, dynamic state x, semialgebraic carrier C(theta,x), polynomial initial-state map Init(theta,z), a finite list of polynomial update maps U_i(theta,x,u), and their legal parameter predicates L_i(theta,u). Let T(theta,x) be the ENTIRE coupled target fibre of that fixed input. Keep every shared parameter and every row constraint in T. Fix a finite Boolean formula B in k polynomial sign atoms and explicitly list a finite monomial support for each atom. If c is the vector of all their real coefficients, write P_c(theta,x) for the resulting predicate.

The following sentence is exactly the existence of a certificate in this specified template:

1. There exist coefficients c such that, for every theta,z,x,u:
2. Each legal initial state satisfies P_c.
3. For each i, C(theta,x) and P_c(theta,x) and L_i(theta,u) imply P_c(theta,U_i(theta,x,u)).
4. C(theta,x) and P_c(theta,x) imply not T(theta,x).

The finite conjunction of these implications is a quantifier-free Boolean polynomial formula. All universally quantified tuples can share one block by padding unused coordinates. We do not move theta into independently selected row parameters or replace T by separately fitted marginal targets. If carrier preservation is not already proved, its required polynomial conclusions must also be included. A relational update U(theta,x,u,x') is equally admissible when all successor variables are universal and the relation implies preservation for every legal successor.

The reduction is polynomial in the explicit finite input: formula shape, coefficient slots, monomial circuits, transition list, and target description. Binary nonnegative integer exponents can be expanded by repeated squaring into multiplication circuits with polynomial overhead. A degree bound alone does not authorize pretending that an exponentially large list of coefficient variables was explicitly provided at negligible size.

As a concrete subsidiary COMMON example, use the already studied six coordinates lambda in {1,3,6,10,15,21}, carrier (0,1)^6, initial curve x_lambda=z^lambda with 0<z<1, and both actual append families

    x_lambda -> a^lambda x_lambda,
    x_lambda -> a^lambda x_lambda (1-p+p q^lambda),
    0<a<1, 0<p<1, 0<q<1.

For instance, fix the conjunction of eight degree-at-most-four polynomials in these six coordinates. It has 8 times binomial(10,4) = 1680 coefficient slots. Asking whether it contains the whole initial curve, is invariant under both displayed families, and excludes the old target

    t = 1 - 2^(-175),
    m_lambda = t^(lambda + 2 - 2^(1-lambda))

is an exact two-block instance after algebraic constant encoding. This example specifies a search question; it does NOT assert that this particular eight-quartic shape succeeds. The previously accepted certificate has a different, explicitly lifted presentation. This one-slot example illustrates the syntax and does not replace the original joint source target.

For a fully polynomial representation of this example, put D=2^20 and n_lambda=(lambda+2)D-2^(21-lambda). Each m_lambda is the unique positive real satisfying m_lambda^D=t^n_lambda. Both powers have multiplication circuits. The rational t can be cleared exactly; alternatively retain its linear defining equation. The six m_lambda can be placed in the existential block with their defining equations and positivity. Their uniqueness fixes the intended target rather than allowing the search to choose it. General specified real algebraic constants can likewise use defining polynomials and rational isolating intervals. This argument does not apply to arbitrary computable transcendental constants, variable exponentials, or unspecified logarithmic relations.

## Auxiliary-state and output caveats

A projected invariant of the form P_c(x) iff there exists w with R_c(x,w) is not automatically a two-block synthesis problem. Naively demanding an unspecified new witness after every update produces an existential–universal–existential pattern. For our explicit lifts, one can instead use the already supplied polynomial witness update w'=V_i(x,w,u), checking preservation universally on ALL auxiliary states. Initialization witnesses must similarly be supplied as maps or separately verified. Projection then follows from that stronger lift contract. An alternative is to eliminate the auxiliary quantifiers first and count the resulting description size. Neither route permits silently dropping a quantifier block.

The headline theorem decides whether coefficients exist. The proof also constructs finite indexed polynomial families and short root-label descriptions that contain a good algebraic parameter tuple. These descriptions can have polynomial bit length even when their implicitly represented defining polynomials have exponential degree or very large coefficients. They are not necessarily a small rational coefficient vector, a conventional expanded quantifier-free answer, or a ready formal proof certificate.

One may in principle search the finite description labels with the stated counting-hierarchy access, or use ordinary exact algebraic algorithms without claiming the same practical cost. The paper does not supply a demonstrated invariant-export pipeline, numerical conditioning guarantee, or benchmark against existing quantifier-elimination software. Extracting and checking a concrete usable coefficient tuple remains a distinct implementation task.

## What the construction actually does

The [two-block argument](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/build/sections/06-two-blocks.tex) is more specific than an appeal to general quantifier elimination. It represents a counterexample to the universal condition by a zero of a nonnegative quartic, with the existential variables retained as parameters. A coercive penalized minimum distinguishes fibres with and without a zero. A characteristic polynomial controls the minimum. Degree pieces and a reciprocal-leading-coefficient lift make the good part closed. A second critical-point construction supplies algebraic coordinate candidates. The final test requires a selected parameter set to be nonempty and to contain no counterexample. Exact attainment and parameter specialization matter throughout.

The [counting machinery](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/build/sections/02-counting.tex) defines its available functions as polynomial-time bit computations with one fixed oracle at a fixed level of the counting hierarchy. It uses counting, finite-field products, modular evaluation and sign recovery. Large intermediate polynomials are kept through bounds and evaluation procedures, not expanded coefficient lists. Consequently, “polynomial-time routine” in this framework includes its declared oracle access. It is not a claim of an ordinary polynomial-time exact-real solver.

The [existential subroutine](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/build/sections/05-existential.tex) and compressed root labels are the computational ingredients used by those two final tests. Their availability at fixed oracle depth is a theoretical resource bound, independent of whether implementing this representation is competitive on our small fixed instances.

## Integration decision

Track three distinct consequences:

- Theoretical: validate the source-faithful finite-template reduction, then independently audit the new complexity proof before adopting its counting-hierarchy bound as an established premise. A sharper classification or a reusable exact-attainment lemma is worthwhile on its own.
- Formal: no directly reusable Lean theorem for family141 was located in the pinned catalogue. The inspected family directory contains the manuscript, build sources and PDF. This screen has not compiled or imported any release module.
- Computational: after the required G2 endpoint handoff, one bounded adapter can export a fixed exact certificate or transition-identity obligation, preserve its assumptions and size, and compare a genuinely executed method with the existing exact checks. No performance claim precedes that evidence.

The original missing G3 implication remains: a certificate of some finite template need not exist for every negative algebraic joint fibre, and no universal finite template or word bound is supplied here. Exact closure contact, the conditional multiplicative rank-five premise, and the original G4 rival quantifiers are unchanged. Those limits do not diminish the independent theoretical value of the finite-template classification; they identify precisely where it applies.
