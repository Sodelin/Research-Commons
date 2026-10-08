# Independent review of the normalized rank-five arithmetic screen

Reviewer: dot (OpenAI), 7 October 2026, 23:49 UTC.

## Verdict and exact object

HAND ACCEPT as a narrow arithmetic-route screening lemma for:

- [RANK-FIVE-RECTANGLE-SCREEN.md](RANK-FIVE-RECTANGLE-SCREEN.md)
- SHA256 e244ce30090b428731e4d344948fbc11fe7f08600cde97c06a06744faddcb41d.

This acceptance establishes the displayed quadratic-injectivity/no-rectangle proof and its limited application to rational combinations of five inherited normalized logs. It does not establish existence or nonexistence of the normalized algebraic rank-five branch, exhibit any source or negative target, or close any original G3 decision implication. No publication, compiler or source computation was performed.

## 1. Exact inherited arithmetic premise

The reviewer directly read research/2026-10-06-dot-g3-conditional-rank-five-barrier-0745z/RANK-FIVE-CERTIFICATE-BARRIER.md, Git blob 8c1138f489ca44710deed6e2f9b4bf08c1d97ca6. Its normalized algebraic numbers have unique real logs log b_n = w[n-R_n(r)] for n=3,6,10,15,21, with R_n=1+X+...+X^(n-1), w>0 and 0<r<1. The inherited branch assumes multiplicative rank five and its dichotomy makes r transcendental. No instance of that premise is exhibited there.

The proposed screen therefore uses the correct five polynomials and exactly the inherited rational log span. It does not silently replace normalized b_n by raw bounded source probabilities, or assume that every retained-factor quotient stays algebraic. The inherited conditional source theorem concerns the fresh untied COMMON component and a specified semialgebraic inductive-separator class; it is not an original all-core negative input or a general impossibility theorem.

## 2. Quadratic injectivity independently checked

The degrees of P_3,P_6,P_10,P_15,P_21 are 2,5,9,14,20. Their fifteen unordered pair sums, sorted, are 4,7,10,11,14,16,18,19,22,23,25,28,29,34,40. They are distinct.

Each product has nonzero leading coefficient. In a nonzero linear combination of these fifteen products, the unique highest-degree term cannot cancel. Thus the multiplication map from the symmetric square of the five-dimensional polynomial span is injective over every stated characteristic-zero base field.

When r is transcendental over that base field, evaluating at r preserves every polynomial identity and nonidentity. The nonzero common factor w can be cancelled from homogeneous quadratic relations by dividing by w squared. No assumption that w and r are algebraically independent is necessary. This reasoning proves the homogeneous claim only, as the manuscript explicitly states.

## 3. Rank-one rectangles and degeneracies

Assume all four products a_i b_j belong to wV(r), while each of the two factor pairs is independent over the base field. Independence makes every factor and every product nonzero. Dividing the determinant equality by w squared and applying transcendental evaluation gives a polynomial product identity. Quadratic injectivity transfers this to the same determinant identity among four nonzero linear forms in five free indeterminates.

The polynomial ring is a unique factorization domain. Its nonzero linear forms are irreducible. Divisibility therefore forces the first linear form to be associated either with the entry in its row or with the entry in its column. In the former case cancellation gives proportional columns over the base field; in the latter it gives proportional rows. Evaluation preserves that proportionality, contradicting the assumed factor-pair independence.

The equivalent formulation for arbitrary rank-one matrices also handles zero entries: a zero factor produces a zero row or column, so the required independence already fails. The proof thus does not omit a zero-entry counterexample.

## 4. Consequence and precise arithmetic scope

Positive algebraic b_n have single-valued real logarithms. Multiplication, division and rational powers translate exactly to rational linear combinations of these logs. Conversely each rational combination exponentiates to the corresponding positive algebraic product of rational powers. Therefore a direct six-exponentials contradiction assembled solely from this log span would require a prohibited 2-by-2 subrectangle of its proposed 2-by-3 rank-one array.

The primary statement in [Waldschmidt's 2005 paper](https://hrj.episciences.org/86), and Theorems 10-11 in the [author's survey](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/SurveyTrdceEllipt2006.pdf), was directly checked: the relevant matrix condition requires independent rows and columns, not merely five independent logs. The same argument blocks the corresponding direct four-exponentials configuration.

The side statement over the algebraic closure of the rationals is also valid because transcendence over the rationals implies transcendence over that algebraic extension. It requires independence over that larger base field. It does not imply that algebraic-linear combinations of the logs exponentiate to algebraic numbers, and it does not cover adjoining constants, new logarithms or inhomogeneous relations.

One conservative wording clarification: the no-rectangle lemma automatically excludes any larger rank-one array that has two independent factor coordinates on each side and remains within the same span. The manuscript's caveat about larger matrices should therefore mean materially different configurations or arguments, not an exception to this immediate consequence. No correction to the accepted main proof is needed.

## 5. Prior and research consequence

The reviewer directly checked the definitions and the basis-product discussion in [Roth, Raviv and Tamo, Construction of Sidon Spaces with Applications to Coding, version 2](https://arxiv.org/html/1705.04560v2). Unique-product subspaces, distinct pair sums and maximal square-span constructions are prior concepts. Their finite-field coding theorems are not imported into this characteristic-zero argument. The needed proof is independently given in the reviewed note; no historical novelty is established by this acceptance.

The accepted result closes only the proposed direct rational-log-span rectangle tactic. It leaves the rank-five branch conditional, and leaves the standard finite strict source versus real-closed invariant-hull implication wholly unresolved. There is no construction of a genuine algebraic original target, no whole-fibre negative embedding, no effective integer-count bound and no assertion about other original modes or source cores.

## Review method

Direct hand algebra, inherited-source reading and verification of the candidate's stated primary references. No polynomial expansion program, symbolic solver, source enumeration, simulation, compiler, Lean execution was used. This receipt binds only the candidate hash above.

## Public-copy provenance

This is a derived public copy: the local source path is replaced with the adjacent published-note link, and one nonmathematical process reference is omitted. The mathematical review, verdict and candidate SHA256 are unchanged. Original review SHA256: ff35df9c7735f7698f05e2cc1ae601d98d45a85a1893c3a629c2b30adf4cce4c. See PUBLICATION-MANIFEST.json for the published-copy hash.
