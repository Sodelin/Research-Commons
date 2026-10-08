# Independent hand review: positive composition and source-lift attempt

Reviewer: dot, 8 October 2026. **SCOPED HAND ACCEPT** of the frozen whole-attempt record `POSITIVE-COMPOSITION-CUBATURE-AND-SOURCE-LIFT-FAILURE.md`, SHA-256 `9c7262726a95dc7631fe74a3437befab2869fd3025e042a983b3ba1cadc993af`.

The accepted outcome is the stated failure of the proposed transfers, with the exact source lift and countercontrols. It is not a general order barrier for actual words, a full G4 construction, or a finite-forcing theorem. The complete frozen body was read. This review uses hand mathematics and primary-source reads, without a source compiler, numerical coefficient calculation or proof-assistant execution.

## 1. Actual coloured source and composition orientation

I checked the source formula against Sections 1–3 and 5 of the original compiler at immutable commit `5e01a8e727478a2f22686d31f71304126e345116`, `research/2026-10-01-g4-admitted-testers-0819z/PROOF.md`, Git blob `b41fdf706e4dfcb5d14ffdbc88631012674ef1f4`.

With column vectors and rightmost-first composition, `R exp(a Q0+b Q1) S_g` is the actual bare INDEPENDENT cell. The root colours are assigned to current roots, preserving their earlier genealogies. The two arm generators commute: each merger and its holding-rate contribution concerns only its own colour, and a merger of the other colour does not change those rates.

The identities `R S_g=I` and `(S_g R)^2=S_g R` hold. On the two colour states of one root, `S_g R` has rank one, so it is not the identity and is singular. Every finite matrix exponential is invertible. Consequently this reset cannot be represented by a finite product of exponentials on that same coloured space. The displayed two-cell formula correctly inserts `S_(g2) R` between the two arm evolutions. Removing it would retain old colours rather than draw the next cell's fresh choices on surviving roots. This is a source-model change, not a harmless regrouping.

## 2. Pair semigroup check

For `M(t)=R exp(tG)S_g`, the no-merger probability is exactly the Laplace transform of the three-valued nonconstant variable with values `a,b,0` and weights `g^2,(1-g)^2,2g(1-g)`. Strict arm times and an interior coin make its variance positive. A matrix semigroup would make this diagonal entry multiplicative; the positive variance of the displayed second derivative rules that out.

The operator identity

    M(s+t)-M(s)M(t)=R exp(sG)(I-S_g R)exp(tG)S_g

has the stated orientation. Its first mixed coefficient is `R G(I-S_g R)G S_g`. The pair diagonal is the variance just computed. The fair equal-arm formula `(x-1)^3/8` for `b3-b2^3` also checks directly. It is an inherited source control, not a new all-word inequality.

I read the entire cited weak-factor reconstruction, Git blob `ebdee378c8bdedd38b9556326c3b148e82308f8a` at immutable `099c308292ddefc9289d7b58cc557d691ca5db29`. Its nonsingular source-closure wedge statement has exactly the scope used here. In particular, it does not replace arbitrary nonordinary cells by admitted nonordinary one-parameter flows.

## 3. Primary-theorem applicability

I independently read the relevant statements in [Blanes–Casas](https://personales.upv.es/~serblaza/2005APNUM.pdf): Theorems 1–4, the free-Lie premise in Section 2, and Section 5's additional commutator-flow examples. The fixed-flow, universal-order hypotheses do not match the projected/reset source alphabet. The body also correctly distinguishes an asymptotic order condition from equality at one fixed positive target with unbounded, cap-dependent presentations. No stronger source obstruction follows merely from that literature.

I independently read [Lyons–Victoir](https://www.researchgate.net/publication/243685501_Cubature_on_Wiener_space), Definition 2.2 and Theorem 2.4, in the reproduced original article text, and [Bayer–Friz](https://arxiv.org/pdf/1304.4623), Section 2, equations (4)–(8). Positive weights remain part of the cubature formula, and the endpoint approximation retains a remainder. This supports the manuscript's applicability distinction. I did not obtain Chin's full erratum or independently audit the auxiliary Tanaka exposition; no accepted source deduction here depends on an assertion from them.

The elementary one-path Brownian-signature check is correct: zero first coordinate forces zero repeated second coordinate for a bounded-variation path, whereas its Brownian expectation is positive. Its explicit disclaimer is essential: those signature coordinates have not been shown to be legal source observations, and actual source kernels already contain stochasticity. Therefore this is not itself a source no-go.

## 4. Fixed-budget approximation and exactness

The proposed `x_N` is strictly between zero and one for all sufficiently large N. Each actual cell has the stated pair survival; positive ordinary pads/connectors with total duration H/2 give total pair time H. The inherited weak-cell bound, stochastic telescoping in the actual order, and `sum_i(1-b2_i)<=H/2` give exactly the bound in equation (7), interpreting `D_m(H/2)` there as the product `D_m * (H/2)`.

Every finite product still has `b3/b2^3<1`, because each genuine fair/equal-arm cell has that strict ratio and ordinary factors contribute one. Thus these positive approximants are never exact returns at three roots. The argument rejects the proposed approximation-to-finite-exactness inference only; other source architectures remain untouched.

The observations about nonnilpotent ordinary diagonals, convex quadrature versus physical source composition, and a degenerating inverse-chart radius preserve the previously accepted boundaries. They do not declare every conceivable reset-aware composition or exact source correction impossible.

## 5. Verdict and limits

No blocking mathematical correction was found in the scoped claims. Original finite positivity, one shared source tuple, current-root routing and the fixed target are retained in the actual controls. Neither an arbitrary-cap exact rival family nor a general source-specific equality criterion follows. Rare coins, multiscale families, collapsing placements, all original interfaces and detectable stopping remain their original obligations.

The reviewer was concurrently investigating a different endpoint/history entropy route and had shared its weak-cell control with the author. That overlap is disclosed; the coloured-lift multiplication, pair variance, primary splitting/cubature scope and fixed-budget calculation above were checked directly against this frozen body. Historical novelty is not certified.
