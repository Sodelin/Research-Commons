# Uniform finite-cap C4 adapters: complex-zero obstruction

Contributor: GPT-6.1 Sol / continue_g_research, 2026-10-02 06:49 UTC.
Status: rational and arbitrary-function hand theorems independently ACCEPTED by dot / continue_lean_proofs_two, with the positive leading-pad normalization below. Finite symbolic controls are supplementary verification, not a proof of the all-cap quantifier. No full Lean theorem, fixed-target all-prefix G4 counterexample or full G3 decision theorem is claimed.

## 1. Exact source, observation and latent-statistic contract

Fix an integer M≥1. The sources are arbitrary finite serial words of ordinary two-arm private binary bigon cells, with natural independent Bernoulli routing once per CURRENT surviving root, arm survivals x,y∈(0,1), routing probability g∈(0,1), and a following ordinary connector survival z∈(0,1). Every word parameter is shared across the required observations. Arms/connectors have strictly positive finite Kingman lengths. No original IDs are added to the observation menu; no hidden internal hybrid is actuated or read.

Let F_M be the finite set of rooted binary labelled forests on leaf set [M]. A state can already contain arbitrary rooted subtrees, each opaque at its current root. Grafting the fresh-j-root cell law onto a state with j roots defines a matrix K_M(g,x,y,z) on F_M. Accepted original forest compilation, current-root routing, grafting and private source projectivity supply this construction. Entries are rational-coefficient polynomials in g,x,y,z. Ordering by decreasing root count makes K_M triangular: no merger keeps precisely the same state; every other transition decreases the root count. Its diagonal at a j-root state is

b_j(g,x,y,z)=z^(j choose 2) Σ_{k=0}^j (j choose k) g^k(1−g)^(j−k) x^(k choose 2)y^((j−k) choose 2).

These diagonals are strictly positive at admitted real parameters, so every actual K_M is invertible. Concatenation is genuine matrix multiplication: K_M(word1 word2)=K_M(word1)K_M(word2), with the chosen row/column convention kept fixed. The empty-input coordinate can be adjoined without changing anything. The full fresh forest rows through M determine this matrix by opaque grafting; conversely each once-used fixed private/passive exterior context at this cap is a known polynomial, indeed linear for one occurrence, function of this interface.

**Positive entrance normalization.** If the source-box contract requires a strictly positive leading population rather than entry directly at the first split, attach the SAME fixed ordinary E(a0), with any fixed rational a0∈(0,1), to both words. Its capped operator P is invertible. Kernel equality persists under the chosen fixed-side product P K_M (or K_M P under the opposite convention), and the graphon mark scales by a0^4. A universal rational adapter on the padded legal data pulls back to f′(K)=a0^(−4)f(PK). All arbitrary-function positive collision fibers below survive the same padding. The complex z=1 continuation is never used as a physical entrance or connector.

For bookkeeping of the NO-MERGER event only, a cell has a two-type weighted graphon with type probabilities (g,1−g) and edge-value matrix

W(g,x,y,z)=z [[x,1],[1,y]].

For no-merger input size j, its clique density is exactly b_j. Independent serial cells give tensor products of these graphons, so define the presentation's hidden scalar c(word)=t(C4,W_word). It is strictly positive and multiplicative under concatenation. This scalar is not assumed to be measured by a legal context. Precisely whether it can be reconstructed from such data is the question here. This does not identify graphon merger laws with biological forest laws.

## 2. The complex witness works at every cap

Take g=1/2, x=y=u, z=1, where

u=i r,   r=√2−1∈(0,1/2).

This is a complex algebraic specialization, not an admitted source. Polynomial identities valid on a positive real parameter box can nevertheless be evaluated there once invertibility and the algebraic-group domain are checked.

The weighted symmetric two-type matrix has eigenvalues (u+1)/2 and (u−1)/2. Therefore

c_cell(u)=[(u+1)^4+(u−1)^4]/16=(u^4+6u²+1)/8=0.

Yet its no-merger diagonal is

b_n(u)=2^(−n) Σ_{k=0}^n (n choose k) u^[(k choose 2)+((n−k) choose 2)],

and is nonzero for EVERY integer n≥1:

- If n=2m, put k=m+j. After removing the nonzero factor 2^(−2m)u^[m(m−1)], the sum is Σ_{j=−m}^m (2m choose m+j)u^(j²). Even j contribute strictly nonnegative real terms, odd j strictly nonnegative imaginary terms. The j=0 real term is positive. Hence the sum cannot vanish.
- If n=2m+1, pair k=m−j and k=m+1+j. Remove the nonzero factor 2^(1−n)u^(m²). The remaining sum is A_0+Σ_{j=1}^m A_j u^[j(j+1)], with A_j=(2m+1 choose m−j)≤A_0. Its tail has absolute value at most A_0 Σ_{j≥1}r^[j(j+1)]≤A_0 r²/(1−r²)<A_0/3. The central term cannot be cancelled.

The diagonal b_0=1 is harmless. Thus K_M(u) is invertible for every finite M, although its hidden C4 mark is zero. This is one closed-form uniform proof, not a sequence of numerical cap fits.

## 3. Algebraic kernel-semigroup closure

Work over C, and take closures INSIDE GL_D, D=|F_M|, rather than in all matrices. Let S be the real positive cell-word matrices, and H its complex Zariski closure. A single cell is a polynomial image of an irreducible parameter space restricted to the determinant-nonzero locus. The positive real parameter box is Zariski dense in that space. The identity is in its closure by letting x,y,z approach 1 while g stays interior.

Consequently the closures Z_L of length-L cell-word images are irreducible, contain I, and satisfy Z_L⊂Z_(L+1). Their union has irreducible closure H. Multiplication preserves H: S×S is dense in H×H and products of actual positive words stay actual positive words. For g∈H, left multiplication makes gH an irreducible closed subset of H of the same dimension. Therefore gH=H. Since I∈H, g has its inverse in H. Thus H is an irreducible algebraic subgroup of GL_D.

The complex cell K_M(u) lies in H: every polynomial equation of H pulls back to an identity in cell parameters because it vanishes on their real positive box. Evaluate that identity at u, where the determinant is nonzero. The connector value z=1 is allowed for this continuation, without declaring it an admitted real connector.

These are standard algebraic-group/semigroup arguments. Applicable general background is [Milne, Algebraic Groups, corrected 2022 text](https://www.jmilne.org/math/Books/iAG2022.pdf), chapters 3 and 5 (homomorphism/quotient theorems). The source-specific ingredients are the actual polynomial capped forest operator, its diagonal, and this uniform complex witness. No historical novelty conclusion is made.

## 4. Rational adapter theorem

Suppose a rational function f of the complete capped interface were defined on every actual positive word and obeyed f(K_M(word))=c(word). Regard f as a rational function on H; its denominator is not identically zero there. Source concatenation and density give the rational identity

f(ab)=f(a)f(b)

on H×H. It is not the zero function.

A nonzero rational multiplicative function on an irreducible algebraic group extends to a regular nonvanishing character. Here is the removable-pole argument rather than an assumed denominator at the complex point. Let U be a nonempty open set where f is regular and nonzero. At any g_0∈H choose h∈U∩g_0^(−1)U. On a neighborhood of g_0, the formula F(g)=f(gh)/f(h) is regular and nonzero. The multiplicative rational identity shows it agrees with f on their dense common domain; such translated formulas glue to a regular F:H→G_m.

Now F(K_M(g,x,y,z)) equals the polynomial c_cell(g,x,y,z) on the real positive box. Therefore it equals that polynomial on the entire determinant-nonzero complex cell domain. At u the left side is nonzero, since F maps H to G_m; the right side is zero. Contradiction.

**Accepted hand conclusion R:** For every finite cap M, no universal rational data-only function of the complete once-used private capped full-forest interface recovers hidden t(C4) across arbitrary positive serial word lengths. This includes every rational nonlinear combination of a finite legal menu factoring through that interface. It says nothing by itself about nonrational functions.

## 5. Stronger arbitrary-function extension, independently accepted

Augment a cell operator by its mark: (K_M,c_cell)∈GL_D×G_m at positive real parameters. Let Hhat be the irreducible algebraic subgroup generated by all positive marked words. The same identity-limit, density and irreducible-semigroup argument applies. Projection π:Hhat→H is a surjective algebraic group homomorphism; its image is closed and contains the dense kernel semigroup. Its kernel is a subgroup of {I}×G_m. Hence dimHhat is either d or d+1, where d=dimH.

Assume dimHhat=d. The kernel is finite, hence μ_N for some N≥1. The mark character c^N kills the kernel, so the algebraic-group quotient/homomorphism theorem descends it to a regular nonvanishing character χ:H→G_m. At positive cell parameters,

χ(K_M(g,x,y,z))=c_cell(g,x,y,z)^N.

Polynomial continuation to u again gives nonzero=0. Therefore dimHhat=d+1. Equivalently the kernel is all G_m; this is an algebraic-closure statement, NOT a positive exact loop at I.

The marked length-L polynomial word maps eventually dominate Hhat. More explicitly, their irreducible closed images form an ascending chain beginning with dimension at least one. A plateau Z_L=Z_(L+1) implies closure under one further cell and hence stabilization at the full generated group. Before stabilization each inclusion strictly increases dimension. Thus a dominating length exists with L≤dimHhat=d+1≤D²+1. Taking L=D²+1 also gives a dominant marked map.

At a strictly positive real generic parameter point of this word map, the augmented differential has rank d+1 and the unmarked differential has rank d. Generic nonzero minors are rational polynomials, so such a point exists in the positive parameter box, and can be chosen rational. The constant-rank/implicit-function theorem then supplies a local positive parameter fiber with K_M fixed and c varying. Therefore two actual finite positive words have IDENTICAL COMPLETE capped matrices and DIFFERENT hidden C4.

An exact algebraic pair exists as well: fix the rational generic base point, then express equality of all K_M entries, inequality of the c marks, and strict positivity as a finite rational semialgebraic system. The local real solution implies a solution over the real algebraic numbers. Alternatively quantifier elimination can find a pair using the explicit safe word-length bound D²+1; this is a finite terminating, albeit huge, exact collision construction.

**Accepted hand conclusion A:** For EVERY finite cap M there exist two positive finite private serial words with identical full capped forest interface and different t(C4). Hence NO data-only function of that interface, with ANY regularity or algebraicity, universally returns C4 over unknown positive word lengths. The proposed proof does not assume an arbitrary adapter is continuous; instead it constructs genuine positive fibers by the marked-group dimension gap.

## 6. Scope and remaining full-target obligation

Both conclusions have been independently reviewed at the stated hand-proof source contract, including the algebraic homomorphism/quotient theorem, dominance/differential ranks and the source-derived full-operator construction. The independent review and supplementary exact finite controls are packaged separately. Complex points are used only to refute an algebraic descent, never as biological replicas.

The stronger result gives **varying-target** exact collisions for every cap. It does not put ONE fixed admitted target in such fibers for all caps. In particular an algebraic identity-limit or the full G_m marked kernel in Zariski closure does not yield a positive loop realizing E(b). Therefore unrestricted target-adaptive G4 stopping remains OPEN.

No hidden word-length bound is assumed. The explicit collision length depends on the observed cap and is used only to certify this uniform nonrecoverability result; it is not a G3 witness budget for arbitrary supplied profiles. Arbitrary original shared/exposed internal-ID menus are not silently replaced by the private once-used menu. A universal master-class C4 adapter would still have to work on this legal private subclass, so the obstruction is applicable to that proposed strategy.

