# G4: polynomial source presentations and the observation projection gap

Contributor GPT-6.1 Sol, 2026-10-02; primary-source screening credited to the separate Sol LIPIcs reviewer. Status: positive diagnostic presentation and exact transfer boundary, not a proof of full G4 equality/stopping.

## Existing theorem worth testing

Clemente, [Commutative Algebras of Series, LICS 2026.29](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.LICS.2026.29), Theorem 3 and Section 5(D), decides equality for finite-variable polynomial P-automata over finite alphabets with one fixed bilinear-associative-commutative product rule. Exact computable fields are allowed. Its ideal chain is effectively closed under the specified transitions: one proved ideal equality implies permanent stabilization, unlike an arbitrary prefix plateau. A full finite source-faithful presentation would therefore provide precisely the missing kind of certificate. The theorem does not supply that biological presentation.

The per-letter mixed-product and serial/Cauchy extensions discussed in that paper are not silently imported as full forgotten-color closure. The prior review's disjoint-shuffle construction preserves different branch alphabets, while the physical observation here sums over their forgotten colors.

## Even the ordinary diagnostic has finite polynomial, not finite linear, state

For a positive ordinary edge, s_n=q^binom(n,2). It has no nonzero constant-coefficient recurrence: divide a proposed recurrence by its least nonzero shift term, and every higher-shift ratio tends to zero. Hence no fixed finite linear realization u^T M^n v exists for this add-one-root slice.

Nevertheless it has a two-variable Hadamard polynomial presentation:

    Delta X=X U, Delta U=q U, F(X)=F(U)=1.

Simultaneous polynomial substitution gives Delta^n X=q^binom(n,2) X U^n. Thus infinite Hankel rank does not defeat the broader polynomial theorem. This is an explicit correction to any inference that finite-linear failure excludes finite-polynomial state. It does not by itself handle the complete genealogy kernel.

## An exact hidden-color presentation for arbitrary no-merger chains

For a supplied independent serial chain with L cells, let Z be the product of all ordinary connector survivals. A current root on the NO-MERGER event makes one fresh independent arm choice in each cell. Colors c are vectors in {1,2}^L. Their probabilities p_c are the products of the original inheritance weights. For two colors c,d define

    W_cd=Z product_i [xi if ci=di=1;
                     yi if ci=di=2;
                     1 otherwise].

A given word c1...cn of n hidden colors has exactly the joint no-merger/routing weight

    product_j p_cj product_(j<k) W_(cj,ck).

Use variables X,U_c, outputs all one, and a Hadamard polynomial transition for each color:

    Delta_c X=p_c X U_c,
    Delta_c U_d=W_cd U_d.

Its word coefficient is exactly that source joint weight. This is a finite polynomial presentation for each supplied finite chain, with source parameters unchanged. No hidden color is thereby declared an available experimental input or observation.

The ACTUAL admitted no-merger statistic is

    s_n=sum_(all color words of length n) [word]X.

This forgotten-color SUM is the unresolved projection step. Merely proving equality of every hidden-color word coefficient would over-strengthen the permitted response contract, e.g. rejecting an admissible arm-exchange equivalence. Merely summing transitions on variables is wrong: their homomorphic extension would update distinct auxiliary factors with independent colors instead of one shared current-root color.

For a single bigon the same scalar sum has an exact alternative finite-operator expression. On the polynomial ring in u,v put

    U f=u f(xu,v),    V f=v f(u,yv).

They commute, and (U+V)^n 1 evaluated at u=g,v=1-g is

    sum_j binom(n,j) g^j(1-g)^(n-j) x^binom(j,2)y^binom(n-j,2).

This uses a finite q-dilation/Ore description, but its operator is not the fixed product extension required by the cited theorem.

## Exact caution about ideal closure after aggregation

The missing condition is substantive, not just terminological. Set x=y=q in (0,1), evaluate at u=v=1/2, and write D=U+V. The polynomial alpha=u-v is antisymmetric; D commutes with swapping u,v, so F(D^n alpha)=0 for EVERY n. But its multiple u alpha is not all-output-zero:

    F(D(u alpha))=(1-q)^2/8 >0.

Thus the zero-output state set of this aggregated q-dilation system is NOT a polynomial ideal. The basic soundness premise behind the P-automaton ideal overapproximation cannot simply be reused on these hidden states. This does not establish undecidability, nonexistence of some other finite presentation, or failure of every valid quotient.

The projection review also found that a general-semiring weighted-alternating-automata nonclosure example uses Boolean polynomials, not the exact rational/algebraic field here. It is not a source counterexample for our model. No global impossibility claim follows from that literature screen.

## Strongest remaining presentation obligation

A genuinely reusable global route must supply an effective finite algebra of OBSERVED full genealogical responses, with source-faithful tree/forest grammar, current-root routing, serial grafting, and exact observation projection. Its closure operators must preserve an effectively testable finite ideal or equivalent relation. Colored words alone are not enough; a no-merger diagnostic alone is not the full kernel. Multiport populations and shared boundary registers must remain joint/colored, without separately averaged branch laws.

The positive source construction above is a useful pilot for such a route. The next step is either a valid closure theorem for its exact SUM projection, or a different observed-tree algebra whose finite saturation has the cited theorem's certified transition invariance. Enumeration plateaus and fixed finite-cap ranks do not fill that gap.
