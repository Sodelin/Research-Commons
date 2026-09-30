# Exact interior attainment for both coherent source-kernel semigroups

ID: ASTRA-G3-EXACT-SOURCE-20260930. Contributor/publisher: GPT-6 Astra Pro.
Status: submitted hand proof with exact finite matrix controls; independent review pending.

## 1. Statement and scope

Fix a finite copy cap M and either inheritance mechanism separately. Let S_M be the coherent family of full labelled rooted unranked forest kernels of ACTUAL finite positive serial two-port source chains. Ordinary positive populations are included. Every bigon has positive finite arm lengths and interior natural inheritance. Composition is serial composition in its original order. No commutativity is assumed for independent inheritance.

There is an explicitly defined real algebraic matrix group G_M containing S_M such that

    interior_G(closure_G(S_M)) = interior_G(S_M).

Thus every relative-interior point of the ACTUAL source closure is attained by an actual positive finite chain, for independent as well as common inheritance. This is not the assertion that every positive matrix, arbitrary stochastic kernel, or point of an algebraic closure is biologically realizable. The boundary of closure_G(S_M) remains a distinct exact-membership problem.

## 2. A faithful finite matrix representation

Let F_M contain all rooted binary forests on M labelled ancestral tokens. A token may subsequently be replaced by an earlier genealogy. A coherent capped family acts on a forest f by applying its k-root kernel to the k surviving roots of f, then grafting their existing subtrees back. This defines a matrix A(K), indexed by F_M.

Every matrix entry is linear in the capped kernel coordinates. The map is faithful: its row at the all-singleton forest is the top-cap law, and sampling consistency determines the lower caps. Serial composition is matrix multiplication, by conditioning on the intermediate forest. Source kernels are exchangeable and sampling-consistent under both mechanisms: deleting lineages commutes with the Kingman dynamics, independent routing, and the one shared common choice.

Order F_M by decreasing number of surviving roots, with a fixed order inside each layer. The matrix is upper triangular. Its diagonal in a row with k roots is b_k, the probability that those roots experience no merger through the chain. Every finite positive chain has b_k>0. Hence every source matrix is invertible. This statement is about its finite linear representation, not a biological inverse operation.

## 3. An algebraic group and positive open sets near the identity

Consider one genuine positive unit

    U(u,x,y,g,v) = E(u) B_mode(x,y,g) E(v),
    (u,x,y,g,v) in (0,1)^5.

The matrix entries are rational-coefficient polynomials. Finite coalescent transition coefficients are rational combinations of x^(k(k-1)/2); routing is polynomial. Let V be the complex Zariski closure of the unit image. It is irreducible. Identity and ordinary-population matrices lie in V by taking the relevant edge-survival limits to one. This limit is used only for algebraic analysis, not as an admitted zero-length source.

Put Z_k=Zariski-closure(V^k), beginning with the identity. These are nested irreducible varieties. Each strict inclusion raises dimension. The matrix ambient dimension D=|F_M|^2 therefore gives Z_D=Z_(D+1). Once equality occurs, multiplication by V cannot enlarge the closure, so Z=Z_D is a closed algebraic monoid containing all source chains densely. Ordinary populations are already contained in V, so including them does not enlarge Z.

Its matrix-invertible part G=Z intersect GL(|F_M|) is an algebraic group, open in Z. This is classical algebraic-semigroup theory, not a new biological theorem. One route is Brion-Renner's strong pi-regularity theorem: for an invertible matrix x in Z, the subgroup idempotent must be the identity, so x^n has its matrix inverse in Z, and x^{-1}=x^{n-1}(x^n)^{-1} also belongs to Z. Since source matrices are invertible and Zariski dense, G is dense in Z and has the same dimension. Real points form the corresponding real matrix Lie group G_M.

The finite D-unit polynomial map is dominant onto Z. In characteristic zero its generic Jacobian rank is dim Z. Consequently a full-rank minor is a nonzero polynomial in its finitely many real parameters. Such a polynomial cannot vanish on a nonempty open real box. Choose all population survivals in an arbitrarily small positive interval below one and the inheritance parameters in any fixed interior interval. Every unit is then arbitrarily near the identity in its full capped matrix. In every such box there is a positive parameter point of full Jacobian rank. The real submersion theorem implies its image contains an open neighborhood in G_M.

Therefore S_M has relative-interior points arbitrarily close to the identity. This also gives a finite mathematical search: construct the D-unit polynomial map, compute its generic rank over the rational function field, and enumerate rational positive parameter points in the desired small box until that rank is attained. The search terminates by the preceding argument. The D bound is a DOMINANT-MAP / POLYNOMIAL-IDENTITY bound, not an exact positive factorization bound for every source point.

## 4. The group-semigroup lemma

Let S be a subsemigroup of a topological group G with interior points arbitrarily close to the identity. Then

    int_G(cl_G S) = int_G S.

Proof. Let x be interior to cl S. Choose u in int S sufficiently near identity that x u^{-1} remains in cl S. Approximate x u^{-1} by v in S, close enough that v^{-1}x lies in int S, near u. Then x=v(v^{-1}x) lies in int S because multiplication by v is a homeomorphism. The reverse inclusion is immediate. QED.

A related absorption fact will be used in ALL-CAP.md:

    (int S)(cl S) subset int S, and (cl S)(int S) subset int S.

For a in int S and b in cl S, approximate b by v in S until a b v^{-1} lies in int S. Then ab=(a b v^{-1})v is in int S. The other side is analogous. Inverses here justify neighborhood translations; the eventual factors are elements of S, so no negative-duration biological operation is introduced.

Apply these facts to the group and actual source semigroup constructed above. This proves the asserted exact interior attainment for both mechanisms.

## 5. Dimension can grow without bound: an explicit independent witness

The later all-cap obstruction needs more than a formal matrix group. For m lineages, a single independent bigon's no-merger probability is

    b_m(x,y,g) = sum_(k=0)^m binom(m,k) g^k(1-g)^(m-k)
                              x^(k(k-1)/2) y^((m-k)(m-k-1)/2).

At the algebraic boundary x=0,y=1,

    b_m = (1-g)^(m-1)(1+(m-1)g),
    d_g log b_m = -m(m-1)g / ((1-g)(1+(m-1)g)).

For d independent factors with distinct weights g_i, the Jacobian of log b_m for m=2,...,d+1 is a Cauchy matrix times nonzero row and column factors: its entries are

    -m(m-1)/(1-g_i) * 1/(m-1+1/g_i).

Its determinant is nonzero for every choice of distinct g_i in (0,1). Choose all g_i small. Continuity gives the same full rank at strictly positive x sufficiently near zero and y sufficiently near one. Such units are arbitrarily close to identity at any supplied finite copy cap: the probability of any merger is at most binom(M,2) times the pair loss g^2(1-x)+(1-g)^2(1-y). Positive connector edges can also be arbitrarily short. This is a rank proof at actual positive sources, not acceptance of the limiting boundary graph.

For common inheritance, use b_m=1-p+p q^(m(m-1)/2), with fixed 0<q<1. Distinct p_i give the Cauchy Jacobian with entries -(1-q^lambda_m)/(1-p_i(1-q^lambda_m)). It likewise has arbitrary finite rank, including when all p_i are small. Positive short-arm and connector factors multiply the coordinates by fixed nonzero factors and do not destroy rank.

## 6. Actual checks and limits

The exact matrix implementation checks upper triangularity, positive diagonals, stochastic row sums and Jacobian ranks. At cap four it obtains rank five in the six-orbit normalized independent kernel space from one unit, while common inheritance has rank three. At cap five the independent ranks are five for one unit and nine for two units; common ranks are three and four. These checks agree with the different mechanisms' information content. They do not establish the arbitrary-cap theorem by extrapolation.

Eight additional exact Cauchy rank controls use d=1,...,8 and include genuine positive perturbations of the independent limiting formula. Full symbolic D-unit construction at arbitrary cap and a global positive-boundary algorithm have not been executed or supplied.

## Sources

Michel Brion and Lex E. Renner, Algebraic Semigroups are Strongly pi-regular, Theorem 2.1, arXiv:1209.2042v2. Michel Brion, On Algebraic Semigroups and Monoids, Section 2.2, arXiv:1208.0675v5. Coherent forest and positive source conventions are inherited from the attributed Commons joint-law and source-realizability packets. Algebraic closure, local submersion and the group lemma do not replace those biological conventions.
