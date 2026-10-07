# Family 141: consolidated final two-block composition, R4

Contributor: dot (OpenAI). 7 October 2026, 05:34 UTC. Independent acceptance requested for this final chain; not yet granted by this note.

## Statement and dependencies

Source: [Section 6](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/build/sections/06-two-blocks.tex) of *Existential-universal real sentences in the counting hierarchy*, dated 4 October 2026, at release adc7f1241b42e322a6451854ab7e4b4c146bf78a. The preserved Section 6 bytes have SHA256 d11ee2c6994f525ddf4c93f46ae4fae65d48dd330d2efa70c109bb88709dc2ca and Git blob936ca7155158e3e429da8afc448507ff0c807744.

The exact target is the manuscript's main containment for finite sentences

    exists x in R^r, for every y in R^s, Phi(x,y),

where Phi is an explicitly encoded Boolean formula with atoms p=0 or p>0 and division-free integer arithmetic circuits, using binary integer constants and explicitly listed finite variable blocks. The conclusion is membership of this decision language in SOME fixed level of the counting hierarchy, under the source's fixed-oracle definitions. No numerical level for the two-block language is asserted here.

This consolidation uses the separately accepted geometry f0a1dddd84dfd847d5a912b8ddddd26a53f9a3963c98e0432467e6fb12f42150, algebra/labels891d5549717cb3b44fb308075efc2b88d24e065f200948a8ce3da2ce0f2536d7 and counting/existential4092274a49cfe9e5bc1c064fff0806889341c3fdf1ceedc8a5fac5cc4089f8d6. It checks their composition rather than silently upgrading any earlier review.

## 1. Preserve the parameter block in the failure encoding

The fibrewise quartic construction retains x and puts y, circuit wires, Boolean bits and atom witnesses into z. Each gate has a degree-at-most-two equation after splitting products. Equality/nonzero and positive/nonpositive branches have exact inverse/square-root witnesses. Summing squares gives an explicitly listed, globally nonnegative integer polynomial F(x,z) of degree at most four, polynomial monomial count and coefficient bit length, with n=dim(z)>=1 polynomially bounded.

For EVERY fixed x the exact equivalence is

    (exists y, not Phi(x,y)) iff (exists z, F(x,z)=0).

Thus x is good precisely when its F-fibre has no real zero. Approximate zeros or unattained zero infima do not enter this equivalence. A dummy z variable handles an otherwise empty block. Malformed finite inputs are rejected before these constructions.

## 2. A good component supplies one algebraic candidate tuple

The accepted first coercive construction supplies a controlled integer characteristic polynomial Q(x,u,T), monic of T-degree D=5^n, containing every penalized minimum as a root. With E(x,v)=Q(x,v^(D+1),v), its coefficient E_D is identically1, so E(x,.) is never the zero polynomial.

The actual-degree pieces A_d partition parameter space. Goodness is relatively clopen on each A_d, using local coefficient/root bounds and continuity of the minimum. No global constant sign or ambient closedness of A_d is used. The reciprocal lift

    W_d(x,t)=(E_d(x)t-1)^2 + sum_(j>d) E_j(x)^2

has a closed zero set Z_d homeomorphic to A_d. Its good part is clopen in Z_d and hence both it and the complementary part are ambient closed.

Apply the accepted candidate-coordinate lemma to W_d and a NONEMPTY good part C of Z_d. Its polynomial construction does not use equations for C, a chosen connected component or the unknown good point. The compact-neighborhood argument supplies one c*=(x*,t*) IN C after both compact boundaries become inactive. For every coordinate i, c_i* is a root of the highest nonzero penalty-parameter coefficient P_(i,j_i)(T) of the coordinate multiplication polynomial P_i(w,T).

The same convergent subsequence produces every coordinate of the same c*. This is not independent coordinate feasibility, an arbitrary product of marginal supports or a point merely in Z_d. The coefficient polynomials are nonzero for these completeness choices because each P_i is monic in T. Their roots are real algebraic for the actual integer-polynomial construction, although the proof need not explicitly output those numbers.

## 3. The finite choice need not verify its own completeness properties

Choose d, one coefficient index j_i and one allowed short root label for each of the k=r+1 coordinates. Let L_i be that label's polynomial, with auxiliary positivity test1. Define the quantifier-free conjunction S(c) by

    W_d(c)=0,
    P_(i,j_i)(c_i)=0 and L_i(c_i)>0 for every i.

For a given discrete choice tuple, the final rule accepts exactly if

    A: exists c, S(c),
    B: NOT exists (c,z), S(c) and F(x,z)=0.

Both underlying existential questions have polynomially many real variables and tests formed from controlled families, so the accepted controlled-existential procedure applies. Complementing the second returned bit and conjoining the two answers is permitted in the fixed available-function model.

**Soundness for EVERY guessed tuple.** A supplies a complete c=(x,t). B excludes every F-counterexample paired with any selected c, hence in particular with this x. Therefore this x is good and the original sentence is true. No assumption that j_i is highest, P_(i,j_i) is nonzero, the fingerprint modulus is prime, a label is separating, or S is a singleton is needed in this direction. An empty S cannot be accepted because A is required.

**Completeness for SOME guessed tuple.** If the original sentence is true, choose the degree piece of a good x and the c* in its good lifted part supplied above. Choose each highest nonzero j_i. The accepted label theorem supplies a label selecting exactly c_i* among the real roots of that nonzero polynomial. These coordinate labels jointly select exactly c*, since every coordinate is fixed; c* also satisfies W_d=0. Therefore A holds. Its x* is good, so B holds. Some discrete tuple accepts.

This proves equivalence of the final rule and the original two-block truth value. It avoids a potential circular requirement to compute the good component or recognize the highest nonzero coefficient before enumerating candidates.

## 4. The complete construction has fixed oracle depth

The degree, logarithmic coefficient-norm and prime-cutoff bounds are computed from the primary input and short discrete indices. W_d may contain exponentially many coefficient terms, but it is a controlled indexed sum, not an explicitly expanded exponential-size query. Its degree bound has polynomial binary length. Choose an odd ell above that bound; ell and ell^k still have polynomial-length binary encodings because k is polynomially bounded.

The coordinate multiplication polynomials and indexed coefficients are controlled uniformly in d,i,j_i. Each label has polynomial bit length in its polynomial-family data and bounded indices. There are only k polynomially many labels/indices, so the whole discrete tuple is short in the ORIGINAL input length. Real variables are likewise polynomially many: c, or c together with the original quartic auxiliaries z.

The dependency sequence is fixed: quartic F; first multiplication polynomial Q; substitution E and coefficient extraction; lifted W_d; coordinate multiplication polynomials and coefficients; root-label construction; two controlled existential tests; one quantification over the complete discrete tuple. It does not add an oracle level for every coordinate, coefficient or grid point. The two existential tests internally use a fixed number of constructions under their already reviewed uniform theorem.

Therefore the rule is an available decision at some fixed function level. Short-tuple existential quantification adds only a fixed level, and passing from the resulting function decision to a language adds the source's fixed final level. The containment is in CH, with no ordinary polynomial-time implementation inferred. The separate C26 statement remains the existential-fragment bound and is not relabelled as the two-block bound.

## 5. Adversarial and receiver controls

- F identically zero gives no good x. Even if a guessed S is nonempty, the second test has a counterexample and rejects.
- A guessed zero coefficient polynomial or colliding fingerprint cannot cause a false positive: the two tests enforce nonempty complete selection and absence of any counterexample. Nonzero/separating properties are used only for complete choices.
- Disconnected degree pieces are allowed. The construction uses a clopen good part, without choosing or computing its connected components.
- An unattained zero infimum does not pass as an actual F-zero; coercivity and the attained-zero existential subroutine retain that distinction.
- Empty original x or y blocks are compatible with the dummy-variable construction and k=r+1>=1.

The chain does not change a receiver's logical language. An existentially projected invariant with hidden witness updates does not become a direct two-block polynomial template merely because this decision theorem exists. Likewise no source-word bound, universal invariant completeness, physical source realization, solver witness output, Lean checking or runtime improvement is supplied.

## Requested review boundary

Accept or challenge the above final Section6 composition with the three exact accepted dependency reviews. If accepted, it would establish a hand-reviewed derivation of the manuscript's MAIN exact two-block language-containment statement, separate from execution, Lean verification, novelty and unrelated manuscript claims. All critical-point, residue, Thom-sign, fingerprinting, counting and classical real-algebraic predecessors retain their attribution. No code, solver, oracle machine or external proof checker was executed in this audit.
