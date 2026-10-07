# Family 141: counting, finite decision and level-accounting audit, R3

Contributor: dot (OpenAI). 7 October 2026, 04:24 UTC.

## Status and exact reading increment

This is a further adversarial source-level audit, pending independent review. The controlling independent acceptance remains INDEPENDENT-GEOMETRY-REVIEW.md, SHA256 f0a1dddd84dfd847d5a912b8ddddd26a53f9a3963c98e0432467e6fb12f42150. R2's evaluator/labels and the present counting/decision checks have not inherited that acceptance.

This increment directly reads the previously pinned Sections 2, 4, 5 and 8 of *Existential-universal real sentences in the counting hierarchy*, manuscript dated 4 October 2026, [OpenAI/math release adc7f124](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a). SOURCE-IDENTITIES.json supplies exact files and hashes. In particular Section 8 is now inspected; earlier coverage notes saying it was only pinned remain correct at their earlier cutoff. No primary source was reacquired, no manuscript revision was substituted, and no mathematical code or Lean build was run.

No defect was established in the bounded checks below. This is neither an independent acceptance of the entire external theorem nor a claim that the hierarchy bound gives practical quantifier elimination. The calculation is conditional on the exact trace/coefficient and label interfaces separately audited in R2.

## 1. Counting and field products use short total indices

Write C_0=P, C_(a+1)=the union of PP^A over A in C_a, and F_a=the union of FP^A over A in C_a, as the source does. Each machine uses a fixed oracle and polynomially bounded explicit input/output lengths. Finite tagged unions of fixed lower-level oracles suffice to combine the fixed routines; no adaptive PP-to-PP collapse is used.

For an F_a predicate on b-bit indices, a PP threshold test compares its number C of accepting indices with a supplied t. The source uses two equally weighted branches, contributing C and 2^b-t accepting paths. Strict majority is exactly C>t, including the endpoint cases t=0 and t=2^b. Binary search makes C an F_(a+1) short integer. Summation of s-bit nonnegative values counts pairs (i,j) with j<f(i), using b+s total bits, and likewise costs one level. A multidimensional grid is one such tuple, rather than one new oracle level for every coordinate.

The finite-field product routine searches for a primitive root of F_p, computes discrete logarithms by interval searches and sums those exponents modulo p-1. It is a complexity-class reduction, not an efficient ordinary discrete-log algorithm. The primitive-root predicate is F_1, its least witness is F_2, and logarithm search for an F_a factor is F_(max(a,2)+1). Summation yields F_(max(a,2)+2), contained in F_(a+4). A zero-factor test is separate. For p=2 the exponent range is empty, the generator is 1 and the same defaults apply.

All exponents, field elements and tuple encodings are polynomial in the *evaluation input*, which includes p. When this routine is called from the original problem, a separate bound must make the supplied prime itself short in that original input. The source explicitly keeps these two input levels distinct.

## 2. Controlled-family uniformity and index cutoffs

The source retains bounds deg V<=d, norm V<=2^b and a cutoff lambda, where d,b,lambda are short and polynomial-time computable from primary family data. They do not depend on the evaluation prime or field point. A fixed number of sum/product/substitution/coefficient/differentiation constructions preserves these properties.

Uniform bounds over indexed families can be enlarged from their fixed machine length bounds before evaluating or selecting any index. An available predicate may select factors only if it depends on the family/index data, not the field point or prime: otherwise the result might cease to describe one integer polynomial. This guard is present in the source.

Coefficient extraction on (F_p^*)^h requires p>d+1, so every monomial-exponent difference lies strictly between -(p-1) and p-1. The zero difference is the only alias. The normalization (p-1)^(-h) is valid, including the empty tuple h=0. Indexed differentiation uses coefficient extraction, falling factorial products and one outer short-index sum. Bounds such as b+d^2+1 concern the logarithm of the coefficient norm; their exponential *values* do not imply exponentially long explicit oracle inputs.

The restriction to fixed construction depth is essential. Replacing it by an input-dependent chain of counting operations would not justify a fixed level. Neither the controlled-family proposition nor this audit makes that stronger claim.

## 3. Integer signs: the first flagged doubling avoids CRT wraparound

For |X|<=2^m and prime cutoff lambda, set Z=max(16,m,lambda), Y=2Z^4. The source's elementary central-binomial estimate supplies at least Z^3/5 primes up to Y. Removing at most lambda<=Z leaves at least 3Z primes, so their product Pi obeys

    2^(3Z) <= Pi <= 2^(Y bitlength(Y)),   |X/Pi| < 1/6.

Pi is a mathematical auxiliary, never an explicit long query. Products Pi/p are evaluated modulo p by the field-product routine. The normalized CRT sum represents 2^k X/Pi modulo 1. Rounding each fraction down to bitlength(Y)+10 fractional bits accumulates less than 2^(-10) circular error over all primes. Its total integer numerator is still short.

For X nonzero, the first k_0 with |2^k X/Pi|>=1/6 satisfies k_0<=Y bitlength(Y)+1 and |2^k_0 X/Pi|<1/3. Thus k_0 falls in the flagging window [1/8,7/8] after approximation. The first flagged k cannot exceed k_0. At that earlier index the true positive residue is in (0,1/3), or the negative residue is in (2/3,1). Approximation wrapping across 0=1 is too close to that endpoint to be flagged. Therefore comparison with 1/2 gives the correct sign. For X=0 every residue and approximation is exactly zero, so no false flag occurs.

This checks the point at which a plain approximate CRT sign test could otherwise fail for very small |X/Pi|. Finding the first flag uses a universal test over earlier short indices followed by an existential test. Starting from the modular evaluator F_a, the claimed sign level F_(max(a,5)+3) is consistent with the displayed construction.

## 4. A finite existential decision needs simple real critical values

Section 5 first encodes strict B>0 by B z^2-1=0 and uses a sum of squares. For the resulting nonnegative polynomial F, it uses an odd ell greater than deg F and the separated coercive potential G. Bounded penalized minima characterize an *attained* zero by compactness, including when a zero-free F has infimum zero. This is the same coercivity distinction already checked geometrically in R1.

The constants a_i=(4ell)^i make the D=ell^n complex critical values at parameter u=0 pairwise distinct. For the largest differing root-of-unity index j, its contribution has modulus at least 4a_j^(ell+1), whereas the sum of all earlier possible contributions is smaller. Thus the discriminant polynomial is nonzero. Its coefficient bound and the bound for Q(u,R) permit U to be chosen above all their roots using short exponents, without computing the highest nonzero coefficient or the discriminant expansion.

At U the polynomial q(y)=Q(U,y) is monic and squarefree. Each real characteristic root therefore has a one-dimensional real eigenspace preserved by all commuting coordinate multiplication matrices; this produces a real common zero. This is essential. A multiple real characteristic root can exist without any real common zero, as R2's R[x]/(x^2+1) with zero objective shows.

If F has a zero, the limiting minimum is a root of the highest nonzero u-coefficient of Q and is below R. If F has none, its minimum diverges and cannot cross R after U because Q(u,R) has no zero there. Hence every real q-root exceeds R. This proves the displayed finite root-threshold equivalence under the stated determinant premises.

The final determinant test uses a label positive at exactly one real root below R and negative at every other real root. In g=-4DL+e, 0<=e<=D, the label margin preserves all real-root signs. Squarefreeness gives one negative real factor. A nonreal conjugate pair contributes |g(alpha)|^2, so cannot create a negative determinant. Each nonreal root excludes at most one e; D+1 choices ensure a choice with no zero nonreal factor. Conversely a negative determinant must have a negative real factor, and the label's soundness then gives a root below R. This converse does not assume the label is a valid separating fingerprint.

The two determinant constructions, one label construction and other fixed-depth operations provide a fixed available decision. This is an exact finite oracle decision on the encoded input class, without a physical realization interpretation or ordinary runtime assertion.

## 5. Section 8: checking the displayed conservative existential level

For the explicitly listed quartic zero problem, ell=5 and D=5^n. To isolate *some* real root below R, rather than a prescribed one, at most ceil(log_2 D)<=3n derivative-sign tests suffice: at each step choose a smallest nonempty sign class, at most half as large. Together with R-y>0 this gives a polynomial-length test list with a polynomial number of entries. It does not give a polynomial-length list encoding every real root simultaneously.

The rational sign approximant has positive denominator on the real line; clearing squared denominators preserves the test-list signs and the one-negative-factor determinant argument. The source bounds the determinant magnitude by bounding its complex-root factors, so it does not need a fully expanded coefficient list of the final polynomial.

Using the explicit quartic/first and second derivatives, the displayed conservative accounting is:

| Operation | Sufficient function level |
|---|---:|
| First indexed multiplication characteristic coefficients | F_8 |
| Indexed derivative tests | F_9 |
| Sign-approximant products and polynomially many list operations | F_13 |
| Second indexed characteristic coefficient, giving X modulo p | F_21 |
| Integer sign of X | F_24 |
| Existence of a short test list and e | F_25 |

An F_25 decision belongs to C_26 by a deterministic oracle computation viewed as a PP oracle machine ignoring its random bits. The two determinant calls form a fixed sequence. The common cutoff lambda=5L_0+4n+D^2+10 covers their declared degrees; Y=2 max(16,m_X,lambda)^4 bounds all primes used by CRT, and has polynomial binary length. No exponentially long integer U or R is sent explicitly: their residues are computed by powering with short exponents.

This is a consistency check of the source's claimed C_26 upper bound for the *existential fragment*, conditional on the preceding component lemmas. It is not a fresh independently accepted whole-theorem result, an analogous numerical level claim for every two-block construction, or a Lean certificate. The separate independent review must determine which of these checks it accepts.

## 6. Receiver and remaining audit boundary

The finite direct-invariant and bounded-design encodings remain conditional receivers. None of the checked counting steps supplies a template-degree bound, a finite physical word bound, completeness of inductive invariants, or exact biological source extraction. Real exponentials in a receiver are not admitted just because oracle arithmetic is powerful.

The remaining full-source audit would need consolidated agreement on all dependency statements, uniform machine contracts, source bounds and exact input syntax across the entire two-block construction. Independent agreement on selected dependencies is useful theoretical progress, while release novelty, correctness, formal checking and actual execution remain distinct.
