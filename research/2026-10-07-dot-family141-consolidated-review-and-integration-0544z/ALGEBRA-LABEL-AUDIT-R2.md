# Family 141: algebraic evaluator and root-label checks, R2

Contributor: dot (OpenAI). 7 October 2026, 03:37 UTC.

This continues the limited geometry review of R1. It requests a separate independent hand review of the trace identity, indexed characteristic-coefficient reduction and mathematical root-label properties stated below. It does not inherit full-theorem acceptance from the geometry review. All source references use OpenAI release `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; source identities are already pinned. No mathematical program, Lean build or external checker was run.

## 1. Ring-level trace identity: no hidden simple-root assumption

Source: Section 3, Proposition trace. Let S be a commutative ring and f_i=x_i^ell−r_i, where the total x-degree of every r_i is below ell. Let A=S[x]/(f_i), with its already checked standard monomial basis indexed by 0≤a_i<ell. Write tau=(ell−1,...,ell−1).

The residue functional L is the coefficient of x_1^(−1)...x_n^(−1) in v times the formal inverse product of the f_i. The total-degree filtration makes this extraction finite. It annihilates the ideal; for degree≤n(ell−1), it is simply the coefficient of x^tau.

Construct the polynomial divided-difference matrix B(x,x') by changing variables one at a time, so f(x)−f(x')=B(x,x')(x−x'). Put W=det B. In A tensor_S A, the adjugate identity yields W(x_j−x'_j)=0 for each j. The degree in x' is at most n(ell−1). The coefficient of (x')^tau is exactly 1: the top combined-degree parts of B are the diagonal differences of x_i^ell, while every r_i difference has combined degree≤ell−2. Reaching the target total degree uses the pure last term on every diagonal and no positive x power.

Therefore L applied in the second tensor factor satisfies L_(x')(W)=1. Since every x'_j can be replaced by x_j when multiplied by W, one obtains

    L_(x')(W v(x')) = v(x) in A.

Expand W in the first standard basis as sum_a x^a w_a(x'). The displayed equality identifies the coefficient functional for x^a as v↦L(w_a v). Thus the a-th diagonal coefficient of multiplication by v is L(w_a v x^a). Summing diagonal coefficients gives

    tr(M_v) = L(v sum_a x^a w_a(x)) = L(v W(x,x)).

On the diagonal, the divided differences are the partial derivatives, so W(x,x)=det(partial_j f_i). This proves the exact trace identity. The calculation takes place over S, without division, a choice of complex zeros or squarefreeness. Free-basis and coefficient identities are preserved by every coefficient-ring specialization.

**Adversarial controls.** For the nonreduced algebra S[x]/(x^2), L(v) is the coefficient of x and the Jacobian is 2x. The trace of multiplication by 1 is 2 and the trace of multiplication by x is 0, as the formula gives. In characteristic 2, both the dimension trace and Jacobian trace vanish; this is consistent rather than a counterexample. A proof that summed only distinct geometric roots without multiplicities would fail here, but the source does not do that.

The converse from a real characteristic root to a real common zero still needs the separate simple-root premise. The algebra R[x]/(x^2+1) with objective v=0 has characteristic polynomial T^2 and a real characteristic root, but no real common zero. Section 5's nonzero discriminant and large specialization are therefore substantive, not optional decoration.

## 2. Indexed determinant evaluation: the exact finite-field contract

Source: Section 3, Proposition char-coeff, using Section 2's finite-field coefficient, summation and product rules. This paragraph verifies the reduction under those explicitly named rules; it is not an implementation or a new proof of all underlying complexity-class closure facts.

Assume n is polynomially bounded, ell and Omega have polynomial binary length, deg_x r_i<ell and deg_x v≤Omega. Let D=ell^n and L0=D Omega+n(ell−1). Suppose v,r_i and the Jacobian J are uniformly evaluable at fixed function level F_a over primes satisfying

    p > n(ell−1)+ell L0+D^2+10,

plus the declared input-family cutoffs. These bounds are functions of the primary family input, not the prime or chosen field point.

For 1≤k≤D, the trace identity and the Laurent expansion give

    tr(M_v^k) = sum_(j≥0, |j|≤L0)
      [x^(tau+ell j)] (v^k J product_i r_i^(j_i)) mod p.

The retained numerator degree is at most ell L0; the requested coefficient degree is at most n(ell−1)+ell L0. Both are below p−1. Fourier averaging over the nonzero field grid therefore extracts exactly that coefficient, without exponent aliasing modulo p−1. The tuple (j,z) has n log(L0+1)+n log p bits, polynomial in the full evaluation input. It is not an exponential-length list or an input-dependent stack of counting calls. The modular numerator uses polynomially many addressed evaluations and modular powering with short exponents. The grid sum and index sum yield F_(a+2), with further safe room in the claimed bound.

Let t_k be those traces and define

    E(z)=sum_(j=0)^D (1/j!) [−sum_(k=1)^D (t_k/k) z^k]^j.

The classical logarithmic determinant identity implies agreement with det(I−zM_v) through degree D. Since p>D, every retained factorial/linear denominator is invertible. E has degree at most D^2<p−1, so another field-average coefficient extraction does not alias higher terms. The source's accounting gives the indexed coefficient in F_(max(a+3,4)+2), safely contained in F_(a+8). The zero-th factorial and empty products cause no exceptional case; primality/domain checks can use fixed defaults outside the asserted range.

To apply this to controlled polynomials with parameters, the matrix-entry degree/norm bounds are proved over Z[t] before any specialization. At evaluation time, parameter values are merely field residues. Integer lifts are used to justify the algebraic identity, not to choose a larger prime cutoff based on those lifts. This separation avoids the possible circular mistake “choose p larger than a coefficient bound that itself grows with p.”

**Scope.** This verifies how an indexed characteristic coefficient reduces to the stated available finite-field subroutines. It does not mean an expanded D-by-D matrix is small, nor that an ordinary bit-time implementation is polynomial without the fixed oracle access.

## 3. Nonzero values at roots: multiple and nonmonic inputs

Source: Section 4, Lemma root-value-bounds. Let P be a nonzero integer polynomial of degree m≤d, norm≤2^b and leading coefficient a. For an integer test polynomial g of degree≤d and the stated norm bound, define

    Ptilde(t)=a^(m−1) P(t/a),
    gtilde(t)=a^d g(t/a).

Ptilde is monic and integer, even when a is negative; gtilde is integer because every exponent of a is nonnegative. The companion multiplication algebra Z[t]/(Ptilde) is free of rank m. Its gtilde eigenvalues are a^d g(alpha), including multiplicities. After zero eigenvalues are removed, their product is a nonzero integer coefficient of the characteristic polynomial, so its absolute value is at least one. Combining this with the uniform upper bound on all other nonzero eigenvalues gives the source's lower bound on any specified nonzero g(alpha).

This avoids the false inference that the complete resultant must be nonzero whenever g is nonzero at one selected root. For example g can vanish at another root or P can have repeated roots. The source explicitly factors out zero eigenvalues, so neither case destroys the argument.

Higher derivative tests have the required norm bound because each falling factorial is at most d^d≤2^(d^2). Derivatives of order above the actual degree vanish exactly and cause no problem.

## 4. Compressed labels: existence versus soundness

Source: Section 4, Proposition root-labels. Derivative signs distinguish distinct real roots. A direct proof descends from the highest nonzero constant derivative: agreement of endpoint signs and strict monotonicity force each lower derivative to have one fixed nonzero sign, eventually contradicting two roots of P. Repeated roots are included. For example P=(t^2−1)^2 has signatures (0,+,−,+) and (0,+,+,+) at its two roots; the zero first derivative is harmless.

For at most d real roots, choose a prime mu>d^3 in the source's polynomial-in-d interval. For each pair of distinct derivative-sign strings, their difference polynomial over F_mu is nonzero, has degree≤d and hence at most d roots. Fewer than d^3 values of gamma are excluded by all pairs. A remaining gamma gives pairwise distinct modular fingerprints; taking weights w_j=gamma^j mod mu makes the actual integer weighted sums distinct as well. A desired root's target sum S* therefore exists with polynomial binary length. This is an existence-of-label argument, not an assertion of a cheap root-finding algorithm.

For soundness, primality and collision-freeness are unnecessary. For every allowed label, including composite mu, the weights are bounded integers. The rational sign approximation A(z), built from even powers of the dyadic product C, has a strictly positive denominator≥1 on all real z. Its error on each nonzero root test value is at most 1/(16M); A(0)=0 handles zero tests. The total weighted error is below 1/16.

After multiplying by a product E of these positive denominators, the label polynomial is

    L = E^2 − 4(sum_j w_j T_j − S* E)^2 − 4(T0−E)^2,

where T_j/E=A(b_j). If the integer fingerprint matches and the separate test b0 is positive, both normalized discrepancies are at most 1/16, giving L≥1/2. Otherwise either the fingerprint is an unequal integer or b0 is nonpositive; one discrepancy is at least 15/16, giving L≤−1/2. E≥1 preserves these margins after clearing denominators. No division by a possibly zero real or finite-field expression is used in the defining polynomial.

Thus every label has the claimed margin and positivity soundness. At least one label isolates each prescribed real root with b0>0. P=0 is excluded only from these selection guarantees; the polynomial family remains defined. In the final two-block algorithm, soundness instead follows from the two exact existential tests, so a degenerate coefficient polynomial or non-isolating guessed label does not create false acceptance.

**Uniformity boundary.** Forming all derivative tests, dyadic factors and denominator products needs exponentially many terms in general. Their indices and all bound parameters are short, and the operations are nested only a fixed number of times. This is compatible with the controlled-family model; it is not an expanded small-coefficient representation or practical output certificate.

## 5. Requested independent acceptance and what remains

This note finds no counterexample to the exact ring trace identity, the stated finite-field determinant reduction or the mathematical root-label guarantees. It provides explicit controls where simplified alternative arguments would fail. Acceptance should name these subclaims and their prerequisites rather than turn “no defect found” into acceptance of the entire paper.

The remaining full-theorem boundary includes a consolidated independent review of the Section 2 uniform machine/oracle rules and CRT sign routine, the full Section 5 finite decision equivalence and the final compositional level accounting. Section 8's numeric level 26 remains outside this note. There is no independent code execution or formal replay. Original G3/G4 source realization, variable exponentials and unbounded certificate search are unaffected by accepting these finite polynomial lemmas.
