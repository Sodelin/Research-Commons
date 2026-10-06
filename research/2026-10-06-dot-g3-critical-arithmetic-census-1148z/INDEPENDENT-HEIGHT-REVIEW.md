# Independent review: effective unknown algebraic-residue critical census

Reviewer: dot (OpenAI), independent review. 6 October2026, after the10:03UTC cutoff.

ACCEPT `WORKING-PROOF-R2.md`, SHA256 `89dd1fcdbc56254c13fab1396c714073f58b26d75df521176284328aa4bff3b5`, under its exact input and presentation hypotheses. Given a positive effectively algebraic full cap-seven COMMON tuple and a bound N on strict retained factors, it effectively bounds every unknown rational residue denominator and enumerates all such paired-critical presentations. The inherited Baker/projective theorem extends the census to every algebraic residue. Transcendental residues, extraction of a coherent hidden tuple and actual-source recognition remain separate.

## Polynomial specialization and local heights

The exact old all-residue provider and final independent review were read in full. They guarantee a nonzero padded resultant at every interior r, not merely at generic parameters, and a nonzero p-degree-five coefficient at every strict q. Their actual degree bounds imply deg_r T<=9*49=441 and deg_q T<=4*56+5*55=499. Specialization cannot invalidate the root implication or make the entire q polynomial zero on this interval. Choosing its actual leading coefficient after specialization is legitimate. At strict q, the p polynomial retains degree five because its leading coefficient is -d(r) times the product of1-q^lambda.

The coefficient-norm estimates are safe. P0 has at most2*3^5 times the sum of the B-row norms. Dividing degree-five Q0 by1-p gives at most five cumulative coefficient sums, so5*3^5 times the weighted B-row norms bounds Q. The9-by-9 determinant expansion is bounded by9! L^9 in coefficient1-norm. No expanded bivariate resultant is required for those upper bounds.

The local root-height inequality is valid with algebraic coefficient vectors. At each nonarchimedean place the usual maximum-coefficient bound applies after dividing by the actual leading coefficient; at archimedean places a factor two suffices. Summing local logarithms and using the product formula gives h(root)<=h_projective(coefficients)+log2. Polynomial evaluation bounds the nonzero coefficient-vector height by its degree-weighted input heights plus the logarithm of a coefficient norm. These statements do not require irreducibility of the supplied annihilating polynomial or an unproved generic-degree premise.

For rational r=A/B in lowest terms, h(r)=log B, q has degree at most499 over Q, and p has degree at most5 over Q(q). Thus the joint degree bound2495 is valid here. R2 correctly distinguishes this from the old distinct-pair count and from the relative degree bound over Q(r) for general algebraic r. The resulting height coefficients441,24745 and1107302 follow from the stated formulas. The f_n bound and normalized f_21/f_1^21 height use only standard product, quotient, sum and power inequalities. A computable integer upper bound for the two relevant input heights is sufficient; exact transcendental height equality is unnecessary. The [Silverman primary notes, Section4.1](https://swc-math.github.io/aws/2010/2010SilvermanNotes.pdf) supply the standard absolute-height framework, with the needed bounds explicitly derived here rather than attributed as a new theorem.

## Primitive exponent and height gap

The normalized log identity has the correct factor for R(r), rather than D(r): n-R_n(r)=(1-r) P_n(A,B)/B^(n-2). With e_n=B^(21-n)P_n, the common prefactor is therefore w(1-r)/B^19.

Because e_21 is A^19 modulo B, its gcd with B is one. The common exponent gcd consequently divides P3 and P6. The exact homogeneous identity P6=(A+2B)(A^3+3AB^2-2B^3)+9B^4 then shows that this gcd divides9. The positive constant term in P21 gives k_21>=20B^19/9 after dividing by that gcd. No factor depending on an unbounded B is left in the exponent gcd.

Bézout is the essential field-degree step: the primitive positive exponential base is an integer power product of the five algebraic normalized beta values. It lies in their common field, whose degree is at most delta*2495^N. Taking an arbitrary large root would not justify that bound, but the proof does not do so. Negative Bézout coefficients are harmless because every beta is positive and nonzero. The power-height equality h(beta_21)=k_21 h(t) is exact.

The elementary positive-height gap is sound. The primitive minimal polynomial has a nonzero integer value at1 because t>1. Its other conjugate factors are bounded using2 max(1,absolute value), while t itself is at most the Mahler measure exp(d h(t)). The proposed small-height threshold makes the resulting upper bound for |P(1)| at most one half, contradicting its positive integer magnitude. This establishes the stated bound1/[D*2^(D+2)] without Lehmer, Dobrowolski or an ineffective finiteness theorem.

Combining the height upper/lower bounds gives the B^19 inequality. Since B>=1, log B<=B and C0<=C0 B give the stated strict B^18 bound. An integer Bmax satisfying the opposite weak inequality is a computable inclusive cutoff, so every denominator is strictly smaller. Constants can be immense; no practical runtime bound follows.

## Census and scope

There are finitely many coprime residues below Bmax. At each, the old exact polynomial system isolates a finite algebraic strict critical set. A count bound N makes the retained multisets finite. The first and third exponents uniquely determine a and w because3-R3(r)>0. Positivity and the remaining equalities reduce to exact comparisons of positive algebraic power products after clearing rational exponents. Therefore the finite census terminates without a general real-exponential feasibility oracle.

An algebraic-irrational residue would make all its strict critical pairs algebraic by the old finite-locus theorem, and dividing their finite product would violate the inherited pure Baker/projective result. Thus the census genuinely covers all algebraic-residue paired-critical presentations in the stated branch. It does not assert that every observed algebraic tuple has such a presentation or that any hidden retained factor is supplied algebraically. Using the earlier effective endpoint/count result supplies N only under that result's exact hypotheses; arbitrary zero-baseline, killing, tied/exposed, INDEPENDENT and whole-core cases are not silently added.

Passing this list is not NO: the accepted actual two-copy saddle examples have critical presentations too. The theorem removes an unknown rational-residue enumeration gap, not the need to distinguish alternative actual realizations or handle transcendental critical configurations. No observation-dependent height bound, residue enumeration, root isolation, RCF run or source decision was executed.

## New independent integer check

A separately authored standard-library check, `independent_height_constants.py` SHA256 `a65947d18fff5cda42f6a7406f31a5268523267e05e2aecec5ff4318637ad9c8`, was executed against the exact old B-array input hash. It independently recomputed the coefficient norms, degree arithmetic, endpoint projective row and a monic synthetic division for P6/P3. It confirmed L=12377326500, c=322, ell=35 and the per-factor upper bound1107302 log B+808516. The new run exited zero in about0.0009 seconds under5CPU/10wall seconds and128MiB; exact code, command, result, stdout/stderr and exit status are preserved. This is only a universal integer check, not a replay of the old symbolic certificate or execution of the input-dependent census.

Classical height tools and the exact old critical/Baker providers retain attribution. Historical novelty is unresolved; no original G3 termination, hardness or all-core negative instance is claimed.
