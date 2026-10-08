# Attempt 4: exact complete-value-space interface for source-supported residues

Contributor: Codex G5 lane, 8 October 2026. **Hand theorem candidate; independent root review requested.** The preceding frozen attempts remain unchanged. This directly tests a remaining interface in the full boundary-classification architecture: COMPLETE source value-space inclusion, rather than a local derivative match. No divisor calculation, algebraic catalogue, QE, source engine or compiler was executed.

The original endpoint is still a terminating recognizer for every finite rational/effectively algebraic original joint observation input, with one admitted finite graph, original-ID map and shared tuple, both inheritance modes and the declared controls/readout. The present component supplies neither those missing data nor a full recognizer. It makes one sufficient actual COMMON residue-attainment premise exact and decidable when the relevant source data are supplied.

## 1. Source and nearest accepted interface

Keep f_i(p,q)=1-p+p*q^lambda_i, H_i=-log f_i, 0<p,q<1, at one original COMMON cap. One factor is an actual natural once-drawn COMMON cell; the capped forest uses the same pair across all coordinates. Positive ordinary connectors and the baseline remain physical, and factor multiplicities remain integers.

The accepted [ARC-SUPPORTED-RESIDUE-ATTAINMENT.md](../../2026-10-01-sol61-g3-boundary-resume-2124z/ARC-SUPPORTED-RESIDUE-ATTAINMENT.md) and its [independent review](../../2026-10-01-sol61-head-audit-1956z/G3-ARC-RESIDUE-REVIEW.md) give an exact finite-source sufficient theorem. Retained pivots must have their WHOLE image in an affine translate of the permitted value space V and be a submersion onto V. Every omitted tail and EVERY value on each residue-approximating arc must lie in V. Positive baseline and zero killing then give finite strict attainment by actual integer-copy approximation plus exact retained-pivot correction. A derivative span at one point alone does not supply these premises.

The reviewer lane's frozen [neutral-curve catalogue candidate](../g3-impossibility/algebraic-normal-unit-level/NEUTRAL-CRITICAL-CURVE-CATALOGUE-CANDIDATE.md), SHA256 8febc9065158935199ccced0b98f57ebedd16de7a9e7f9c921e2efec9c2c96c1, describes cap-bounded divisors of the restricted f_i and a finite carrier catalogue even for real normals. At writing its catalogue theorem is awaiting root review. The first theorem below is a separately bound consequence of the same divisor identities for ONE SUPPLIED algebraic carrier, not a silent extension of that frozen body.

## 2. Full log-value space equals a rational divisor row space

Supply an irreducible algebraic plane curve C with a nonconstant strict real analytic arc I, whose closure includes a neutral point where p(1-q)=0. None of the f_i is identically zero on C, since they are strictly positive on I. Let A be the integer matrix of orders of all f_i at their zeros/poles on the smooth projective normalization of C. Include every normalized branch, including infinity. The matrix has finitely many rows.

Define the COMPLETE real arc-value space

    V_I=span_R{H(p,q):(p,q) in I}.

**Theorem 1.** V_I equals rowspace_R(A). In particular it is rational, independent of shrinking to a nonempty neutral analytic subarc, and effectively computable from a supplied algebraic carrier by finite normalization/divisor computations. This claims no evaluated matrix or algorithmic complexity bound.

**Proof.** If e is an integer vector in ker_Q(A), the meromorphic monomial product_i f_i^e_i has zero principal divisor. It is constant on the connected projective normalization. Along the neutral real arc each f_i tends to one, so its constant is one. Taking positive real logarithms gives e dot H=0 on I. The rational kernel has a rational basis, so every real vector in ker_R(A) annihilates V_I.

Conversely let a real covector c annihilate V_I. Differentiating its identically zero function on I gives the meromorphic differential identity sum_i c_i d f_i/f_i=0. Analytic continuation extends that identity to the irreducible complex carrier. Its residue at each normalized point is sum_i c_i ord(f_i), so A*c=0. Thus the annihilator of V_I is EXACTLY ker_R(A). Double annihilation in finite-dimensional real linear algebra gives V_I=rowspace_R(A). QED.

No Baker premise or algebraicity of c is needed. Full criticality of I for c is also unnecessary for this value-space theorem; the carrier itself and its neutral strict arc are the supplied source data. Nonneutral carriers need an affine constant-level treatment, not this linear identity. Merely including some convenient zeros/poles would give the wrong matrix.

For a finite collection of supplied infinitely populated neutral retained arcs, their summed COMPLETE value space is therefore computably rational by summing these row spaces. This does not identify the arcs or their occurrence counts from arbitrary input.

## 3. A complete arc-compatibility predicate from rational V

Now supply a rational subspace V of R^d and an effectively real-algebraic residue node r with 0<r<1. Compute an integer row basis e_1,...,e_s for V-perp and define the ACTUAL strict source set

    T_V={0<p,q<1: product_i f_i(p,q)^e_ki=1, every k}.

Negative exponents are cleared by the positive f_i denominators, so this is semialgebraic over the rational numbers. It is not a freely chosen kernel set.

**Theorem 2.** The following conditions are equivalent and are decidable by a finite RCF procedure from V and r:

1. There exists a strict analytic COMMON factor arc (p(t),q(t)) extending analytically to (0,r), whose COMPLETE log-value space is included in V.
2. (0,r) belongs to the closure of T_V.

**Proof.** For every strict factor, H belongs to V exactly when every integer annihilator row has zero log value; positivity makes that equivalent to the displayed monomial equations. Condition 1 therefore gives a curve in T_V approaching (0,r), and hence condition 2.

Conversely, (0,r) is a boundary point outside the strict set T_V. Semialgebraic curve selection gives a curve in T_V approaching that point. After a finite Puiseux reparametrization it extends as an analytic arc in the parameter t at zero, with p(0)=0, q(0)=r and 0<p(t),q(t)<1 for small t>0. The f_i approach one, so their real logarithms extend analytically there. Every value H(t) belongs to V by the exact monomial equations; consequently its ENTIRE span belongs to V. This is the required analytic source arc. QED.

Closure membership can be written directly as the RCF formula

    for every delta>0 there exists (p,q) in T_V
        with p^2+(q-r)^2<delta^2.

Complete real-algebraic quantifier elimination decides it. Passing gives a real algebraic arc certificate in principle; this note claims no executed QE, numeric neighbourhood, explicit arc or approximation count. If V=R^d, the empty equation list has the expected meaning.

The predicate is NECESSARY AND SUFFICIENT for existence of a source arc with the full inclusion premise. It is not merely a test that R(r), one tangent direction, or a local response derivative belongs to V. The algorithm requires the supplied residue to be algebraic; algebraic observations alone do not establish that hidden-residue premise.

## 4. Actual attained normal-form consequence, reusing prior proof

Suppose an actual capped COMMON closure normal form has positive baseline, no killing, a summable retained list and finitely many positive residue terms w_k*R(r_k). Supply the retained-arc/pivot certificate required by the accepted theorem, with its whole-image and tail inclusions and submersion onto V. If V is obtained from supplied neutral algebraic carriers as in Theorem 1, and the residue nodes are supplied algebraic, Theorem 2 decides EACH remaining complete arc-compatibility premise.

When every predicate passes, the accepted integer-copy approximation/retained-pivot correction proves one EXACT finite strict COMMON word with the same capped signature. All rows use the same corrected physical factors. This is a more effective interface for an inherited sufficient theorem; the attained-normal-form conclusion is not presented as a new reproof or a total algorithm.

A failed predicate means that this V lacks an arc with the full required inclusion. It does NOT mean that the target is NO: another pivot space, another normal form or a remote actual presentation may exist. The algorithm must not return NO on that basis.

## 5. Does this finish the complete recognition attempt?

No. The proposed finite neutral-carrier catalogue can make the candidate V spaces finite at a fixed cap, and the present theorems make their exact algebraic-residue compatibility test finite. They still do not find the source-consistent retained pivots, bound integer unit-level words, bound isolated critical repetitions as the normal varies, or classify every unsupported/killing/zero-baseline form. The catalogue itself is not yet an accepted premise at this note's writing. Transcendental residue nodes remain outside Theorem 2's effective-input promise.

The original finite observation input may project to a positive-dimensional hidden kernel fibre and need not select one algebraic normal-form tuple. Actual original-ID controls, coupled channel normalizations, exterior shared registers and INDEPENDENT routing remain their original separate obligations. Neither logarithmic dimension nor the new RCF predicate is a substitute for the whole observation compiler.

Thus this attempt closes a specific complete-value-space TEST interface conditionally, while the global integer-count/normal extraction and boundary-attainment gates remain. No full recognizer, NO completeness theorem, impossible-master result, executed implementation or Lean coverage is claimed.

## Attribution

COMMON factor compilation, semialgebraic curve selection, principal divisors/logarithmic residues, finite algebraic normalization and RCF are inherited classical/source tools. The reviewer owns the frozen carrier-catalogue proof. G5 supplies this separately frozen full-value-span/arc-compatibility connection to the accepted ARC-SUPPORTED source theorem. The old attainment proof retains its credit, integer copies and actual retained pivots. Historical novelty is unassessed. Root independent review is requested before promotion.
