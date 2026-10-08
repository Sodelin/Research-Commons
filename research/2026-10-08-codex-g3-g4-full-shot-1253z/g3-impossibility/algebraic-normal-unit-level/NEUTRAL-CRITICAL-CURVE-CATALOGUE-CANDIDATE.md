# A finite cap-dependent catalogue of neutral-reaching COMMON critical curves

Contributor: Codex reviewer lane, 8 October 2026. **HAND-DERIVED CANDIDATE; independent root review required.** This is the author's contribution, not covered by the adjacent independent review of G5. No catalogue, factorization, source instance, solver, symbolic calculation or program was executed. This note describes a mathematical algorithm and its source-level proof.

The purpose is to remove one specific unknown-family gate in a full G3 attempt. It does not decide word membership, bound all source counts, establish a full recognizer, or prove undecidability.

## Actual source and precise claim

For fixed finite cap let the distinct positive integer exponents be `lambda_1,...,lambda_d`, in the original COMMON case `1,3,6,...,binom(M,2)`. Put

    f_i(p,q)=1-p+p q^lambda_i,
    H_i(p,q)=-log f_i(p,q),   0<p,q<1.

These are the inherited coordinates of one actual natural unequal COMMON factor. They are not freely chosen moments, an external mixture, new readouts or INDEPENDENT kernels. The actual whole word uses the same cell parameters across all capped forest coordinates and has a positive ordinary baseline.

For any nonzero **real** normal c, define its strict critical set by `c H_p=c H_q=0`. A neutral-reaching critical curve means a one-dimensional real semialgebraic piece of this set with an arc whose closure in the closed unit square contains a point where `p(1-q)=0`. The normal is fixed on that arc. No algebraicity of c is required for the claim below.

**Candidate theorem.** For each cap, there is a finite effectively enumerable list of plane algebraic curves over the real algebraic numbers which contains the irreducible algebraic closure of every such neutral-reaching critical arc, for every nonzero real normal. Each listed curve's strict neutral-reaching real pieces and the linear spaces of normals making it critical can be filtered by finite algebraic procedures. Optional ordinary neutrality `c Lambda=0` can be imposed in that filter. The list is cap-dependent and may be enormous.

This is a catalogue of curves and their normal spaces, not a finite list of all normal vectors, all critical points, all words, or all finite witnesses.

## 1. Fixed degree of a critical curve

After clearing the positive factor denominators and the nonzero factor p in the q derivative, the two critical polynomials can be taken as

    P_c = sum_i c_i (1-q^lambda_i) product_(j != i) f_j,
    Q_c = sum_i c_i lambda_i q^(lambda_i-1) product_(j != i) f_j.

The sign of each derivative is irrelevant to its zero set. Define

    delta_i=lambda_i+1,
    D=sum_i lambda_i+d-1.

Their total degrees are at most D and D-1. Moreover P_c is not the zero polynomial: at p=0 it is `sum_i c_i(1-q^lambda_i)`, whose distinct positive powers force all c_i to vanish if it is zero. Thus every irreducible complex curve carrying a critical real arc has degree at most D. It cannot be a two-dimensional critical component.

Take the irreducible complex algebraic closure C of one critical arc. The cleared polynomials vanish on the arc and hence on C. At the real strict points every f_i is nonzero, so none is identically zero on C. These conclusions still hold when the polynomial coefficients c are arbitrary real numbers: complex factorization and algebraic closure here are mathematical constructions over the coefficient field in C, not claims that c is algebraic.

## 2. A bounded integer divisor matrix

Use the smooth projective normalization of C. Each f_i is a nonzero meromorphic function there. Its principal divisor has integer orders at finitely many points. Because f_i is the restriction of a polynomial of total degree delta_i, its homogenized numerator is a nonzero section of degree `delta_i deg(C)`, and its affine denominator is the corresponding power of the projective affine-coordinate section. Therefore:

    |ord_P(f_i)| <= D delta_i,
    sum_P max(ord_P(f_i),0) <= D delta_i,
    sum_P max(-ord_P(f_i),0) <= D delta_i.

Cancellation at infinity only reduces these bounds. They apply on the normalization, so singular branches are counted separately; no smoothness of the plane curve is assumed.

Make a matrix A whose rows are the order vectors `(ord_P f_1,...,ord_P f_d)` at all points where any order is nonzero. It has at most

    B=2 D sum_i delta_i

rows, and every entry is an integer of magnitude at most `D max_i delta_i`. Thus A belongs to a finite cap-computable set of integer matrices, irrespective of the curve's coefficients or of the normal's arithmetic height. Zero rows may be padded to use the common bound B.

## 3. Criticality forces a nonzero rational relation space

Full criticality gives on the real arc

    sum_i c_i d f_i/f_i = 0.

This is a meromorphic differential identity on the irreducible complex curve, by continuation from the arc. Its residue at any normalized point P is `sum_i c_i ord_P(f_i)`. Hence

    A c=0.

Since c is nonzero, the integer matrix A has a nonzero rational kernel. This uses residues of logarithmic derivatives directly; it does **not** split algebraic differential coefficients by Q-independence and does not require Baker.

For any integer vector e in this rational kernel, the meromorphic monomial `product_i f_i^e_i` has zero principal divisor. A meromorphic function with no zeros or poles on a connected smooth projective curve is a nonzero constant. Negative powers cause no problem for this function-field argument; actual strict factors remain positive.

Along the neutral-reaching arc, `p(1-q)->0` implies

    0 <= 1-f_i <= lambda_i p(1-q) -> 0.

Every one of these constant monomials therefore has value **one**. In particular, choose one nonzero primitive integer vector e in `ker_Q A`. Then C lies in the unit equation

    U_e(p,q)=product_(e_i>0) f_i^e_i
             - product_(e_i<0) f_i^(-e_i) = 0.

The empty product is one.

## 4. Why only finitely many curves remain

Enumerate the finite bounded set of integer matrices from section 2. For every matrix with nonzero rational kernel, choose a nonzero primitive integer kernel vector by exact rational linear algebra. There are finitely many chosen vectors, even though the bound may be impractical. Form their U_e polynomials.

Each U_e is nonzero. The actual distinct f_i are irreducible, nonassociate polynomials in C[p,q]: each is primitive and linear in p with constant coefficient one, and its q exponent distinguishes it. Unique factorization therefore forbids `product_i f_i^e_i=1` as a rational-function identity for nonzero e. This step uses the actual source factor family, not an arbitrary parameterized torus map.

C is an irreducible component of one of these finitely many nonzero plane polynomials. Their coefficients are integers. Absolute factorization supplies finitely many component equations with algebraic coefficients. Retain the real components supporting strict one-dimensional arcs and neutral-reaching pieces. Standard finite algebraic factorization, real algebraic decomposition and closure tests describe a terminating catalogue algorithm. No such operations have been run here.

For a listed irreducible component G, the condition that it be critical for c is the pair of identities `G divides P_c` and `G divides Q_c`. These are finitely many homogeneous linear conditions in c with algebraic coefficients, obtainable by polynomial reduction. Add `c Lambda=0` if needed. Whether the resulting real normal space is nonzero is exact finite linear algebra. If it is nonzero, it contains an algebraic basis, but it generally contains infinitely many normal vectors. The critical and neutral real-piece tests must both pass; algebraic components that merely occur in an over-enumerated unit equation are not automatically physical critical curves.

## 5. What this removes, and what it does not

This candidate would replace an unbounded search over **neutral-reaching critical curves** by a finite cap-dependent catalogue, including real normals. It is stronger on that family gate than requiring an algebraic supplied normal. It does not invalidate G5's affine-level correction: nonneutral curves can have nonunit constant levels, and their values remain affine rather than linear.

For each fixed normal, the inherited neutral-tail analysis and semialgebraic finiteness show that any critical sequence with summed pair loss finite and infinitely many occurrences must approach a neutral-reaching curve. The candidate therefore identifies the possible curve carriers of such sequences. It does not give the loss floor uniformly as the normal varies.

In fact a cap-only floor over all normals is unavailable by a direct source control. At d>=4, for every strict cell the three vectors Lambda, H_p and H_q have a nonzero common annihilator. Choosing rational `p=1/n,q=1/2` gives rational derivative entries and an algebraic ordinary-neutral critical normal; its pair loss is `1/(2n)`. Thus arbitrarily weak actual critical cells occur as the normal varies. This control does not keep one target fixed and is not a G3 impossibility or an input-bound counterexample.

Most importantly, a finite catalogue does not decide whether a given algebraic target is a product of finitely many actual factors on its curves, with integer occurrences and all original shared constraints. The curve parameters remain continuous, the factors cannot be given fractional multiplicities, and a smaller torus/log dimension is not a smaller Kingman cap. Isolated critical cells depending on the unknown normal also remain. Full original G3 additionally retains boundary-NO normal extraction, coupled all-core fibres, controls/registers and INDEPENDENT chronology.

## Prior and review boundary

The actual COMMON normalization, fixed-cap compiler and critical equations are inherited. The earlier neutral-accumulation provider already isolates the dangerous p->0 interior-node branch for a fixed real normal; G5's corrected Baker split gives constant rational component levels for algebraic normals. The new attempted step is the bounded-degree/divisor catalogue of neutral-reaching curves. Bezout, principal divisors, logarithmic residues and absolute factorization are classical tools; no historical novelty claim is made.

Root must independently check the normalization, degree and divisor bounds, continuation/residue step and finite-catalogue deduction before acceptance. The author does not approve this contribution. Full G3/G4 remain open.
