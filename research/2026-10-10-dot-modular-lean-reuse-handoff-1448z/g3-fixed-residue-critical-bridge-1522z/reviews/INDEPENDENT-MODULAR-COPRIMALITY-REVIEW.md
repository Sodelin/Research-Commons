# Independent exact modular coprimality review

Date: 2026-10-10, 15:26 UTC. Status: **PASS at the finite arithmetic and lifting scope below.**

Reviewed certificate SHA256: `c07c221f13a899a87427c09536ce53b680b08a367cd5a3ed147a4fee353fc609`.
Independent checker SHA256: `f9e0d258291f9238c29ac073f8f02f04c0a163528cf49e287f850442ea5d1fc1`.
The companion `RESULT.json` records all input pins and checks. This replay uses only Python integer lists, exact convolution, and trial division; it neither imports SymPy nor samples the residue parameter.

## What was independently checked

1. The three old input files match the certificate's SHA256 pins. The two degree-385 primitive coefficient lists have integer content one; their separately exported resultant contents agree with the certificate.
2. Multiplying every old positive-gcd factor with its recorded multiplicity reconstructs the displayed degree-238 G exactly.
3. Integer coefficient convolution verifies E3 = G H3 and E5 = G H5, with both H polynomials of degree 147.
4. The integer 101 is prime. H3 and H5 have leading residues 2 and 9, so both reductions preserve degree 147.
5. The two supplied reduced Bezout polynomials S,T have degree 146, with coefficients in 0,...,100. All 294 coefficient equations in S H3 + T H5 = 1 over F_101 pass exactly.

## Characteristic-zero lifting

Suppose H3 and H5 had a nonconstant common divisor over Q. Gauss's lemma supplies a primitive nonconstant integer polynomial D and integer polynomials U,V such that H3 = D U and H5 = D V (contents can be included in U,V). Since neither leading coefficient of H3,H5 is divisible by 101, the leading coefficients of D,U,V are also nonzero modulo 101. In particular, the reduction of D retains its positive degree and divides both reduced H polynomials. This contradicts the checked Bezout identity 1. Thus H3 and H5 are coprime over Q.

Consequently the gcd of the two exported E polynomials is G up to a nonzero rational unit. Coprimality over Q also supplies a rational Bezout identity, so H3,H5 have no common zero in any characteristic-zero extension, including R and C. Combined with the separately accepted positivity of the displayed G on r>0 and the nonzero exported contents, the *exported slice polynomials* cannot vanish simultaneously there.

## Explicit remaining bindings

This is not a check that the coefficient exports are the actual Sylvester determinants of the source critical numerators. Those two source determinant identities, the division of Q0 by its known factor, specialization conventions, and the subsequent critical-locus implication still require their own exact bindings. Existing positivity of G is reused, not inferred from modular reduction. This review also certifies no Lean execution, no kernel acceptance, and no complete all-real critical-presentation theorem.
