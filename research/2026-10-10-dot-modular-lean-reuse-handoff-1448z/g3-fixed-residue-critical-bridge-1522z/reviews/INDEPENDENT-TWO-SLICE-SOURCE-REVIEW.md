# Independent two-slice source arithmetic review

Date: 2026-10-10, 15:43 UTC. Status: **SCOPED EXACT/SOURCE PASS** for the certificate data and their mathematical assembly interface. No new Lean run or kernel theorem is certified here.

## Exact final inputs and executions

- Modular coprimality certificate: `c07c221f13a899a87427c09536ce53b680b08a367cd5a3ed147a4fee353fc609`, independently reviewed in `INDEPENDENT-MODULAR-COPRIMALITY-REVIEW.md`, SHA256 `2f19732fa1e05a1a278fd8c7ff36cdd21a51003d4a451daa2f02dc21b63912f8`.
- q=3 source certificate: final `dc1a071a81ef7f9b0f6ee4d97dae3559e4ee8153248c87a053c821b8a388bb42`. Its entire mathematical content agrees with independently replayed snapshot `100c5631fd8682a3bd7f6eed5fa69465755559963cd9d61eabd80a7ca4fb98e3`. The sole difference is the elapsed-time metadata. Exact comparison receipt: `c75fd06d184c3fd7a5b6230bb97f0717dfebfea1671cc3c9a63fe542bbfe2fe4`. The earlier partial generation failure and its snapshots remain preserved.
- q=5 source certificate: `4e33a9a93c579666526202d304d77fb300dfd47ce472183014e524da54d4e470`. Independent checker `1610e991a9f1b619a722c04b7a4597106b4dcd7d612271ae449d8eb8eba19491`; result `c90459ff7c87fdad23eba4a0386c4dce677ed826d9ff952bd9ec71b97db50833`.

The q=3 and q=5 replays take approximately 0.16 and 0.18 seconds. They use only exact nested integer arrays, under 30-second CPU and 256-MiB bounds. They reconstruct source P and Q0 from the pinned old B coefficients, check Q0=(1-p)Q, and verify every coefficient of U P+V Q=D and D W=K E_z. Both W polynomials are the constant 1 and both K integers are nonzero. The generic implication would only need K nonzero, not a nonvanishing W assumption.

The first q=5 replay had a stale result-key label saying E3, although the executed input was correctly E5. The final checker and result fix that label; the first result is preserved. No arithmetic formula changed.

## Existing imported coefficients also match

A separate strict source-expression parser consumed every monomial of the six existing `normalB0` through `normalB5` definitions, source SHA256 `bbe8ec1f645faeb7436828c9a7e00bb23138a6361fcadd098a8804b50d0c4749`. All 222 displayed monomials, including the positions of all omitted zero coefficients, agree with the old normal export `cc57db65563ac4a7e2f5bf9581b8b75803f2052a49d19442f5e756a0f82996e3`. The degrees are 49,49,46,42,32,20. The full expressions are consumed; this is not a spot check or parameter sampling.

Checker: `eeba989911384989bb3780426fec7d0d5138d5b9e05737020afb7bd0fda4cb6a`.
Result: `558797d3a6072fb6464b62abfaab53c10497def82f6357e919db2c84eccd88c8`.
This source audit supports, but does not replace, the corresponding Lean equality theorem between imported definitions and the new coefficient representation.

## Mathematical assembly, with its degree conditions

For every real r>0, the modular certificate plus the inherited positive G factorization implies that E3(r),E5(r) cannot both vanish. Choose z in {3,5} with E_z(r) nonzero. The checked source identity then supplies a nonzero scalar Bezout identity for the actual P(r,p,z),Q(r,p,z). Thus they are coprime as polynomials in p.

At either witness z, the existing general fifth-coefficient identity gives

    coeff_(p^5) P = -normalMass(r) product_i (1-z^lambda_i),

which is nonzero. This uses r>0 and z>1; the existing convenience lemma with hypothesis 0<q<1 must not be applied at z. Q has p-degree at most four. Hence the appropriate padded 5-by-4 resultant at z is nonzero, even if Q drops degree. The resultant of the generic source P,Q is therefore a nonzero polynomial in q.

Every strict critical pair has P=Q0=0. Since p<1, Q0=(1-p)Q gives Q=0, so its q-coordinate is a root of that generic resultant. At every strict q, the existing nonzero fifth-coefficient theorem bounds the p-fibre by five roots. This is exactly the inherited all-real fixed-r finiteness mechanism. A quantitative 2495 count additionally uses the usual source q-degree bounds 56 for P and 55 for Q and the padded determinant degree bound 4*56+5*55=499; that degree/count formalization is not inferred merely from the two finite certificates.

The algebraic witness survivals 3 and 5 are not admitted source survivals or extra tests. They only establish that a polynomial is not identically zero. No determinant equality between an old exported E_z and the new generic source determinant is needed if the implementation follows these direct source Bezout identities and the correctly padded nonvanishing argument.

## Verification boundary

The finite certificate and literal old-source coefficient gates have independent exact checks. Import bindings, coefficient-list-to-polynomial identities, generic Q0 division, specialization, padded-resultant degree lemmas, finite root/fibre assembly, full dependency build and axiom audit still require actual Lean results. The generator's final bounded success does not erase its earlier resource failures. This review supplies no compactness/count bound uniform in r, no normalized complex-curve/logarithm formalization, no effective transcendental enumeration and no original-source membership algorithm.
