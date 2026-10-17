# Third mathematical review receipt

2026-10-17 UTC. dot (OpenAI), working with Nolan. Independent hand review of `SHARP-CONDUCTANCE-DETERMINANT-BOUND-REVIEW-06.md`, SHA256 `aa47f32ddd05f0606e109bf1586cd940ff9ccd23a619dc7e6d0b2f55b7534ce0`.

## Verdict: PASS within the stated algebraic scope

No defect found in the full proof of

    det r >= |g-2|-1

for canonical PHS 4x4 contractions with exactly two electron modes and g=2-||A||_F^2+||B||_F^2. This is a hand-proof review, not machine verification, experimental validation, physical extremizer admission, or historical novelty certification.

Checks performed:

- Block trace gives (1/2)Tr(QrQr†)=||A||_F^2-||B||_F^2. The displayed W is unitary, makes r real under canonical PHS, and sends Q to iJ with the stated sign. The antisymmetric-matrix inner product gives q=<J,MJM^T> and ||J||^2=2, without an omitted factor.
- With orientation (1,2,3,4), *E13=-E24, so J is anti-self-dual; all three displayed f vectors have the asserted Hodge sign and unit norm.
- An ordinary SVD can always be oriented on both sides: for O1 Σ O2^T, set F=diag(1,1,1,det O1), G=diag(1,1,1,det O2); then U=O1F and V=O2G lie in SO(4), and D=FΣG. This includes rank deficiency and the zero matrix. Product(di)=det M holds independently of rank.
- Both exterior rotation factors commute with the Hodge projection and restrict to orthogonal maps. Thus the compression norm is unchanged; the three diagonal entries for D are exactly the complementary product sums divided by two. No false assertion of Hodge invariance for D is required.
- For a,b in [-1,1], the two displayed products imply |a+b|<=1+ab, including endpoints and negative ab. Each complementary pair has ab=det M. Multiplication by ||J||^2=2 cancels the compression's factor 1/2 and yields the claimed inequality.
- Both sharpness diagonal families satisfy contractivity and give exactly the stated q, determinant and g. W†MW restores canonical PHS. This proves abstract sharpness only, as the source correctly says.
- The interval minimum and strict/non-strict positive-margin statements are correct. If the error interval does not intersect physical [0,4], the measurement/model premises are inconsistent; such an interval is not a usable certificate. Clipping a consistent interval to [0,4] is optional and can only improve its lower bound.

The g<0.004 implication det r>0.996 follows exactly. Intermediate g does not provide a negative certificate.

## Prior-work disposition

The separate `DIRECTED-PRIOR-REVIEW-20261017-0059.md` remains applicable: unitary two-electron negative determinant implies g=2 in Beenakker et al. arXiv:1012.0932 Sec.IV A and related Béri bounds; Marciani et al. Physica E77 (2016) Eqs.48-52 contains the one-electron nonunitary antecedent. No exact general four-dimensional inequality was located in that bounded search, which does not establish novelty. The current theorem reduces consistently to g=2 at det r=-1.

Recommended status: mathematically reviewed exact algebraic sufficient bound with abstract sharpness; novelty unresolved. Keep zero-energy, zero-temperature/zero-bias physical readout assumptions and the distinction between finite determinant sign and protected thermodynamic topology.
