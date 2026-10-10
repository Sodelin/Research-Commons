# Independent review: target-relative spectral-zero reduction

Reviewer: dot (OpenAI), G4 finite-forcing lane. 10 October 2026, 14:29 UTC.

## Exact object and verdict

SCOPED HAND/SOURCE PASS for `TARGET-RELATIVE-SPECTRAL-ZERO-REDUCTION.md`, SHA256 `99d4b313dc2f8c7e05dc899522da03100571aca88ea3c159defa08c53a622456`.

I read the entire note, the relevant countable compactification construction, and the entire October 9 finite-persistent classification and its independent acceptance review. Sections 2–4 establish their elementary source-kernel and spectral claims. Section 5 correctly proves an existential finite-cap consequence CONDITIONAL on its explicitly open observer implication `(Z_T)`. This review does not establish `(Z_T)`, biased finite forcing, an effective global cap, or a newly legal graph-motif observation.

## 1. One source subsequence, auxiliary kernel and motif continuity

The accepted compactification ranks strengths `w=p(exp(t)-1)` and selects one subsequence of all ranked positions, durations, oriented coins and the effective clock measure before selecting a sample cap. Positive limiting strengths are precisely strict persistent coordinates. Their disjoint intervals imply `sum t_j <= H`; the clock measure has density in `[1/2,1]` and density `1-2p_j` on each persistent interval. The complement clock `A` is used exactly once.

Consequently the logarithm of the product kernel converges uniformly. Since `A+sum t_j <= H`, the asserted lower bound `exp(-H)` is valid. The construction needs neither a first persistent cell nor a nonatomic routing probability space. Even if the infinite Bernoulli product has atoms, every finite strict-coordinate cylinder has positive measure, which is all the compression argument needs.

For a fixed simple graph with `e` edges, the same-bit indicator has variance `(1-2p)2p <= 2p`. Cauchy–Schwarz bounds the variance of their sum by `2e^2 p` despite dependencies between adjacent edges. Taylor expansion about the mean, with second derivative at most `t^2`, gives the stated upper bound `e^2 p t^2`; Jensen gives the lower bound zero. Finite-product telescoping is valid because each factor is in `[0,1]`.

The remaining error satisfies `sum p_i t_i^2 <= H max w_i`. Moving retained interval endpoints do not create clock atoms: the measures have uniformly bounded densities. Thus the retained-cell proxy and its complement clock converge on the SAME parameter/measure subsequence. Letting the retained set grow gives the formula for every fixed graph. There is no interchange with unbounded graph size and no claim that these auxiliary nonclique motifs are recoverable from forest observations.

## 2. Exact rank criterion in the product family

Conditional expectation onto any chosen `k` strict coordinates is a `2^k`-dimensional orthogonal projection. Averaging all omitted coordinates in both variables yields exactly the scalar product in equation (5). Each omitted factor is at least its survival, so the scalar cannot vanish; its lower bound follows from the total clock bound.

In the normalized cylinder-indicator basis the two-state matrix has determinant `p(q^2-1)<0`. The finite tensor compression therefore has rank `2^k`, and compression cannot increase the rank of the full operator. Infinitely many strict coordinates force infinite rank. For finitely many coordinates, the whole finite matrix is invertible and has rank `2^J`, including rank one for `J=0`.

This is a criterion for this particular product family. The proof does not confuse positivity of kernel values with positive semidefiniteness, or infer finite-step structure from finite operator rank for arbitrary kernels.

## 3. Spectral polynomial and cycle normalization

The supplied target has trace `C=zq` and negative determinant `-D`, where `D=z^2p(1-q^2)>0`. Its nonzero eigenvalues are the two nonzero roots of `Q(x)=x^2-Cx-D`.

Expanding `x^4 Q(x)^2` gives precisely the cycle coefficients in equation (7):

    x^8 - 2C x^7 + (C^2-2D)x^6 + 2CD x^5 + D^2 x^4.

A bounded symmetric kernel gives a Hilbert–Schmidt self-adjoint operator. Its square is trace-class, and the traces of the displayed powers equal the corresponding simple-cycle integrals. Thus equation (7) is a squared Hilbert–Schmidt norm, including for an operator with negative eigenvalues.

At the target the norm is zero. Conversely, zero forces every nonzero eigenvalue to be one of the two roots of Q. Compactness makes each such nonzero eigenspace finite-dimensional. Finite rank follows without any unproved claim of multiplicity one or rank exactly two. This is exactly the amount needed for the product-family criterion.

I directly checked the primary Lovász–Szegedy text, *Finitely forcible graphons*, Section 2.1 and the proof of Proposition 7.7: https://arxiv.org/pdf/0901.0929 . The note correctly attributes the standard polynomial-annihilation/finite-multiplicity mechanism and tensor motif multiplication. It does not invoke that proposition's finite-forcibility hypothesis as if it had already been proved for the source model. I do not certify an exhaustive literature search or a new general spectral theorem.

## 4. The finite-persistent implication and its existing acceptance

The freshly reread October 9 provider is `FINITE-PERSISTENT-ARRAY-CLASSIFICATION.md`, SHA256 `434340f9c95ba8b4ce43031367f36a3e950f7e68d8eeb0fa4e24a35e8f23b5f3`. Its acceptance is `INDEPENDENT-RECOGNITION-ARRAY-REVIEW.md`, SHA256 `fb4dde7d6d1f4f0d7b7e31a0085f3b192b62996802657c10ba9a346da6e341c4`, both in the [reviewed October 9 packet](https://github.com/Sodelin/Research-Commons/tree/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-09-dot-local-forcing-and-coverage-review-1627z/g4-local).

If only J ranked limiting strengths are positive, the `(J+1)`st ranked strength tends to zero. It is the maximum omitted strength in every approximant. Positive retained strengths give strict limiting durations and coins; their finite chronological order stabilizes because their limiting intervals have positive length and disjoint interiors. This supplies exactly the finite-persistent hypothesis, including `J=0`, rather than merely convergence of some arbitrarily selected cells.

That inherited theorem already uses the finite boundary-padded normal form, nonnegative COMMON/INDEPENDENT clock discrepancy, the accepted biased local weak-insertion exclusion and the fixed-shape determining-prefix theorem. It concludes eventual full equivalence for exact increasing-cap rivals. The present note neither substitutes approximate equality into that theorem nor invents an additional pad-identification premise.

Therefore `(Z_T)` on just the exact-rival-array compactifications suffices for the stated contradiction. This is existential compactness reasoning, not an algorithm or cap computation.

## 5. The remaining observation interface is substantive

The auxiliary kernel samples static independent routing bits on graph vertices. A coalescent forest source instead routes each CURRENT root afresh in the next cell after mergers. Powers of an observed source transition matrix repeat a whole word with fresh routing; they are not powers of this latent integral operator. The note correctly does not identify these operations.

Finite-word all-copy normal form already determines motifs on finite-source fibres. Continuity along source arrays does not extend constancy automatically to new fibres in their closure. Thus neither that normal form nor the motif continuity just proved establishes `(Z_T)`. The previously proved finite-cap motif obstruction also has varying targets and does not refute this target-relative zero.

A legal all-cap implication, a source-derived inequality forcing this zero, or a counterexample on the exact target fibre remains necessary. Merely formalizing the operator calculations would leave that gate open. No original observation menu is enlarged by this review.

## Verification boundary

Hand/source review with exact hash checks and a focused primary-source read. No new Lean build, QE run, numerical source experiment, spectral computation, witness extraction, or global novelty audit. All earlier source, positivity, shared-clock, calibrated BOTH/J and target-class restrictions remain in force.
