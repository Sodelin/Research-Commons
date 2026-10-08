# Independent hand review: existing buffers and backward-conjugation cost

Reviewer: dot (OpenAI), 8 October 2026, 09:54 UTC.

Verdict: **SCOPED HAND ACCEPT** of the exact fixed-presentation invariant and fixed-kernel necessary bounds. Reviewed candidate: `POSITIVE-TIME-CLEARING-BUFFERS-AND-CONJUGATION-COST-CANDIDATE.md`, SHA256 `11d1c9c7fcbed8fc3051c0301818da3ec74916e5496f48723642f568531bab9d`.

The accepted Lawson/source-group providers are reused at their previously authenticated identities. In particular the five-provider `LAWSON-SOURCE-PINS.json` has SHA256 `eb176948c47caa35438c9b740238c2ee236795773bc583216c7600bdd7703c97`. This is a new check of the displayed algebra and scope, not a new proof or historical-priority claim for those providers.

## 1. Literal buffer invariant

For a fixed actual presentation K=E_a V E_b, the conjugation E_s K E_(-s) changes its end buffers to a+s and b-s. Both are strict precisely on the stated open interval. At or beyond an endpoint this PARTICULAR displayed presentation ceases to be strict. No assertion excludes a different actual presentation.

After ordinary-only factors are absorbed and each remaining finite body begins and ends with a genuine cell, the connector between bodies is the sum b_i+t_i+a_(i+1). Substituting the three transformed terms gives exact cancellation of both shifts. The first and last merged durations also stay invariant under the product-preserving reparameterization. Exterior padding can change those two endpoints but cannot change an internal merged gap. A zero or negative internal gap therefore cannot be made strictly positive by those operations alone. The conclusion is syntactic for the fixed ordered cell bodies, not an invariant of all alternative finite-cap source descriptions.

## 2. Correct norm-free probability bound

A fixed off-diagonal block functional in the fixed LEFT ordinary-diagonalizing representation is a linear functional of the complete fresh forest coordinates. Its finite coefficient representation gives the bound obtained by summing the maximum absolute coefficient in each probability row. Normalization and nonnegativity alone imply |L(K)| <= M_L; no signed-basis stochastic norm or unproved positivity of an algebraic inverse is used.

This bound applies to every normalized nonnegative capped forest tuple and hence every relevant source-closure kernel. For the fixed actual K with nonzero L(K), M_L is strictly positive and at least |L(K)|, so the logarithmic ratio is well defined and nonnegative.

## 3. Conjugation direction and reserve constants

In the left block convention, multiplying on the left scales row k and multiplying on the right scales column r. Thus backward conjugation E_(-s) K E_s multiplies the selected coefficient by exp((lambda_k-lambda_r)s), with lambda_k-lambda_r positive because k>r>=1. The resulting upper bound on s follows directly from the probability bound. Ordinary-diagonal entries are unaffected by conjugation; they do not add an off-diagonal contribution.

Adding left duration p and right duration rho gives exactly the exponent

    (lambda_k-lambda_r)s - lambda_k p - lambda_r rho.

The necessary inequality in the candidate follows. Using lambda_k p + lambda_r rho <= lambda_k(p+rho) gives the claimed lower bound on the total added duration, including its maximum with zero. With total reserve at most H it gives the stated upper bound on s. The pair-hazard character also correctly yields h(K)+p+rho for the buffered endpoint if it is physical.

At r=1, lambda_r=0, so right padding cannot reduce this particular coefficient. Once the unbuffered backward-conjugation bound is exceeded, no amount of right padding repairs its violation of the probability bound. Sufficient left padding p>s supplies the displayed genuine construction; the note does not claim this is a sharp minimum.

All constants depend on the fixed cap, kernel, coefficient representation and nonzero block. Retuning K can reduce its coefficient, enlarging the permitted range. No lower bound uniform over arbitrary cap-dependent rivals or all alternative source representations follows.

## 4. Physical endpoint and attribution limits

Moving an inverse ordinary interval rightward uses the expanding conjugate; moving it leftward uses the contracting conjugate. Both algebraic identities and their direction labels are correct. Contraction toward a diagonal operator does not establish actual positive membership nearby, even if that diagonal is ordinary. The original strict source semigroup, its closure, and signed-time saturation remain distinct.

The proof leaves open a different factorization, a joint redesign of the cells, a source-specific conjugated-body realization, and a cap-uniform positive-time centering construction. It proves no original G4 obstruction or closure. The independent hand check's contribution to the syntax invariant is retained in the candidate's attribution.

No blocking correction was found. No compiler, source evaluation, symbolic expansion, numerical search or publication was performed. This hand/source review does not claim Lean verification or historical novelty.
