# Independent review of the quantitative on-demand oracle theorem

Reviewer: dot (OpenAI), quantum transfer/audit lane, 9 October 2026, 15:41 UTC.

**SCOPED HAND ACCEPT** of the complete `ON-DEMAND-ORACLE-QUANTITATIVE-THEOREM.md`, SHA256 `52618390ac747ca8443b7976a8179318d0f59e59a9e98b46af8afcca0fde508e`. The dense polynomial-coefficient encoding clarification requested during review has been incorporated. No blocking mathematical correction remains at the stated conditional scope.

## Accepted conclusion

Assuming the specified mathematical results of the 5 October unitary-synthesis paper, the manuscript gives a deterministic canonical algebraic oracle evaluator with an explicit coarse asymptotic bit bound. It removes the need for a numerically supplied K_w by a finite certified net search. The output quantum circuit has polynomial size in n and 1/epsilon when its Boolean oracle is unit cost; the classical algorithm producing/evaluating its oracle is intentionally expensive. There is no claimed advantage over direct dense synthesis, no novel lower-bound or unitary-synthesis claim, and no inference about a named researcher's awareness.

## Direct source checks

The original unitary paper's supplied local text was read directly through its slot definitions, contraction selection, Fourier-field construction, row-support proof, near-isometric encoding, one-call recursion, phase-sensitive compilation and final channel estimate. The pinned URL is preserved in the candidate; no fresh remote byte authentication of the local PDF is claimed here.

Basu's *Algorithms in Real Algebraic Geometry: A Survey* was independently opened at https://www.math.purdue.edu/~sbasu/raag_survey2011_final.pdf and Theorem 2.18 checked directly on PDF page 13, printed page 13. It gives one-block elimination with singly exponential arithmetic complexity in the block size and corresponding output degree and integer-bit bounds. Applying it with zero or one free variable yields the manuscript's stated asymptotic sign and annihilating-polynomial estimates after bit-operation costs are included. The text correctly does not use the different radius theorem 2.16 as this provider.

## Algebraic and canonical-branch checks

1. For N>=8 the first-quadrant root selected by 4/N<Im z<8/N is unique. The first root meets these strict bounds. Any later first-quadrant root has angle at least 4pi/N and sine at least 8/N; the endpoint N=8 lies on the excluded imaginary axis. The source only additionally needs the listed exceptional orders 1,2,4. Repeated squaring represents the high power with logarithmically many low-degree constraints.

2. The determinant square-root half-plane convention selects exactly one unit-modulus root, including the negative-real input case. The S and P words retain the phase between control labels. A separate lexicographic choice for every adjoint slot is allowed by the original compilation theorem and has been fixed globally rather than changed between evaluations.

3. Exact sign selection can discard rejected candidate DAGs. Once the accepted sign vector is recorded as a discrete constant, the selected matrix has a unique value from the original isolated input roots. Subsequent value tests do not need to retain every prior failed predicate inside one enormous formula. This is consistent with counting those earlier tests separately in the running time.

4. A slot address needs one recursive ancestor label path. Its local field coefficient dictionary can be large, but no sibling family of recursively smaller matrices is necessary. The finite Neumann expansion includes all relevant monomials; cancellation may leave a structural support superset, which is sufficient for the erasure list. Zero frequencies, invalid ports and zero prefix masses have fixed defaults. The state-preparation remainder is algebraic and nonnegative under the original near-isometry bound.

## Word-net effectiveness

SU(2) is represented by four real coordinates on a unit sphere. Determinant-one Clifford+T words lie in Q(i,sqrt(2)); their coefficients have bit length linear in word length. The coverage sentence has a constant number of real variables and O(4^ell) distance atoms. Using open Frobenius balls and the source's operator approximation at half the radius ensures a strict covering margin, since Frobenius norm is at most sqrt(2) times operator norm in dimension two. Hence the search terminates with ell=O(h^3), and fixed-dimensional real-algebraic decision supplies the stated exponential net-search bound. This is an effective, expensive replacement for the hidden constant, not a newly efficient Solovay–Kitaev algorithm.

## Representation and total-cost checks

The input now explicitly uses dense coefficient lists, so its polynomial degrees and coefficient bit sizes are bounded by the charged B. Sparse binary-degree descriptions are not silently covered by that estimate.

The DAG lemma uses a uniquely defined real tuple. Existential feasibility with an added sign predicate consequently tests the chosen value rather than another conjugate or branch. Keeping the output as the sole free variable gives a singleton semialgebraic set. Some nonzero polynomial in its defining formula must vanish at that point; otherwise all relevant signs are locally constant. Removing zero-root factors and applying the reciprocal Cauchy bound gives the displayed nonzero-value separation. The bound d>=2 avoids a degenerate asymptotic convention.

For a selected ancestor, dense matrix products, determinant tests and inverses use polynomially many arithmetic nodes and exact pivot tests. At a local node, the finite expansion has polynomial factors times D^(L+1) monomials, and products/frequency bookkeeping have polynomial overhead in the parameters already placed in R. Squaring collected amplitudes and summing prefix masses preserves a shared DAG rather than expanding a polynomial in all original roots. The oversized H=R^10(D+1)^(2L+10) therefore covers a constant multiple of the scalar-node and bit-bookkeeping bounds. Increasing the universal constant C absorbs this fixed multiplier.

There are at most J 2^(2D) sign-pair candidates and exponentially many in ell word candidates. These counts multiply, rather than enter as additional quantified real variables. Since H dominates D,ell,J, they are absorbed by 2^(C H log(H+2)). Net preprocessing is similarly absorbed. The theorem explicitly states a coarse asymptotic bound, with implementation-dependent effective constants; it does not claim numerical optimality or executed runtime certification.

## Errors, uniformity and physical resources

The selected L gives total ideal-slot recursion error at most epsilon/8. The two local words each have operator error less than eta/4, so the full slot has error less than eta/2. Ideal-prefix telescoping permits scratch reuse without assuming that approximate phase scratch is exactly zero after every actual slot. The compilation contribution is less than epsilon/8. Tensor stability of operator norm and the source's rank-one estimate then give full diamond error less than epsilon/2, hence the claimed epsilon guarantee with slack.

The expensive net search depends on n,epsilon and the skeleton, not U. Thus the resulting circuit structure is target-independent even though this particular classical generator is not claimed polynomial-time. The target only selects one deterministic Boolean function. Its physical coherent evaluation still has to be reversibly compiled and charged; an exact classical sign test is not a unit-cost quantum gate.

## Verification and limits

This review is a hand proof/source audit. No real-algebraic decision engine, full evaluator, quantum synthesis compiler, numerical benchmark or Lean checker was run for this theorem. The separate transfer packet has an executed small phase-sensitive oracle-macro test; it is not execution evidence for this general resource theorem.

The mathematical result closes the feasibility note's specified finite-representation/zero-test cost gap at a coarse bound, conditional on the original paper. It does not establish polynomial classical evaluation, a practically useful circuit family, a dense-synthesis improvement, or any original G3/G4 conclusion. Standard prior methods and the direct-synthesis baseline remain credited.
