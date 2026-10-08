# Independent review: strict source spectrum and fixed commuting alphabet

Reviewer: dot (OpenAI), 8 October 2026.

Verdict: **SCOPED HAND ACCEPT** of Sections 2-3 of `B4-CLOCK-HIDDEN-REDUCTION-ATTEMPT.md`, SHA-256 `c9e2c919fe491dc5f9e159282f60bae31886a6b72b81c97f4254857fc354c136`. These sections prove the private-source semisimplicity restriction and the effective affine-output search for a finite fixed commuting algebraic physical alphabet. They do not prove general original G3 recognition or undecidability. No correction is required.

## Source representation and no same-grade transitions

This is the CURRENT-FOREST transition representation. Apply the kernel for the current number of roots, route those roots according to the natural mode, and graft already completed subtrees opaquely. If the root count does not decrease, no merger occurred. Routing alone changes neither labels nor completed subtrees. Therefore the only transition within a root-count grade is the unchanged forest, with scalar probability b_j(K); the whole grade block is b_j(K)I.

The original full labelled forest/graft source and private append law are the accepted [admitted-tester proof](https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md), Git blob `b41fdf706e4dfcb5d14ffdbc88631012674ef1f4`. No hidden conditional register is added to this representation. A changing exposed register could invalidate the same-grade statement, which is why the reviewed source contract remains private natural chains.

This argument is distinct from the faithful LEFT-regular forest algebra, whose block index is entering-token arity. The current proof consistently uses the current-root-count representation and does not mix those two index conventions.

## Strict ordering and diagonalizability

Projective coupling of one extra current root gives b_(j+1)<=b_j on every remaining actual factor. For an independent cell, the old route choices can be held fixed and one new Bernoulli route added; the conditional extra no-merger factor is at most one. COMMON uses the same single arm choice. Ordinary factors have the same monotonicity.

Every reviewed strict word contains a positive ordinary population E(z). No-merger probabilities multiply under concatenation, and its consecutive ratio is z^j. Thus

    0<b_(j+1)(W)<=z^j b_j(W)<b_j(W),  j>=1.

In particular 1=b1>b2>...>bm>0. Scalar diagonal blocks on distinct grades can be separated by successive block-unitriangular elimination: each Sylvester equation divides by a nonzero b_j-b_k. The transformed matrix is the direct sum of these scalar blocks. Hence its minimal polynomial has no repeated factor, and the matrix is diagonalizable over the reals.

The empty-forest state is isolated. Its additional identity block can be grouped with the constant eigenvalue without introducing a same-eigenvalue nilpotent term. Restriction to an invariant subspace and passage to an invariant quotient preserve semisimplicity. A literal intertwining realization of a nontrivial Jordan block by one strict source letter is consequently impossible.

I also checked the relevant primary Bell construction. [Polynomially Ambiguous Probabilistic Automata on Restricted Languages, Section 3.1](https://drops.dagstuhl.de/storage/00lipics/lipics-vol132-icalp2019/LIPIcs.ICALP.2019.105/LIPIcs.ICALP.2019.105.pdf) explicitly starts from a repeated-eigenvalue matrix with a nonzero superdiagonal whose powers encode an integer, then uses related commuting counters with fixed row sums. Scalar stochastic normalization does not remove their Jordan structure. This confirms the claimed mismatch with a literal physical-letter realization. It is not a prohibition on every possible computational encoding.

## Fixed commuting alphabet and common projectors

Let K1,...,Ks be the finite fixed commuting alphabet in the manuscript, with effectively algebraic capped kernels and fixed effectively algebraic affine readouts/targets. Diagonalizing K1 by a block-unitriangular matrix preserves the scalar diagonal blocks of every other letter. Commutation with its distinct grade eigenvalues forces all transformed off-grade blocks of every other letter to vanish. Consequently all letters share the root-grade projectors P_j and act there by the scalars b_(j,i).

The projectors are effectively algebraic; they may also be computed by the usual polynomial spectral-projector formula from K1. Products therefore have the displayed expansion in monomials product_i b_(j,i)^n_i. The root-one eigenvalue is identically one, so any constant/target term in an affine equation can indeed be absorbed into its coefficient c1. This remains correct if some projector has zero readout.

## Effective dominance bound

The first nonzero algebraic coefficient c_j0 can be found by exact equality tests. After dividing by its positive monomial, all later grade ratios satisfy a fixed strict bound r<1, because both the alphabet and the number of grades are finite. Thus the absolute tail is at most C r^n, where n is total letter count.

Exact algebraic arithmetic can test C r^N<|c_j0| while increasing N, and this loop terminates by r<1. No logarithm equality oracle is needed. For all n>=N the leading term cannot be cancelled, so all possible equality solutions lie among finitely many shorter words. If a row has no later nonzero coefficient, it is impossible; if every coefficient of every row is zero, all permitted words satisfy the response equations. Empty-word and empty-alphabet conventions can be dealt with separately and do not affect the bound.

For a finite list of simultaneous equalities, one nonautomatic row supplies a bound sufficient to search them all. This establishes the precise finite fixed-alphabet decision claim. It does not bound or decide products from the entire continuously varying source family.

## Required scope and whole-attempt status

The fixed algebraic coefficients are essential. If a retained exterior tuple varies, the leading c_j can vanish or approach zero, so this bound is not automatically uniform over that tuple. Likewise arbitrary ordinary pads need not commute with an INDEPENDENT alphabet merely because the chosen letters commute with each other. Neither extension is claimed in the frozen manuscript. Nonlinear endpoint constraints can also destroy the one-common-leading-term argument; they are excluded there.

The zero-selector discussion in Section 4 correctly identifies its role as inherited moment-support/convex reasoning. This receipt does not promote it to a new nonlinear all-core alphabet-enforcement theorem. The original reverse implication excluding unencoded sources remains absent, so the attempted undecidability reduction is incomplete.

The accepted facts retire the literal commuting Jordan-counter realization and prove the narrowly stated fixed physical alphabet affine-output search. They neither settle the variable/noncommuting source class nor give an input-effective bound for original coupled G3. No G4 consequence, historical novelty, compiler result or source execution is claimed. Review consisted of hand reasoning, source reads and hash checks only.
