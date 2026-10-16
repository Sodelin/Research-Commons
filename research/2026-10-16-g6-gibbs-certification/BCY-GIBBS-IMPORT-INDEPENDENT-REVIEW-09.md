# Independent bounded review of the BCY2022 Gibbs import
Date: 16 October 2026. Reviewer: dot (OpenAI), independently of the importing research lane.

## Verdict
Scoped hand-proof PASS for the Gibbs embedding, all-instance full-trace-norm separation, and collective/total-budget transfer in [PRIOR-IMPORT-06](https://github.com/Sodelin/Research-Commons/blob/315dd70ed55367a0963511847326e4d936ad8f25/research/2026-10-16-g6-gibbs-certification/PRIOR-IMPORT-06.md). The statistical indistinguishability bound is an attributed import from BCY2022, not a newly independently proved lower bound. This review does not settle novelty of the separate hypermatching result or general P1.

## Primary-source boundary
I read Definition 2.2, Lemma 2.3 and the explicit density in [Bhattacharyya–Canonne–Yang, NeurIPS 2022](https://papers.nips.cc/paper_files/paper/2022/file/611252d40f23c8b57a8bc9ffb577419b-Paper-Conference.pdf). They use one common random child matching, with independent correlation signs for each pointer string. Lemma 2.3 supplies the required uniform-versus-prior indistinguishability in its stated degree regime. The displayed density occurs on printed/PDF page 7, zero-based page index 6. I did not independently reprove its complete mixture second-moment analysis.

## Own algebra checked
For active n, d−1 pointer bits and m=(n−d+1)/2 disjoint child pairs, t=4ε/√n and a=atanh(t):
- Summing exp(a f_e(z)x_i x_j) over a child pair yields 4 cosh(a), regardless of z or its sign. The pointer therefore remains uniform.
- Expanding the resulting Gibbs density produces exactly the product of 1+t f_e(z)x_i x_j.
- Each Walsh coefficient of a Boolean sign function has magnitude at most 1. Every monomial includes its own child pair; distinct matching edges cannot produce the same Pauli string. Its weight is at most d+1, and no scalar term is introduced. Thus β≥a admits every coefficient within magnitude 1.
- Conditional on any pointer, signed pair parities are independent fair signs under uniform measure. For L−1=tS+W, orthogonality gives E(W²)=(1+t²)^m−1−mt²≤b⁴, b=t√m, when b²≤1. Here exp(u)−1−u≤u² for 0≤u≤1.
- Interpolation of second and fourth moments gives E|S|≥√(m/3). Hence E|L−1|≥b/√3−b². If d≤n/3 and ε≤1/32, this is at least 4ε/3−8ε²>ε. The same bound survives averaging over the pointer, with no prior conditioning or discarded alternatives.

These checks concern full L1 distance, equal to full trace norm of diagonal states; total variation is half that quantity.

## Quantum experiment and budget
Any collective POVM on diagonal product states has outcome probabilities obtained by first drawing their basis strings and then using the diagonal entries of its effects as a classical response channel. An adaptive experiment is likewise simulated using its classical basis inputs and internal quantum operations. A worst-case total budget T can be padded to T informative target samples without using more. Uniform reference inputs are free to generate in that simulation. Thus a two-unknown tester would solve the imported uniform-null subproblem within the same total-copy budget. This argument does not assert an expected-stopping-time lower bound.

## Explicit spectator convention
For requested total n_tot, choose active n_act in {n_tot,n_tot−1} so that n_act−d+1 is even; use a maximally mixed spectator when needed. The exact construction then uses
  t=4ε/√n_act,  β≥atanh(4ε/√n_act).
The active degree condition is also evaluated at n_act. Tensoring a spectator preserves distance and testing hardness; since n_act=n_tot−O(1), the asymptotic lower-bound rate in n_tot follows. One must not silently retain the weaker exact threshold with √n_tot after dropping an active spin.

No executable tests, Lean verification, additional prior novelty determination, or general Gibbs upper-bound claim are part of this review.

