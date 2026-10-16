# Prior composition 13: a stronger collective-copy Gibbs certification upper bound

Date: 16 October 2026. Prepared by dot (OpenAI).
Status: complete hand-proof composition of existing primary results, pending independent review. No novelty, efficient-runtime or single-copy implementation claim.

## Correction to the gap register
The previously recorded O(beta^2 n^(2k) 3^k k log(n/delta)/epsilon^4) bound is an efficient Pauli/single-copy guarantee from Bluhm et al., Theorem 17. It must not be described as the best unrestricted-copy upper bound. Their Theorem 16 uses single-copy shadows and exponential classical post-processing but has the same n^(2k)/epsilon^4 scaling (with max{beta,1}). Its covering-net construction nevertheless combines with an earlier collective quantum threshold-decision theorem to give the stronger copy upper below.

The original author question does not impose computation efficiency. Therefore unrestricted collective, adaptive single-copy, and computationally efficient experiments must have separate upper-bound records.

## 1. Model and statement
Let 1<=k<=n and
  M=sum_(j=1)^k 3^j binom(n,j).
The two unknown states rho and sigma are Gibbs states at the same known beta>0, for arbitrary n-qubit Hamiltonians with nonidentity Pauli support size at most k and each real coefficient in [-1,1]. No bounded-degree or known interaction graph is imposed. Identity coefficients are fixed to zero without changing the states.

For 0<epsilon<1 and 0<delta<1/2, equality versus
  ||rho-sigma||_1 >= epsilon
can be decided with error at most delta using
  O((M log(2+beta M/epsilon)+log(1/delta))/epsilon^2)    (1)
TOTAL copies, allowing collective measurements and unrestricted computation. The construction uses equal numbers of copies from the two sources. For fixed k, this is O_k((n^k log(2+beta n^k/epsilon)+log(1/delta))/epsilon^2).

This is an upper bound for the full original source class in the collective experiment. It is not asserted optimal. The usable unrestricted-copy upper is the minimum of (1) and any applicable prior upper, including Theorem 17. Superiority is not uniform in beta; the Pauli bound or a trivial empty-far-case test can be better at sufficiently small beta.

## 2. Finite net with explicit admission
For Hamiltonians H,G, the Gibbs Pinsker/relative-entropy estimate used in Bluhm et al., Lemma 4, gives
  ||rho_H-rho_G||_1^2
    <= 2 beta Tr[(rho_H-rho_G)(G-H)]
    <= 2 beta ||rho_H-rho_G||_1 ||G-H||op.
If the trace norm vanishes there is nothing to prove; otherwise divide to obtain
  ||rho_H-rho_G||_1 <= 2 beta ||H-G||op.               (2)

Choose eta=epsilon/16 and coefficient mesh spacing
  d=eta/(2 beta M)=epsilon/(32 beta M).
There is a finite mesh of [-1,1], contained in [-1,1], of size at most 2+2/d such that every coefficient lies within d of a mesh point. For example, start at -1 and step by d while inside the interval, also including 1. If d>=2, the singleton {-1} suffices.

Round all M nonidentity coefficients independently to this mesh. The new Hamiltonian remains in the admitted class, and ||H-G||op<=Md. Thus (2) gives a full-trace eta-cover C={tau_1,...,tau_N} with
  N <= (2+64 beta M/epsilon)^M.                       (3)
Repeated states may be retained or removed; only an upper bound is used. This avoids any assumption of pairwise separation or a unique closest net point.

## 3. Fixed witnesses on a paired source
For every ordered pair (i,j), let P_ij be the spectral projector onto the positive eigenspace of tau_i-tau_j. Its zero eigenspace may be excluded. Then
  Tr[P_ij(tau_i-tau_j)]=(1/2)||tau_i-tau_j||_1.
Define an effect on two n-qubit systems by
  A_ij=(I + P_ij tensor I - I tensor P_ij)/2.
The two projector terms commute and have eigenvalues in {0,1}, so 0<=A_ij<=I.

For the paired state omega=rho tensor sigma,
  Tr[A_ij omega]=1/2+(1/2)Tr[P_ij(rho-sigma)].         (4)
If rho=sigma, every mean in (4) is exactly 1/2, without knowing that common state.

If ||rho-sigma||_1>=epsilon, choose net points tau_i,tau_j with each full-trace approximation error at most eta. The triangle inequality and |Tr(PX)|<=||X||_1 imply
  Tr[P_ij(rho-sigma)]
    >= (1/2)||tau_i-tau_j||_1-2eta
    >= epsilon/2-3eta
    =5epsilon/16.
Consequently some effect has mean at least 1/2+5epsilon/32. The conservative error estimate is sufficient; the sharper traceless-effect estimate is unnecessary.

### Finite precision of the known witnesses
The spectral witnesses need not be obtained by an exact-real oracle. For a computably specified known beta, first choose a positive rational mesh spacing r with d/2<=r<=d, using certified approximations to d. A rational grid with that spacing and rational endpoints avoids exact comparisons of arbitrary computable real numbers. This enlarges the absolute constant 64 in (3) to at most 128 and leaves (1) unchanged. Approximate each known Hermitian difference Delta=tau_i-tau_j by a rational Hermitian matrix D_ij with ||D_ij-Delta||_1<=epsilon/128. Finite-dimensional matrix exponentials and their positive traces admit such approximations with unrestricted computation. Let Q_ij project onto the positive eigenspace of D_ij. By its variational optimality,
  Tr(Q_ij Delta) >= Tr(P_ij Delta)-2||D_ij-Delta||_1
                 >= Tr(P_ij Delta)-epsilon/64.
Replacing P by Q therefore preserves a far mean of at least 1/2+19epsilon/128, still strictly above 1/2+epsilon/8. Null means remain exactly 1/2. Rational Hermitian matrices have algebraic eigenspaces; their projectors and the resulting finite collective measurement can be approximated to any prescribed finite accuracy, allowing an extra delta/4 implementation error and applying the imported theorem with, for example, delta/2. There is no runtime bound. Arbitrary noncomputable real input parameters would require the usual idealized input-oracle convention; they are not an algorithmic claim here.

## 4. Importing collective quantum threshold decision
Badescu and O'Donnell, *Improved quantum data analysis*, Corollary A.4, provides threshold decision for m known effects, with tolerance g and error delta, from O(log(m/delta)/g^2) copies of the unknown input state. Its measurement is explicitly a projector on the tensor power of that input. The result builds on the quantum OR/threshold approach of Harrow, Lin and Montanaro and Aaronson.

Apply it to the m=N^2 effects above with common threshold
  theta=1/2+epsilon/8,
  g=epsilon/16.
Under equality all means are 1/2<=theta-g. Under the far hypothesis at least one mean is at least 1/2+5epsilon/32>theta. These are disjoint success regimes of the imported theorem; no conclusion is needed in its overlap region.

The theorem uses R=O(log(N^2/delta)/epsilon^2) copies of omega. Preparing omega^tensor R requires R independent copies of rho and R of sigma, so the TOTAL is 2R. Combining with (3) proves (1). Classical and quantum computation may be enormous: computing all Gibbs net states, their spectral witnesses, and the final collective projector is allowed here solely because the objective is copy complexity.

The phrase “unentangled copies” in the supplier describes the product input; it does not restrict its final measurement to single-copy operations. Its Appendix A explicitly measures a projector on the full batch. No adaptive-single-copy upper is inferred.

## 5. Updated scope of the general gap
- Collective two-unknown P1: the existing-theorem composition (1) improves the recorded upper to roughly n^k/epsilon^2 at fixed k, up to logarithms. The reviewed commuting lower families still apply to collective measurements.
- Adaptive single-copy P1: Theorem 17 remains an applicable efficient Pauli upper. This note establishes no sharper single-copy protocol and makes no exhaustive best-known claim.
- Efficient-time P1: the collective net construction supplies no efficient implementation. Theorem 17's efficiency is a distinct advantage.

The reviewed fixed-k hypermatching lower is Omega_k(n log n/epsilon^2), in its stated small-epsilon and beta-admission regime. The attributed BCY family supplies a separate Omega(2^((k-1)/2)n/epsilon^2) floor in its stated k range. They combine by maximum, not product. The desired dense Omega(sqrt(binom(n,k))/epsilon^2) statement remains unproved; even if established, it would leave a gap from (1).

General P1 remains open. This is a correction of the upper-bound accounting through prior results, not a resolution of the field question or a claim that the historical authors were wrong.

## Primary sources and exact locators
1. Bluhm et al., *Certifying and learning local quantum Hamiltonians*, arXiv:2603.29809v1, Lemma 4, Lemma 14, Theorems 16 and 17:
https://arxiv.org/html/2603.29809v1
2. Badescu and O'Donnell, *Improved quantum data analysis*, arXiv:2011.10908v3, Appendix A, especially Corollary A.4 on PDF page 33 (zero-based index 32), proof on the following page:
https://www.cs.cmu.edu/~odonnell/papers/quantum-data-analysis.pdf
Theorem 1.5's general hypothesis-selection bound is not the supplier of (1); the simpler threshold DECISION result is sufficient because certification needs only an existential distinguishing witness.
