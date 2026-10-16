# A noncommuting k-block lower-bound reduction
Date: 2026-10-16. Prepared by dot for Nolan.
Status: complete source-level hand reduction using an established adaptive-measurement lower bound. No new lower-bound technique or novelty claim; no Lean formalization or execution.

This supplements [Checkpoint 01](https://github.com/Sodelin/Research-Commons/blob/ec136c4e6056e9901a67db082eb1d4e5349d85d7/research/2026-10-16-g6-gibbs-certification/SCOPED-LOWER-BOUND-CHECKPOINT-01.md). Its exact two-unknown-state, common-beta, bounded-Pauli-coefficient model and TOTAL-copy convention are retained.

## Imported primary theorem
[Chen, Huang, Li and Liu, Tight Bounds for Quantum State Certification with Incoherent Measurements, arXiv:2204.07155v2](https://arxiv.org/html/2204.07155v2), Lemma 6.2 and Theorem 6.3, supply the following hard family. For sufficiently large dimension d and 0<eta<=1/12, distinguish I/d from (I+eta M)/d, with M drawn from their conditioned traceless GOE ensemble. On its support ||M||op<=3 and ||M||1>=d/12. Any adaptive single-copy measurement procedure with success at least 2/3 requires Omega(d^(3/2)/eta^2) copies. The randomness is a single unknown state choice, fixed across copies. We import this theorem and its specified ensemble, not a new Gaussian calculation.

## Exact Gibbs admission
Take k<=n, d=2^k sufficiently large, 0<epsilon<=1/144, eta=12 epsilon, and
  beta >= atanh(36 epsilon).
Every supported M is traceless, and I+eta M has spectrum in [1-3eta,1+3eta], contained in [3/4,5/4]. Hence
  rho_M=(I+eta M)/d
is a full-rank state, and
  ||rho_M-I/d||1 = eta ||M||1/d >= epsilon.

Set L=log(I+eta M) and define the identity-gauge-fixed block Hamiltonian
  H_M = -(L - Tr(L) I/d)/beta.
Its Gibbs state is exactly rho_M: subtracting a scalar multiple of the identity changes only the partition function.

All nonidentity Pauli strings on this block have weight at most k. For such a string P,
  h_P = -Tr(P L)/(beta d).
Let c be the midpoint of the interval [log(1-3eta),log(1+3eta)]. Since Tr(P)=0,
  |h_P| = |Tr(P(L-cI))|/(beta d)
        <= ||L-cI||op/beta
        <= atanh(3eta)/beta
        <= 1.
The trace inequality follows from ||P||1=d. The midpoint is used only to bound nonidentity coefficients; the actual Hamiltonian above has exactly zero identity coefficient. No locality-preservation claim is being made for logarithms on more than k qubits: the entire unknown matrix is confined to one k-qubit block.

Embed H_M on the first k of n qubits, with no other terms. The full Gibbs state is
  rho_M tensor I_(2^(n-k))/2^(n-k).
All original coefficient constraints hold. The uniform null is H=0 at the same beta. The two-unknown problem includes the subclass with the second state fixed uniformly mixed.

## Exact preservation of the single-copy access model
A POVM E_y on the full n-qubit copy, with the spectator state tau fixed, induces the block POVM
  F_y = Tr_spectator[(I tensor tau^(1/2)) E_y (I tensor tau^(1/2))].
Each F_y is positive, sum_y F_y=I, and
  Tr[E_y(rho_M tensor tau)] = Tr[F_y rho_M].
This remains true conditional on any classical history, so arbitrary adaptive choices on individual full copies are simulated by adaptive single-copy measurements on the block. Known uniform second-source samples can also be simulated, including adaptive source selection. In a TOTAL-budget-N protocol at most N copies of the unknown block are used. Thus the imported lower bound applies without extra quantum memory or a stronger measurement oracle.

The family is not simultaneously diagonal in one fixed known basis; the proof here relies on the imported adaptive quantum lower bound, unlike Checkpoint 01's classical matching reduction. We do NOT extend its d^(3/2) lower bound to collective measurements.

## Consequence and exact remaining gap
In the stated epsilon,beta regime and for sufficiently large 2^k, the original single-copy task requires
  Omega(2^(3k/2)/epsilon^2)
TOTAL copies. For k>=2, combining independent lower-bound subclasses with the matching prior in Checkpoint 01 yields
  Omega(max{n,2^(3k/2)}/epsilon^2)
whenever BOTH sets of admission conditions hold. No product of the two factors follows.

This supplies a noncommuting, coefficient-admitted obstruction sensitive to the measurement class and to k. At fixed k, it does not improve the matching family's linear n floor. The main open dependency is still the joint n,k,beta dependence for fixed-k noncommuting interactions, rather than a proof for an unrestricted d-dimensional state class. In particular, placing independent hard blocks does not by itself multiply their lower bounds: a single n-qubit copy contains every block, and the allowed within-copy POVM may couple them.

The fresh paper [Hung and Tsai, Efficient Quantum State Identity Testing, arXiv:2610.04597v1](https://arxiv.org/html/2610.04597v1) does not close this gap: its task concerns a collection of pure states with a near-identical versus low-overlap promise, and permits collective procedures. Its logarithmic collection-size bound is not a bound for two unknown mixed Gibbs states in our access model.
