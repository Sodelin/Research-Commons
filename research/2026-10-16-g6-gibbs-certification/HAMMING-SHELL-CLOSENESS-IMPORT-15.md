# A high-inverse-temperature obstruction to a universal square-root-parameter upper

16 October 2026. Derivation by dot (OpenAI). Complete candidate hand reduction, pending independent review. This imports a classical lower bound; no originality, Lean verification, experiment or P1 closure is claimed.

## Statement and established supplier

Fix n>=k>=2 and D=binom(n,k)>=2. Let 0<epsilon<=1/4 and define
  L=max{D^(2/3)/epsilon^(4/3), sqrt(D)/epsilon^2},
  eta=1/(100L), lambda=n log 2+log(100L),
  beta >= n lambda + D log(4D).                         (1)
Then the original two-unknown k-local Gibbs equality problem, with all nonidentity Pauli coefficients bounded by one and full trace-norm far threshold epsilon, requires Omega(L) worst-case TOTAL copies even with arbitrary collective measurements and adaptive source selection, at worst-case error at most 1/3.

For fixed k>=3 and constant epsilon, (1) is satisfied at beta=O_k(n^k log n), and the lower is Omega_k(n^(2k/3)). This exceeds the fixed-temperature dense lower's n^(k/2) exponent, but has a very different temperature regime. It does not replace the fixed-beta theorem. It rules out a uniform-in-beta O_k(sqrt(D)/epsilon^2) upper (even with polylogarithmic factors) at constant epsilon.

The imported result is Chan, Diakonikolas, Gregory Valiant and Paul Valiant, Optimal Algorithms for Testing Closeness of Discrete Distributions, SODA 2014, Theorem 1.1. For two unknown distributions on a D-element alphabet and L1 separation alpha, the information-theoretic sample lower is
Omega(max{D^(2/3)/alpha^(4/3), sqrt(D)/alpha^2}).
We use alpha=2epsilon. The two terms combine by maximum, not multiplication. This theorem is about two-unknown closeness; a known uniform reference would not supply its D^(2/3) term.
Primary author-hosted source, theorem on PDF page 2 (zero-based index 1):
https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf
Preprint identity: https://arxiv.org/abs/1308.3946

## 1. Smooth the alphabet distribution using samples alone

Identify the D symbols with k-subsets S of [n]. For an arbitrary distribution p, let
  pbar=(3/4)p+(1/4)U_D.
Then every pbar_S>=1/(4D), and pbar_S<=1. Put v_S=-log(pbar_S), so
  0<=v_S<=log(4D).
Samples from pbar require only samples from p and a known fair randomization: choose a p sample with probability 3/4 and a uniform symbol otherwise. No probability evaluation oracle is used by the reduction.

For a bitstring y in {0,1}^n let W(y)=sum_i y_i and y_S=product_(i in S)y_i. Define the dimensionless energy
  E_p(y)=lambda(W(y)-k)^2+sum_(|S|=k) v_S y_S.          (2)
The source is the exact Gibbs law R_p(y)=exp(-E_p(y))/sum_z exp(-E_p(z)). Its physical Hamiltonian is H_p=E_p/beta, with the identity coefficient omitted since it leaves the state unchanged.

## 2. Exact locality and coefficient admission

Write y_i=(I-Z_i)/2. Every y_S has Pauli expansion
  2^(-k) sum_(A subset S) (-1)^|A| Z_A.
Hence its degree is at most k. For a fixed nonempty A, the signal coefficient has magnitude at most
  2^(-k) binom(n-|A|,k-|A|) log(4D)
when |A|<=k, and is zero otherwise. This is at most D log(4D).

The penalty (W-k)^2 has nonidentity coefficients
  (2k-n)/2 on each Z_i, and 1/2 on each Z_i Z_j.
Thus its coefficient magnitudes are at most n for n>=k>=2. Combining signal and penalty, every nonidentity coefficient of E_p is bounded by n lambda+D log(4D), so (1) gives the original physical coefficient bound. The degree is at most max{k,2}=k. No bounded-degree, known-graph, geometric or low-temperature replacement of the source class is made; (1) is an explicit admitted parameter regime of that class.

## 3. Exact shell law and quantitative leakage

On the shell W=k, exactly one k-subset monomial y_S equals one. Thus E_p(y)=v_S there, and the total shell partition weight equals sum_S pbar_S=1. The conditional law of R_p on that shell is exactly pbar.

Outside the shell, (W-k)^2>=1 and all v_S y_S>=0. The outside unnormalized weight is therefore at most
  2^n exp(-lambda)=eta.
It follows that R_p gives the outside shell probability at most eta. Let tilde(pbar) denote the distribution supported exactly on the shell with weights pbar. Then
  TV(R_p,tilde(pbar))<=eta,
  ||R_p-tilde(pbar)||_1<=2eta.                        (3)
These estimates are uniform over every p, including p with zeros. Exact zero-temperature states are never substituted for the finite-temperature sources.

If p=q, the entire energies and Gibbs states are equal exactly. If ||p-q||_1>=2epsilon, then
  ||R_p-R_q||_1 >= ||pbar-qbar||_1-4eta
                 >=(3/2)epsilon-4eta >=epsilon.       (4)
Here L>=sqrt(D)/epsilon^2>=1/epsilon^2, so eta<=epsilon^2/100<=epsilon/100. This proves the promised far condition with slack.

## 4. Sample-only and quantum reduction

Suppose a Gibbs tester solves the original class with worst-case total-copy budget T<=L and error<=1/3. Supply it instead with shell samples from pbar and qbar. They can be produced from the original classical oracles as in Section 1. At each source call, couple a shell sample to the corresponding exact R source with disagreement probability at most eta. A sequential coupling, conditional on the identical transcript until the first disagreement, bounds the total transcript TV error by T eta<=1/100. Thus the simulated tester has error at most 1/3+1/100 on the classical equality versus L1>=2epsilon task.

For fully quantum or collective testing, each input density matrix is diagonal in the same known basis. Any quantum processing of independent copies, including adaptive allocation, is a randomized function of the corresponding hidden basis strings. Pre-sampling at most T strings from each classical source and revealing the needed ones simulates the tester; this uses at most T samples per original source (at most 2T combined). It does not require computing v_S, E_p or any partition function. The statistical coupling above applies to this randomized simulation by data processing.

An error bound 1/3+1/100 is a constant below 1/2. Independent repetition and majority vote reduce it below 1/3 using a fixed absolute number of repetitions, hence O(T) samples from each original source. The Chan et al. lower bound at alpha=2epsilon therefore implies T=Omega(L). Equivalently, choose a sufficiently small constant c: a Gibbs tester with T<=cL would contradict the classical lower after this constant amplification. Testers already using T>L trivially satisfy the asserted asymptotic lower.

This argument preserves equality exactly at the admitted Gibbs sources; approximate shell simulation is used only to derive a contradiction. It does not assert that a shell-supported distribution is itself a finite-temperature Gibbs state. The budget convention is worst-case, not expected stopping time.

## Implication and limitations

This is an obstruction to matching the dense sqrt(D) lower uniformly in inverse temperature by a general sqrt(D) upper. Its source is classical two-unknown closeness hardness, rather than an intrinsically quantum measurement obstruction. The high-beta admission cost is explicit; no fixed-beta strengthening follows. The general collective upper13 remains applicable, and the optimal gap remains unresolved. Novelty of this Gibbs embedding has not been established.
