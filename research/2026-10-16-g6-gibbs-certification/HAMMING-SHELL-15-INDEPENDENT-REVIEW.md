# Independent review: Hamming-shell closeness import 15

16 October 2026. Independent hand review by dot (OpenAI).
Verdict: scoped mathematical PASS. No blocking defect found. This accepts an attributed reduction of the classical two-unknown closeness lower bound, with the stated high-inverse-temperature admission. It is not a new classical lower bound, a fixed-beta improvement, a novelty conclusion, numerical validation or Lean verification.

## Source identity and supplier
Reviewed HAMMING-SHELL-CLOSENESS-IMPORT-15.md, SHA256 ebc2af4bffa0ccf5b7beec33f6413f9f68db45c3567bf21b5fd9c6d6265205f3, in full.

I independently opened the primary author-hosted Chan–Diakonikolas–Valiant–Valiant paper and read Theorem 1.1 on PDF page 2 (index 1):
https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf
It states the information-theoretic two-unknown L1 closeness rate max{D^(2/3)/alpha^(4/3),sqrt(D)/alpha^2}. The surrounding text explains the maximum of the two regimes. Taking alpha=2epsilon changes only absolute constants. The source is used for this established sample lower bound; the Gibbs embedding is checked separately below.

## Exact energy and coefficient check
With y_i=(I-Z_i)/2, the k-subset monomial expansion has coefficient 2^(-k)(-1)^|A| for every A subset S. Summing over S containing a fixed nonempty A gives the candidate's binomial count. The loose D log(4D) upper bound is valid.

Expanding W=(n-sum_i Z_i)/2 gives single-Z coefficients (2k-n)/2 and pair-Z coefficients 1/2 in (W-k)^2. All nonidentity coefficients of the combined energy are bounded by n lambda+D log(4D). Dividing by the stated common beta therefore admits every source in the original coefficient-bounded, at-most-k-local class. The discarded identity coefficient does not change the state. Positivity of the smoothed probabilities makes every energy finite, including for input distributions with zero coordinates.

## Shell law, leakage and promises
On Hamming weight k exactly one k-subset monomial is one, so the shell partition weight is exactly sum_S pbar_S=1. Outside it the integer squared penalty is at least one and every signal contribution is nonnegative. Thus outside partition mass is at most 2^n exp(-lambda)=eta, and the exact finite-temperature state is within TV eta of the shell law. This is a finite-temperature bound, not a zero-temperature replacement.

Equality is exact at the admitted sources whenever p=q. For far inputs, smoothing preserves three quarters of L1 distance; triangle inequalities lose at most 4eta. Since eta<=epsilon^2/100 and epsilon<=1/4, the displayed lower bound exceeds epsilon with slack.

## Sample-only reduction and budgets
The reduction generates pbar from samples by known randomization and never evaluates p_S or the Hamiltonian coefficients. Their definitions establish existence of admitted source states; they need not be computed to simulate the approximate input.

At each adaptive source call, an exact source sample and its shell approximation admit a coupling with mismatch at most eta. Up to the first mismatch their transcripts, hence adaptive decisions, coincide. The worst-case T-call transcript discrepancy is therefore at most T eta. For T<=L this is at most 1/100.

All exact and approximate states are diagonal in a common known basis. Quantum processing, including collective measurements and adaptive allocation, can therefore be simulated as stochastic processing of the underlying basis strings. Pre-sampling T strings from each source uses at most 2T classical samples and handles arbitrary allocation. This constant factor is harmless. No efficient classical simulation is claimed or required for an information-theoretic lower bound.

The simulated error is at most 1/3+1/100. A fixed number of independent repetitions reduces it below 1/3, using O(T) samples; the source lower bound then implies T=Omega(L). The argument for T>L is immediate. The convention is a worst-case budget throughout, not an expected stopping-time budget.

## Scope of the consequence
For fixed k>=3 and constant epsilon, n lambda is O(n^2+n log n), while D log(4D) is O_k(n^k log n). Thus the stated sufficient beta scale is correct. At this explicitly growing beta, D^(2/3) exceeds sqrt(D) by a polynomial factor, so a beta-uniform square-root-D upper with only polylogarithmic overhead cannot hold at constant epsilon.

This does not strengthen the fixed-positive-beta dense theorem and does not identify the optimal original-class sample complexity. The temperature dependence is essential and must remain visible in any summary.

