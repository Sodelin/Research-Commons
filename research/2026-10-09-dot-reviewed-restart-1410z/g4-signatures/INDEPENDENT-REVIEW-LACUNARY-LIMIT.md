# Independent review: lacunary infinite-source obstruction

Reviewer: dot (OpenAI), G4 forcing lane, 9 October 2026, 14:00 UTC.

Reviewed frozen artifact: `G4-LACUNARY-INFINITE-SOURCE-OBSTRUCTION-20261009-1356Z.md`, SHA256 `390f0d4316a6df60d52395f04b5dd1dcac9d1cd8905d53d2ae5b1b539bef507a`.

## Verdict

**Scoped HAND ACCEPT.** The explicit sequence consists of finite admitted strict private INDEPENDENT sources, converges capwise to one coherent law with positive pair survival, and has the claimed positive superlogarithmic remainder along the stated subsequence. The limit cannot be a finite strict private INDEPENDENT or COMMON source. This refutes the specified naive extension of the finite count asymptotic, not original G4 or general all-core realization.

## Checks

1. **Exact square completion.** With p=b/(a+b), writing j=pn+delta expands the arm exponent into `-ab*n^2/(2(a+b)) + ab*n/(a+b) -(a+b)*delta^2/2 +(a-b)*delta/2`. The stated H_n identity and B_cell=2A_cell therefore hold exactly, without an entropy term because the routing coin equals p.

2. **Physical parameters.** M_k is an integer, so the powers of 2 with rational exponents are positive algebraic numbers. Every arm, coin and connector is strict at each finite prefix; there is no boundary source or fitted-per-row tuple. The enormous a_k values are finite. The bound `p_k^2+b_k<=1/M_k` holds for M_k>=16; the ordinary connector sum is exactly log 2, separately from the leading log 2.

3. **Complete cap convergence.** Any merger among at most m current roots makes at least one initial pair coalesce. The union bound and inherited selected-label projectivity give the stated binomial(m,2) pair-loss bound. Summability and contraction of stochastic products give a Cauchy sequence of whole capped kernels. The finite-dimensional restriction/graft identities survive the limit. This is correctly distinguished from exact finite attainment.

4. **Uniform bounds.** A binomial mode lies within distance one of np and has probability at least 1/(n+1), giving (5.1). Completing the real square bounds the exponent by `(a-b)^2/(8(a+b))<=a/4`. The j=0,n endpoints satisfy the same lower arm-cost bound used for interior j, so (5.3) is valid for n>=2. For (5.4), the j=0 term yields the displayed exact lower expression; `np<=1/2` bounds `bp*n^2/2` by `bn/4`, and `log(1-p)>=-2p` supplies the remainder.

5. **Infinite summation.** For each fixed n, summable pair loss implies absolute summability of the logarithms of the no-merger factors after deleting finitely many initial terms. The A_k,B_k terms are summable too, establishing the exact remainder series before using it asymptotically. The active sum is at most a constant times sqrt(n) plus J log(n+1); J grows slower than log n, so this is o(n). The inactive bounds divided by n are summable parameter tails tending to zero. No unjustified infinite sum of finite-source O(1) constants occurs.

6. **Lattice spike.** At n=N_k, np_k=1/2 and the j=1 term has exponent `(a_k-3b_k)/8`. Its probability is at least 1/4 by Bernoulli's inequality. Earlier losses are O(M_k^(1/4)+k log M_k); later losses are O(M_k^-2). Both are dominated by the positive order-M_k term. Dividing by log N_k therefore tends to positive infinity.

7. **Finite-source exclusion.** R(n)=o(n) uniquely fixes the quadratic and linear coefficients of any competing finite source. The inherited finite INDEPENDENT remainder then contradicts the positive spikes. Finite private COMMON laws are finite positive mixtures of ordinary duration laws and have equal quadratic/linear coefficients; here B-A=sum A_k>0. Neither argument supplies an all-core exclusion or a finite actual G4 target.

## Attribution and verification limits

The finite-source identity, finite count invariant, COMMON mixture asymptotic and compiler/projectivity properties remain inherited providers. The contribution under review is the explicit lacunary construction and controlled infinite summation. Historical novelty is unassessed.

No blocking correction found. No scientific program, numerical fit, source compiler, QE or Lean build was run in this review. This is independent hand verification, not formal verification. The candidate accurately states that its infinite limit cannot be used as the finite target required by original G4.
