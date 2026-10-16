# Independent review: fixed-beta classical shell candidate 18

Date: 2026-10-16. Independent mathematical hand review by OpenAI assistant for Nolan. **Scoped PASS**, subject to the explicitly stated original coefficient-bounded Hamiltonian class. No independent execution, Lean verification, novelty or full P1 closure claim.

## Reviewed source and prior supplier

Reviewed `FIXED-BETA-CLASSICAL-SHELL-CANDIDATE-18.md` in full, SHA256 `e1c5598612b5c70ee7d4275b0b47f865dd9285d4ad41eff26d8469e3fb968915`.

The testing supplier is Chan–Diakonikolas–Gregory Valiant–Paul Valiant, [SODA2014 Theorem 1.1](https://www.cs.purdue.edu/homes/pvaliant/closeness.pdf). The reviewer previously directly inspected that primary theorem for import 15: equality versus separated two-unknown distributions on D symbols has the stated maximum of the D^(2/3)/epsilon^(4/3) and sqrt(D)/epsilon² lower bounds, up to universal constants. The present pass checks the new fixed-temperature encoding and sample-only transfer, rather than re-proving that prior testing theorem.

## 1. Fractional energy and clone leakage

The square and pair-energy terms are nonnegative for every fractional vector x in [0,1]^s. This is essential: rounding is used for the lower bound, not to replace the actual energy by a possibly negative logical approximation. The constant-block weight-two shell has exactly one configuration per pair and total unnormalized weight one.

The constant-block leakage estimate correctly bounds the two possible logical weights at distance a from two by 2s^(2+a), and uses a²>=a. The chosen lambda easily yields eta/4.

For each fixed rounded configuration, choosing q flipped physical positions determines the original configuration uniquely, so binom(sm,q) is a valid overcount even with deterministic tie-breaking. The inequality w_i(m-w_i)>=m min(w_i,m-w_i)/2 gives the total lock bound. Splitting it in halves yields

J_p >= mu m q/4 + min(lambda a²/4, mu m² a/8).

Both entries in the minimum are at least 4a log(2s) for a>=1. The subsequent sum over rounded logical weights is at most 2s². With u=sm exp(-mu m/4)<=1, exp(u)-1<=2u gives exactly the displayed bound 4s³m exp(-mu m/4)<=eta/4. Thus the complete clone leakage is at most eta/2, uniformly in the unknown p. No uncontrolled factor exponential in sm was dropped.

## 2. Coefficients and field reservoir

Expanding in Z=1-2y gives the stated lock pair coefficient -mu/2, square pair coefficient lambda/(2m²), and cross-block coefficient v_ij/(4m²). The locking term has no linear coefficient. The linear square coefficient -lambda(s-4)/(2m) and pair-energy field contribution -sum_l v_il/(4m) are correct. The stated m bound makes every logical pair coefficient at most 3beta/4 in magnitude. Hmax and S0 correctly dominate each field and the sum of absolute fields, respectively.

Replacing the field F(z) by F(z)sum_l a_l/R gives the desired conditional distribution when the reservoir is all plus. All new coefficients respect the beta bound. The global logical flip leaves K unchanged and reverses F, proving exactly Z_minus/Z_plus=exp(-2h0 R). This controls the unwanted pure phase without assuming a sign for any unknown field.

For l<=R/2, the pointwise energy cost relative to all plus is at least gamma lR-2lS0/R, which exceeds gamma lR/2 under R²>=8S0/gamma. For q=R-l<=R/2, the all-minus comparison subtracts an additional 2h0q; since 2h0=gamma and R>=8, the same gamma qR/2 bound still holds. Summing binomial multiplicities on both sides and allowing middle-layer double counting is valid. The stated constraints give non-plus weight below eta/4 relative to Z_plus, hence the corresponding TV bound. Adding clone leakage gives total TV below eta.

## 3. Physical overhead and testing transfer

All integer conditions are eventually satisfiable. For fixed beta and constant epsilon, lambda and V are O(log s); choosing m=C_beta log s for a sufficiently large constant satisfies the polynomial-exponential inequalities. Then S0=O(s² log s), Hmax=O_beta(s), and R=O_beta(s sqrt(log s)) is sufficient. Thus N=sm+R=O_beta(s log s), with every clone and reservoir spin counted. This implies the stated N^(4/3)/(log N)^(4/3) consequence along the constructed sequence. An all-N extension is not accepted without its additional explicit monotone size rule, as the candidate itself notes.

The null p=q remains exact. Smoothing leaves more than 3epsilon/2 full L1 separation; the two TV errors cost at most 4eta in L1 and preserve at least epsilon separation. The ideal encoding uses only source samples, known uniform randomness, deterministic copies of classical bits and fixed reservoir bits. It never queries p-values or unknown Gibbs parameters.

Because every constructed Gibbs state is diagonal, full basis samples can simulate arbitrary collective measurements with unrestricted computation. Adaptive source choices can be handled by sampling each requested source as needed, or by pre-sampling a hard-cap supply from each source, incurring only a constant factor in the total sample budget. The T eta transcript error and fixed-success amplification therefore justify the imported lower bound. This is a hard-total-budget statement, not an expected-stopping claim.

## Accepted scope and useful interpretation

The construction establishes the claimed fixed-beta lower bound for the original class bounding each Pauli coefficient. It uses growing interaction degree and potentially growing per-site interaction sums. Consequently it is not an import into a bounded-degree or bounded-local-energy class at fixed beta. This distinction matters when comparing temperature regimes and must be preserved in readable summaries.

The result does not close the general certification gap or distinguish optimal single-copy from collective complexity. Novelty of the locking/field-gadget composition remains unresolved and requires prior-work review before any priority statement. No mandatory mathematical correction was found.
