# Bounded certified-forward code review and control gate

Reviewer: dot (OpenAI), 5 October 2026, 10:46 UTC.

Exact admitted source: certified_forward.py SHA256 **c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace**.
Verifier: **04d1d1929b8a385f16ed1916f63b1bb1743c10f6969201da708f0af5dd14f211**.
Contract: **42bae7bfd75627ebb76a7879b01605bb1ed4f78acc25f4ae65fa24ca414bdd8a**.
Unit tests: **5d57db79b1df9bf1a29f07f05d15dd35b6ac0f5f2584c7aac63e4088c3c15ba3**.

The complete source, verifier and contract were read. All eight unit tests were independently rerun under a 512MiB /60-second bound and passed. No full 330-output fixture result is asserted by this pre-execution review.

## Arithmetic and formula review

The public evaluate/report entry points enforce the exact nine-key source contract, strict time ordering, positive rates and interior inheritance. Float/bool source values are rejected. Raw rational text is capped at 160 characters before parsing; reduced numerator/denominator encodings are capped at 256 bits. The low-level expression helper presupposes an already validated source, as in both public entry points and controls.

Interval arithmetic is exact Fraction endpoint arithmetic. Products are sign-aware, reciprocal division is by a nonzero exact scalar, and dyadic floor/ceiling round outward. Unit-range intersection is justified by the known probability/Laplace range and raises on a contradictory interval. Frozen interval objects and typed cache keys preserve the primitive's input contract.

For exp(−x), the large-argument interval [0,2^(−B)] is valid when x>=B because e>2. Otherwise halving gives u<=1, where odd/even alternating Taylor partial sums bracket exp(−u). Rounding contributes at most two grid widths. After m squarings, the displayed width recurrence gives (5*2^m−2)*2^(−(B+m+4))<2^(−B). Nonnegative interval squaring and range clipping preserve containment. The runtime width check remains a useful fail-closed guard. No ordinary floating exponential is used for certification.

The grouped H/S/R formulas match the accepted six pair densities, including one C interval across t1 and the BB split-route root term. The verifier independently keeps the C density split at t1 and compares exact exponential-polynomial dictionaries, with no floating equality threshold. Both mean and Laplace interval widths are now checked before evaluate returns, matching the report's output-width field. The bounded precision/term guards refuse rather than make an unmet width claim.

## Exact bounded validation admitted

Admit only the two declared synthetic parameter fixtures in verify_controls.py, one with rates 1,2,3,4,5 and one with all rates 2, both at h=1/16,t1=1/8,t0=3/16,g=1/3. Produce all 330 mean intervals at 64-bit width with associated Laplace intervals, exact density-expression comparisons, equal-rate reductions and fixture monotonicity checks.

Use the proposed 512MiB memory cap, 240-second outer wall limit and 180-second internal budget. Preserve stdout, stderr and terminal status in fresh non-overwriting files; bind the exact source/verifier hashes before and after. Any failure or incomplete output remains a failed/unadmitted control, not a partial precision success. No engine simulation, biological input, fitting, inverse-domain search, installation or new inference is part of this gate.

This bounded module is not the unrestricted-precision oracle in the abstract inverse theorem: source encoding and requested 16–128 output-bit limits are material implementation limits. It is not a generic data admission or estimator. The feature means are not a simplex, observations require the exact phased source/channel contract, and no BPP convergence, statistical confidence or empirical reliability conclusion is obtained from these arithmetic controls.
