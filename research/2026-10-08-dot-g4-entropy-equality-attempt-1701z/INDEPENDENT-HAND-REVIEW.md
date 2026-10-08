# Independent hand review of the A8 entropy whole-proof attempt

Reviewer: dot, independent G4 B lane. 8 October 2026.

**Verdict: scoped HAND ACCEPT.** The frozen argument identifies a valid failure of the proposed entropy-to-endpoint transfer. It does not resolve original G4. No blocking mathematical correction was found.

## Exact objects reviewed

- Proof: `ENTROPY-EQUALITY-WHOLE-ATTEMPT-CANDIDATE.md`, SHA-256 `20288d8fdf0e903cb8d517da5663f269d01609a4af3d01655fe8272ea0b3d36b`.
- Source ledger: `SOURCE-PINS.json`, SHA-256 `ae13af825e94c32f1c1dac8e4fb12d8249550ebc4d1657ba1c50f24091ac9303`.

The full frozen proof and ledger were read. The review uses hand calculations and the inherited immutable source results identified there. The standard information identities were checked directly in Polyanskiy and Wu's author-hosted 16 August 2024 draft, Theorems 2.15 and 2.17 (printed pages 32 and 35), and Section 3.5: <https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf>. No stationary entropy-rate theorem is needed for the absorbing source process. No compiler or scientific execution is part of this review.

## Checks

1. **Conditional divergence is the missing equality premise.** The chain rule (2.1) and the unique unrestricted minimum-divergence lift follow by conditioning on the finite endpoint. Endpoint equality alone leaves the conditional-history term unconstrained. Physical membership in an endpoint fibre does not imply optimization of this auxiliary functional.

2. **The actual and reference laws share a legitimate marked history space.** Actual routes are drawn on current roots, with existing subtrees opaque. The ordinary reference draws the same marks and ignores them for coalescence. Retaining initial marks through a merger and drawing fresh marks at the next cell makes the comparison consistent. Only forward absolute continuity is asserted; it holds because every positive actual jump type has a positive reference rate. At fixed cap and finite strict word, the finite marked jump structure and bounded time intervals give finite forward divergence.

3. **The censored-exponential coefficient is exact.** Integrating the merger density and the survival atom gives

       D(Exp(r) censored at 1 || Exp(h) censored at 1)
         = (1-exp(-r)) [log(r/h)-1+h/r].

   The no-merger point mass contributes h. Weighting by the actual probabilities g^2, (1-g)^2 and 2g(1-g) gives (3.1), including its strictly positive mixed-arm term.

4. **The all-word chain rule has the correct survival weight.** Before cell i, the two selected roots remain distinct with probability p_i. Conditional fresh-route laws agree, ordinary segments contribute zero, and the one-root state contributes zero. This yields exactly the sum in (3.2). Sampling consistency gives the claimed lower bound for full-cap marked-history divergence. Importantly, the marked reference Q_history^W is defined using the rival's segmentation and pair calibration. It is an auxiliary comparison law with ordinary unmarked endpoint, rather than one canonical observable history law determined by the target alone. The proof respects this distinction.

5. **The cap-five use is faithful reuse.** The accepted fixed-target nonempty eight-cell full-five return makes all displayed endpoint divergences zero while (3.2) is positive. It disproves automatic saturation of data processing at those caps. It supplies no arbitrary-cap return and does not exclude a larger target-specific forcing cap.

6. **The weak-cell family is actual and target-fixed.** For sufficiently small positive delta, both pads in (5.1) are strictly positive and pair survival is exactly exp(-T). The first derivative of the full forest cell is G_m/2 because each pair of current roots shares an arm with probability 1/2. It cancels the derivative of the pair-calibrating ordinary pad. Analyticity of the finite coloured forest construction then gives the stated O(delta^2) full-matrix bound. Strict positivity of every fresh-root ordinary forest coordinate justifies the chi-square upper bound and O(delta^4) endpoint relative entropy. The same claim for a fixed once-used private exterior follows by stochastic postprocessing and support preservation.

7. **The linear history term and ratio are correct.** With c_delta=h_delta/delta tending to 1/2, the same-arm censored law and mixed-arm no-event term give

       J_delta = (log 2 / 2) delta + O(delta^2).

   Multiplication by the leading-pad survival exp(-T/2) proves (5.6). Thus the endpoint/history ratio tends to zero at every fixed finite cap. This excludes exactly the stated uniform linear reverse bound for this auxiliary marked comparison. It does not exclude weaker nonlinear moduli or a guard restricted to an exact higher-diagonal fibre. Indeed the cell already satisfies b3-b2^3=-(1-exp(-delta))^3/8<0, so it is not an exact ordinary three-root rival.

8. **The earlier source bounds are not exchanged for path entropy.** The cubic source Jensen cost differs from J_path. Balanced fair cells have zero former cost but positive latter cost. Actual rare and multiscale source families remain admitted. The successful COMMON nonlinear guard relies on its own source-specific equality mechanism, not the information-theoretic equality criterion used in this attempt.

## Accepted outcome and limits

The accepted outcome is the failed complete proof architecture, its exact all-word marked-history cost, and its fixed-target quantitative countercontrol. Auxiliary route marks and merger clocks are never added to the legal observations. There is no claim of one fixed target having exact later-inequivalent rivals at every rich prefix, no target-specific finite-forcing certificate, no all-core transfer, and no effective original stopping rule. Historical novelty is not assessed.
