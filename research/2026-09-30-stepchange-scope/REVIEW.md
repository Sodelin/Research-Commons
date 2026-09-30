# Independent adversarial review and executable receipts

2026-09-30. Parent session stepchange-scope; subagents share the parent's context and are not independent laboratories or blinded evaluators.

Two reviewers examined the all-N derivation: `royal_society_finite_population` checked source correspondence, endpoint and absorption assumptions; `finite_population_proof_audit` separately checked accessibility, martingales, limiting arguments and the full-family kernel. Neither found a fatal flaw under the declared finite extension. `finite_population_exact_check` wrote the rational endpoint verifier independently of the prose proof. Root read its implementation and reran it successfully. This is hand review plus exact bounded computation, not an executed Lean proof. Lean is absent from the observed executable path; no toolchain installation was needed for this bounded check.

## Objections that changed the packet

1. **Initialization matters.** The reset formula needs an already locally reset-compatible background before the pulse. Reviewer caught its omission; PROOF §4 now requires mirrored initial states or at least one unmarked reset generation. As a countermodel, let both demes initially be EE, use L=0 and reset after mating. The marked migrants have the same viability as their resident deme-two peers in the first generation, so expected B₁=B₀. Later reset makes global marker frequency a martingale, leaving R=0 rather than the positive reset-compatible formula. The verifier explicitly includes this control.
2. **Name the observable correctly.** H=2p̄(1−p̄) is global allelic diversity, not the observed heterozygote fraction. Mirrored pure demes have H=1/2 and zero within-deme heterozygotes. Prose and code now use the precise terminology.
3. **Separate finite horizon from source equilibrium.** Expected global marker frequency at finite T is our extension of the deterministic source assay. Terminal fixation gives equal-deme frequencies. No unconditional result survives an unannounced survival/persistence filter by default.
4. **Preserve stochastic choices.** Fixed-count balanced migration, soft viability, independent gametes, repeated parent draws and selfing are required. The paper does not provide those finite-population choices. Source life order is retained; moving reset earlier produces a different model and zero endpoint RI.
5. **Population size is not migration fraction.** Independence of N is at fixed m=k/N. Changing N at fixed k changes m. The proof excludes k=0,k=N and s=1 where its accessibility argument fails.
6. **Full-family computation is specified, not run.** Ten phased diplotypes, the pulse kernel, marker-absorbing classes, transient linear system and fixed-time LLN paragraph were separately reviewed. The endpoint script does not validate the full two-locus implementation or intermediate-epimutation comparison.

## Actual verification

Command: `python exact_check.py` (standard library only). All exact assertions passed; all three endpoint matrices have 36 states and stochastic rows, exactly two absorbing endpoint states, and reachability from every state. Both marker kernels preserve the global marker mean in every row. The selected-chain absorption probability and hitting-time linear systems have exactly zero residuals on all transient states.

At N=2,k=1,s=1/3, B₀=1/4. Complete reset from compatible backgrounds gives E B_T=1/5 and R=1/5 at T=1,2,5,10. Fixed-genetic, reset-before-selection and incompatible-L=0 initialization controls give R=0. Mirrored genetic initial states have E H=11/25 after one generation and approximately 0.155823 after ten; the exact mean selected absorption time is approximately 11.199115 generations. These are illustrative finite receipts, not extrapolated all-N proofs or biological estimates.

Results retain matrix SHA256 values, exact small fractions, exact linear-system solution and fraction hashes for longer expressions. The script reproducibly regenerates them. The excluded cases and s=0 control are exercised.

## Residual risks

The full stochastic extension has not been fitted to empirical populations or checked against freshly downloaded supplementary recursions. General sign regions, meaningful burn-in windows and sharp size-dependent bounds remain open. No exhaustive novelty search, independent external review, efficiency benchmark or field-advance certification has been performed. The all-N arguments stand on their stated assumptions; their broader biological consequence is a testable research program.
