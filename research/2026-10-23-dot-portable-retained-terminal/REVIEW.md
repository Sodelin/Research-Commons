# Corrected retained-profile build: terminal evidence review

Date: 23 October 2026, 15:10 UTC. Reviewer: dot (OpenAI), for Nolan.

## Exact outcome

The existing owner's [run 39956450515](https://github.com/Sodelin/Research-Commons/actions/runs/39956450515), at immutable source `0b9e1cc1d23e7fe182672bd9166e555259a65cf6`, completed with overall **failure** at 15:06:50 UTC. This does not mean its retained mathematical profile failed. The independently retrieved terminal logs for [job 120423643520](https://github.com/Sodelin/Research-Commons/actions/runs/39956450515/job/120423643520), “Coherent retained Lean profile (not all 116 formalizations),” establish two separate outcomes:

1. **Fresh retained-profile compilation, aggregate and owned audit passed.** Step 8 completed successfully. The log contains all 1,633 ordered module invocations, from `SourceNetwork` at 12:55:05.9605489 to `ResearchCommons` at 15:05:50.8714513. Its final receipt reports `compiled_modules: 1633`, `checked_or_reused_modules: 1633`, `reused_retained_objects: 0`, `selected_source_modules: 1631`, `full_profile_source_modules: 1631`, `complete_profile: true`, `compiler_exit_success: true`, and `owned_axiom_audit_passed: true`. The two additional invocations include registry/aggregate assembly. The source-graph SHA256 is `768e587ffb189b3700aa4acc82853dcced49477b80c028d70e055d40cf65ff13`.
2. **Subsequent generated-certificate integration failed.** Step 9, “Kernel-check Rust-emitted positive and negative certificates,” failed in `OriginalTreeBank.lean`. The first logged errors at 15:06:38 are unknown constants `UnifiedLean.G6.NaturalCellInverseRates.AgeAtom.equal` and `UnifiedLean.G6.NaturalCellInverseRates.AgeComparison.fixed`, followed by instance/type and proof errors. The process reports `PACKAGE_INCOMPLETE: Lean rejected OriginalTreeBank: exit status: 1`; the package step exits 2. This is after successful profile compilation/audit, not a recurrence of the earlier audit-directory error, and not evidence of a counterexample to the retained mathematics.

At 15:06:14.5277627 the owned audit printed **104,633 declarations, 94,481 theorems, zero owned axioms, zero nonstandard rows, zero missing modules**. These are audit declaration counts, not numbers of independent discoveries or complete claim cards. Crucially, the receipt also explicitly reports `all_claims_formalized: false` and `historical_acceptance_transferred: false`.

## Evidence preservation

Step 10 retained exact completed source objects and step 11 uploaded evidence, both successfully. The log records [artifact 12510503843](https://github.com/Sodelin/Research-Commons/actions/runs/39956450515/artifacts/12510503843), `portable-lean-evidence.zip`, 9,290,851 bytes, with uploaded ZIP SHA256:

`0c922b62441a3913f6aaf04e593766cab02a080244d851595e815d8ee762d6a7`

This review read the GitHub job/run API and decoded terminal job logs (23,282 lines; 2,977,781 JavaScript string characters). It did not download or independently hash the ZIP, rerun a compiler, inspect every proof body, or modify any source. The artifact identity/digest above is the hosted upload log's evidence, not a fresh local recomputation.

## Keep different runs and different gates separate

- The later run `39959472128` cancelled its own coherent-profile job `120433803666`; it did **not** cancel the watched job. Its selected population checker had previously failed in `NativePopulationTableCertificate`.
- At `078ca7a75366251396299821a2d216badf094042`, run `39961206384`/job `120439586391` separately passed a selected population closure/audit (3,950 declarations, 2,227 theorems, zero owned axioms/nonstandard rows/missing modules), then failed in emitted `EdgePopulation` code. Its first error concerned a noncomputable `originalSource` dependency, followed by type/field errors and heartbeat limits. This is neither the full retained-profile result nor a successful native population export.
- The full per-claim integration gate remains distinct and failed in the watched workflow. Passing the retained profile does not bind all current claim cards, establish every native/parser refinement or observation-law connection, or close G3/G4's unmatched original master obligations. All previously accepted mathematical scopes remain intact.

## Next action and stopping condition

**The old-head caller failure is already superseded in later scoped owner receipts; do not assign a duplicate repair.** The previously read [source-cell receipt at fcfc99d557fe474a7c66e02819a2438fe41b2f12](https://github.com/Sodelin/Research-Commons/blob/fcfc99d557fe474a7c66e02819a2438fe41b2f12/packages/research/integration/source-cell-verification.json) records `OriginalTreeBank`, `OriginalParallelBank` and `OriginalCellExclusion` passing at source `33e96ac3737ddbe7067970d51fa9e28370befad0` / run `39958237938`, with the complete selected 2,651-declaration / 1,400-theorem owned audit.

The additionally retrieved [population caller receipt at cc97572efbe42deb6e85fa848ae19d70da545746](https://github.com/Sodelin/Research-Commons/blob/cc97572efbe42deb6e85fa848ae19d70da545746/packages/research/integration/population-caller-verification.json), Gitblob `bacd9f654ad1b61b3cc3d08dba20c36c8156a88c`, records `OriginalTreeBank`, `EdgePopulation`, `AncestralPopulation` and `PathPopulation` passing at source `47ea5dcdef06592c0fbb2cdbaa32879dde0986c1` / run `39970715643` / job `120472647148`. It reports a clean 4,137-declaration / 2,363-theorem selected audit, with 116 selected sources, 108 retained objects reused and eight authored sources recompiled. Its explicit scope is particular total ordered-copy tables on the same captured original source/shared bank, with universal native/parser refinement, whole epoch/word/readout and full-registry coverage excluded.

These later receipts were read as immutable owner verification records; their jobs were not independently replayed or newly log-audited in this watch. They resolve the old particular-caller failures at their own source identities, not the full-profile gate on all later commits. Conversely, the independently log-verified fresh full-profile success belongs exactly to `0b9e1cc1d23e7fe182672bd9166e555259a65cf6`, not silently to the later sources. The remaining owner join is coherent evidence for the actual selected release plus the still-explicit per-claim/native/physical interfaces, not another derivation of these already checked examples. No rerun or duplicate repair is requested by this receipt.

The assigned watch is complete: the exact run reached a terminal state and its successful retained-profile stage, subsequent failure and evidence artifact have been distinguished. No newer run is being followed automatically.
