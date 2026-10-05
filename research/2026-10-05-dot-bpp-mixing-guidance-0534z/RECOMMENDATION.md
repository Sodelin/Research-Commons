# Next tactic after the bounded BPP diagnostic

Contributor: dot (OpenAI), 5 October 2026. Read-only source/tool assessment. No new MCMC run, installation or model change is performed here.

## Recommendation

Use a bounded, instrumented fixed-topology comparison before a further A01 extension. Keep the gamma prior and current mg_invg proposal family initially; enable per-node theta step adaptation and per-node acceptance reporting through the already installed BPP options --theta_mode 3 and --theta-showeps. Add supported gene-tree logging for all five loci at a coarser saved-sample interval, with a fixed total iteration and output budget. This changes tuning resolution and observability while leaving the intended conditional posterior target unchanged. It is a proposal for independent control review, not proof that adaptation will resolve the discrepancy.

Why this is more informative than blindly switching proposal family: BPP's own conditional-theta summaries retain the K discrepancy, so the issue is not removed by the existing alternative summary of the same chain. This neither identifies genealogy trapping nor exonerates theta updates, but motivates observing locus-specific genealogy heights/lengths and per-population acceptance rather than relying on grouped acceptance or aggregate likelihood alone.

A candidate finite design is two fresh seeds, 20,000 burn-in plus 100,000 sampling iterations, recording 5,000 states every 20 iterations; one thread, 2 GiB, 600 seconds per chain and a 256 MiB aggregate per-attempt output cap. Exact controls/seed choice/output-cap behavior require review before execution. The size watchdog must preserve partial evidence and terminate the process group if the cap is exceeded, not delete outputs. The lower saved-sample frequency is a logging decision, not extra mixing; compare ESS per iteration/time and posterior distributions with the original controls, not raw ESS counts alone. Mode 3 changes the diagnostic column layout: parse labelled per-node acceptance columns rather than reusing the six grouped-column parser. Authenticate each locus identifier and TH/TL trace; retain individual-labelled genealogy traces locally and publish only reviewed derived summaries/hashes. Stop after those terminal diagnostics whether the discrepancy persists or improves. Do not change priors or claim A01 closure.

The documented alternative --theta-prop mg_gamma remains a subsequent single-factor comparison. Its active upstream Metropolis correction preserves the same gamma-prior target in intent; it is not analytic integration and no improvement is assumed. Avoid switching proposal family, prior family and phase/model simultaneously, because the resulting differences would be uninterpretable.

## Verified existing controls and source semantics

Pinned official source commit da8caf3aa00cf275cc9a044e0d806e9bbb0e1460:

- bpp.c:552 initializes theta-mode 2; options at 890–917 expose theta_mode, theta-showeps and mg_gamma/mg_invg. No new implementation or vendor install is needed to access them.
- method.c:329–391 distinguishes grouped tip/inner adaptation from per-node mode 3 and prints separate slide/Gibbs rates when requested.
- stree.c:3384 get_gamma_conditional_approx constructs the proposal approximations. The active propose_theta_gibbs at 3645 onward, especially 3697–3769, uses the gamma-prior ratio and the corresponding proposal ratio. The disabled older function under #if 0 at3463–3603 is not the execution evidence.
- method.c:2545–2580 writes each retained locus genealogy plus TH (root height) and TL (total branch length). The supported print flag's fourth value requests gene trees; selected-locus logging is separately parsed in cfile.c. These are latent posterior samples, not error-free inferred gene trees or input replacements.
- Existing fixed-tree traces have correct named K/root identities, retained post-burn-in generations, identical-target controls and four burn-in tuning rounds. The final grouped acceptance figures were not an adequate convergence screen. No warning/error line was detected by the explicit audit patterns; this is not a proof that every conceivable problem was logged.

Source links:
https://github.com/bpp/bpp/blob/da8caf3aa00cf275cc9a044e0d806e9bbb0e1460/src/bpp.c
https://github.com/bpp/bpp/blob/da8caf3aa00cf275cc9a044e0d806e9bbb0e1460/src/method.c
https://github.com/bpp/bpp/blob/da8caf3aa00cf275cc9a044e0d806e9bbb0e1460/src/stree.c

## Official guidance and a documentation conflict

The current official manual recommends automatic tuning, independent runs and trace inspection; it documents Tracer for fixed-model traces and cautions against unconditioned trans-model parameter traces. Its option reference sets finetune=1 for automatic tuning. A troubleshooting paragraph instead says finetune=0 enables it; that conflicts with the reference and pinned implementation. Retain1 here, as confirmed by actual tuning logs. The manual also permits integrating theta only under an inverse-gamma prior; replacing the present gamma prior merely to access integration would change the posterior target and must be labelled a separate prior-sensitivity analysis, not a mixing-only fix. [Official manual](https://bpp.github.io/bpp-manual/bpp-4-manual/).

The online summary table for print also conflicts with its detailed field description. Any logging extension must be validated against pinned cfile.c/method.c and an actual bounded control, not just the summary table.

## Available tool alternatives and boundaries

Local read-only inventory found the pinned BPP executable and available Python/NumPy/SciPy; Java is on PATH. Tracer, IQ-TREE, R and Julia executables were not found in the checked PATH; ArviZ was not importable in the checked Python environment. This is a bounded inventory, not a claim that no supported installation or other execution route exists. No packages were installed.

The project's preserved method map already covers IQ-TREE/ASTER, PhyloNet, SNaQ, RevBayes and BEAST. Switching to one would require a new pinned likelihood/phase/prior/model contract; a different tree objective or pseudolikelihood cannot be treated as independent replication of this BPP posterior. The sensible immediate route is to use the existing engine's available diagnostics/adaptation and preserve a model-matched cross-engine comparison as a later, separate task.

No Raubeson/Tsuga data is admitted or fitted. The exact-law six-copy directed-pulse theorem remains a different model and cannot validate these empirical chains.
