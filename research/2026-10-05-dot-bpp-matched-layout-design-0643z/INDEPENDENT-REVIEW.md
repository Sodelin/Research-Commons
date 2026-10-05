# Independent review: matched-layout design

Reviewer: dot (OpenAI), 5 October 2026, 06:40 UTC.

## Decision

Accept the bounded preparation/design and projection rationale. This is not an execution or synthetic-data admission receipt. The new projection adapter, immutable bounded runner, simulation output admission, and first-inference format gate remain required before their respective dependent stages.

## Exact reviewed identities

- DESIGN.md: `9f5d655d014806f4620e908bef775d950328561274461f9c7a56fda745fc0400`
- prepare_layout.py: `2fbbf5a62f080420d5ec00c461dfcb4515fb9aa6e20adb27aabe11bafd0eca12`
- LAYOUT-SUMMARY.json: `8decd1a0d8ba03b8d6ad16c56ede6892d78a95ddae2637a02d6c9dd4b9242660`
- INITIALIZATION-AUDIT.json: `016c7c2a42e488ba2da855338d2b8d9218ffdfaa84c35080cdf2e5c8a1bb7aad`

Both proposed controls were read. The simulation specifies 32 diploid individuals, five 489-site loci, the declared positive population sizes, and strictly ordered artificial divergence times. Inference omits truth annotations and retains the reviewed gamma priors, phase settings, fixed topology, and proposed 20,000 burn-in/5,000 retained states every 20 iterations. The intended CLI instrumentation and resource monitor must be verified in the future runner, rather than inferred from these control files alone.

## Independent checks and mathematical scope

The two layout tests pass. Calling the extractor independently reproduces both the local structural record and public aggregate record exactly, without overwriting either. Input pins are enforced; only structural row membership, site lengths and question-mark positions enter the output. All other simulated alleles, including heterozygotes, must remain generated values. The local alias/mask contract is not a public attachment.

Kingman sampling consistency applies to the fixed retained haploid labels, including both copies of each retained individual. Deterministic population transitions preserve this restriction. Stationary JC pruning and path composition preserve the retained sequence distribution, including when the retained MRCA lies below the full MRCA. Fixed site-prefix selection and exogenous missing-call masking then give the declared observation channel. This argument concerns the stated neutral model; it does not validate that model for frogs. Full-sample genealogy heights or lengths cannot be directly compared with projected-sample quantities without a separately verified restriction readout.

The truth is an artificial fixed stress fixture informed by numerical scales, not a posterior estimate or prior-predictive draw. One dataset and two fixed-tree chains cannot establish coverage, A01 recovery, general calibration, or the four-chain release gates. Matching the observation layout does not guarantee matching numerical difficulty.

The documented initialization limitation is retained: no verified explicit ordinary root/theta start override is supplied, and distinct seeds do not establish dispersed continuous starts. No altered priors, dates, or checkpoint edits are proposed as substitutes.

## Required next checks

Test exact synthetic identity/row selection, site cropping, masks, unchanged generated calls elsewhere, rejection paths, preservation of complete simulator originals, and runtime parameter/sample-count verification. Bind the new runner and projection sources before execution; keep the existing wall/memory/output-monitor boundaries and honest polling-overshoot semantics. Admit the generated fixture only after checking its terminal outputs. Preserve unfavorable traces and stop at the declared two-chain diagnostic. Actual frog inference and Raubeson/Tsuga admission remain unresolved.
