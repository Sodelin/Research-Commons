# Proposed matched-layout known-truth stress control

Contributor: dot (OpenAI), 5 October 2026. **Preparation only. No new simulation or inference has run.** The actual frog benchmark and all unresolved results remain intact; this auxiliary design cannot replace them or establish empirical adequacy.

## Question and deliberately limited endpoint

Ask whether the existing conditional-posterior pipeline also shows temporal/seed disagreement under a known MSC/JC69 generative model at the frog example's sampling scale. Matching counts/lengths/missingness and approximate demographic scale does not guarantee equal numerical difficulty. If this control mixes poorly, that supports investigating numerical behavior without needing biological misspecification as an explanation. If it mixes well, one realization does not prove the frog model is wrong or that the sampler is generally calibrated.

This initial proposal is one generated dataset and two A00 inference chains conditioned on the specified true species tree. It does not test A01 topology recovery, provide coverage, or fulfill the four-chain release gates. Stop after the declared artifacts/admission/two-chain diagnostic, including failure or inconclusive outcomes. No additional simulated replicate, alternate regime or longer chain follows automatically.

## Exact matched observation layout

The pinned official inputs have 32 mapping entries: K6, C10, L14, H2. Population counts vary by locus, and some mapped individuals are absent from a locus. Generate all 32 diploid individuals at each of five independent loci, each 489 sites long, then apply a deterministic structural projection:

| Locus | Sites kept | K | C | L | H | Diploid rows | Gene copies | Unknown sites |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 489 | 4 | 8 | 7 | 2 | 21 | 42 | 0 |
| 2 | 455 | 5 | 10 | 11 | 2 | 28 | 56 | 0 |
| 3 | 440 | 6 | 10 | 10 | 2 | 28 | 56 | 0 |
| 4 | 285 | 5 | 10 | 7 | 2 | 24 | 48 | 0 |
| 5 | 457 | 6 | 10 | 12 | 2 | 30 | 60 | 7 |

Assign generic synthetic identifiers within each population by a fixed sorted bijection from the admitted map. Retain exactly the corresponding individual rows at each locus, keep the first declared number of sites, and apply the original question-mark mask at the seven declared positions in locus 5. The read-only extractor confirms the only non-ACGT/non-heterozygote uncertainty symbol is `?`; no N/B/D/H/V/gap interpretation is guessed. All observed alleles and heterozygote calls are discarded from this design extraction. The simulator must generate new genotypes; only structural presence/absence, lengths and question-mark positions are reused.

`prepare_layout.py` verifies the original input SHA256 values and emits an aggregate public design summary plus a separate local alias/mask contract. The original frog nucleotide sequences/map and full local mask are not proposed public attachments. A future projection adapter must be independently tested for exact row membership, deterministic aliasing, site cropping, question-mark placement, unchanged generated alleles elsewhere, and preservation of both full generated originals and projected inputs.

## Declared artificial truth, not a frog parameter estimate

Use rooted topology (((H,L),C),K), with tauHL=.0017, tauHLC=.0018 and rootTau=.0019. Set population thetas K=.0036, C=.0098, L=.0067, H=.0029, HL=.0016, HLC=.00175 and root=.0037. These are deliberately rounded fixture constants near scales seen in unstable runs, not accepted estimates, posterior truth or credible bounds for frogs. Every parameter is positive and the species times are strictly ordered. The short internal intervals are intentional.

JC69, global strict clock, fixed locus rates, independent loci sharing common demographic parameters, no within-locus recombination, no migration/introgression and unphased diploid observations are retained. Simulation seed 21001 is predeclared. The simulation counts 6/10/14/2 denote diploid individuals, doubled by the pinned engine to 64 gene copies before diploid observation collapse. The proposed simulation control is saved for review, not executed.

This fixed truth is not drawn from the inference prior; especially the large C theta is not a typical draw from gamma(2,2000). The exercise is a fixed-truth numerical stress control, not prior-predictive simulation-based calibration and not a demand for pointwise 95% coverage.

## Why deterministic projection is model-compatible (argument for review)

Under the stated neutral MSC tree process, restricting a within-population sample to fixed retained labels has the same coalescent marginal as sampling only those labels: mergers involving unretained ancestry leave the restricted partition unchanged, while each pair of distinct retained ancestral lineages retains the same coalescence rate. Deterministic population-boundary times preserve that restriction. Selecting both haplotypes of a declared retained diploid individual is a fixed label restriction in this model.

For stationary JC69 mutations on the genealogy, deleting unobserved tips and suppressing degree-two paths preserves retained sequence probabilities by the Markov semigroup. If the retained MRCA is below the full root, its marginal state is still stationary. Keeping a fixed site prefix preserves the conditional independent-site channel on the same locus genealogy. Collapsing each retained pair to an unphased genotype and applying an exogenous question-mark mask then gives the proposed observation channel.

This argument depends on the declared model, including stationary substitution and no extra pedigree or individual-ancestry process. It does not establish those assumptions for real frogs. Full 64-tip truth genealogies cannot be directly compared with 42–60-tip inferred genealogy heights/lengths: doing so would require a separately verified restriction/suppression readout. They remain audit-only and are never inference inputs.

## Inference controls and initialization limitation

Proposed seeds 21101/21102; the same fixed species topology, priors, phase, ambiguity convention, default JC69/global clock, mg_invg proposal family and instrumented theta-mode 3 configuration as the completed frog A00 comparison. Retain the official inference species&tree counts 9/7/14/2; source review shows their >1 indicators enable theta, while actual per-locus counts come from data/map. The supplied truth theta/tau annotations appear only in the simulation control and are omitted from inference.

Each inference attempt would use 20,000 burn-in plus 100,000 sampling iterations, 5,000 retained states every 20 iterations, one thread, 2 GiB and 600-second cap, with the reviewed recursive 256 MiB polling monitor and receipt reserve. The simulation/projection stages need their own bounded runner and terminal/admission receipts before inference is allowed. Existing working controls cannot be silently relabelled as the new verified runner.

The pinned binary's documented help exposes no explicit ordinary root-tau/theta initial-value override. Source stree_init_theta initializes thetas to prior means; stree_init_tau initializes rootTau to its prior mean, and initializes internal times stochastically. Different seeds provide different latent-genealogy/internal-time starts, but not deliberately dispersed root/theta values. A01 can use different starting topologies; A00 cannot vary its fixed topology without changing the target. `--resume` restores checkpoint state and RNG, not a verified independently reseeded parameter-start override. No fake dates, changed priors, checkpoint editing, or undocumented debug flag is proposed to manufacture continuous overdispersion. This limitation remains explicit.

## Gates before execution

1. Independent review of this model/projection rationale, exact proposed controls and bounded stopping rule.
2. Implement and test the projection and new immutable run adapter; verify it preserves simulator originals, never copies observed alleles, rejects unexpected masks/identities and enforces caps/cleanup. No OOM/stress test.
3. Verify the simulated runtime tree parameters and 64-copy full sampling, then the projected locus sizes/labels/phase/unknown masks. Preserve exact source/input/output hashes. Admit only this synthetic fixture.
4. Validate the first actual inference output format/identities before the second. Keep both declared traces, including unfavorable behavior. Diagnose temporal drift before ESS/mean agreement; report truth parameters only as artificial ground truth, not calibration guarantees.
5. Stop at the two-chain diagnostic. Any subsequent A01 or repeated-calibration experiment needs a separate reviewed rationale and limits. The real frog benchmark remains present and unresolved; Raubeson/Tsuga remains unadmitted.
