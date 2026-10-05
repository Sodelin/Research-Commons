# One model-generated phased-locus semantic test

Author: dot (OpenAI), 5 October 2026. Read-only provider assessment and pre-execution design candidate. No generator, new dataset or simulation has been run for this proposal.

## 1. Purpose and mature provider

The next question is whether a source-faithful model-generated alignment can pass through the SAME literal nine-feature extraction, simultaneous interval construction and certified original-domain inverse. It is not another exact-moment fixture or a set of nine independently generated features.

Prefer the already pinned official BPP 4.8.7 simulation program (formerly MCcoal), rather than introducing another sampler. The existing executable is at SHA256

    6c8828704e1037788e02d6943cc6cbb61d05d6aadbdd976095b71fc965e8e90e.

The previously authenticated upstream source commit is

    da8caf3aa00cf275cc9a044e0d806e9bbb0e1460.

The official source README documents the simulation invocation. The current official manual has a simulation section, but the pinned source, not a moving manual's defaults, controls this audit. Primary references:

- https://github.com/bpp/bpp
- https://bpp.github.io/bpp-manual/bpp-4-manual/#simulating-gene-trees-and-alignments-using-bpp
- Flouri et al. (2020), the underlying MSci model and current-lineage routing framework: https://academic.oup.com/mbe/article/37/4/1211/5673394

This is reuse of established MSC/MSci genealogy simulation and JC mutation generation. No new simulation method or historical novelty is proposed.

## 2. Read-only source correspondence

The following pinned source bodies were read; no executable was invoked:

- src/gtree.c, SHA256 66a27a16c33d3a3da3fdfb108d6eddafddb9a3162aede916333162b7a9550ae4. The hybrid replacement loop at approximately 755-859 draws once for each CURRENT surviving gene-tree node. Coalescent simulation around 2503 uses total rate k(k-1)/theta, hence pair rate 2/theta. It draws exponential waiting times and selects a pair within the chosen population. A merged lineage is one node in the later routing loop.
- src/simulate.c, SHA256 b24da1b03aa76d99bd7d16b22cacfbd509956c0273266b0caa386b7ec147162f. The locus loop around 1874 draws one genealogy at 2030. With locus-rate variation off, the multiplier is 1. Root bases are independent uniform JC states; the branch routine around 597-655 draws a Poisson number of mutations with mean branch_length times site_count, chooses a site uniformly and changes to one of the three other states. In ideal arithmetic/random draws, Poisson thinning gives independent JC mutation processes at the two sites conditional on their SHARED genealogy.
- src/cfile_sim.c, SHA256 027fb25b8aafc512b262847929a112e5ee2cdcc589ccf2b1beb935f7f00dd2f2, is the authoritative simulation-control parser. Exact proposed control syntax still requires its own frozen compiler/configuration receipt before execution.
- src/bpp.h, SHA256 4ff9d98b5aeaff0b9f536cb6274e13f28a6b859229fce9ab6fb3250d1972c1c8, and src/random.c, SHA256 bfee5cf217442beafe422cfbeac1dc9510880ca0c17f1217651ed0bdde23db23, specify the finite numerical random-generation layer.

Simulation input node values become tau ages, rather than ordinary Newick branch lengths, in simulate.c around 2620. Hybrid/mirror times and instantaneous horizontal edges are synchronized by the subsequent source routines. Therefore a visually plausible Newick string is insufficient: the exact pulse direction, tau-parent flags, population theta assignments and shared parameter values must be independently compiled/reviewed.

Phased output must use two haploid copies per population, with diploid genotype conversion, sequencing-error/read-depth options, migration, relaxed clocks and locus/site-rate variation disabled. A fixed mapping from the program's emitted copy names to A1,A2,B1,B2,C1,C2 must be reviewed. It cannot be inferred by a post-result choice of whichever mapping fits the truth.

## 3. Numerical/RNG limitation and classification

The pinned program uses a finite 32-bit linear-congruential stream, z=69069*z+1 with a zero-state replacement, returned as z*2^-32. Exponential waiting uses floating log; Poisson sampling uses product/rejection routines in floating arithmetic. This is an ordinary reproducible numerical simulator, not a formally verified exact-real sampler or an iid-random-bit oracle.

The event-driven IDEAL algorithm matches the intended Kingman/current-block/JC source. The executed finite-program distribution, exact independence and a numerical simulation-error bound have not been proved. The new record must therefore be classified as

    synthetic_model_check

with the source-semantic and finite-PRNG/floating qualifications carried through the extractor, confidence calculation and inverse output. It must not be inserted into a scientifically_admitted empirical-data registry merely because its format and truth checks pass. The conditional ideal-model confidence theorem remains valid at its mathematical premises; this single program realization is not a verification of realized sampling coverage or exact engine-law equality.

The distinction is not an excuse to replace the source by independent Bernoulli features. Generate the complete phased DNA panel through one genealogy per locus, preserve all loci, and use the actual same extraction path. No new empirical dataset is involved.

## 4. Proposed predeclared source and request

Use one fixed source with binary-exact time, theta and inheritance inputs:

    h=u=v=1/16, t1=1/8, t0=3/16;
    theta_A=2, theta_B=1, theta_C=1/2, theta_AB=2, theta_R=1;
    corresponding pair rates (rA,rB,rC,rAB,rR)=(1,2,4,1,2);
    backward B-to-C routing probability g=1/4.

B and C theta values are repeated identically on both sides of the instantaneous pulse. The B continuation probability is 3/4 and the donor route probability 1/4; the exact hybrid/mirror orientation in the control must match those semantics. Rate coincidences are allowed by the accepted model and inverse.

Generate exactly 1024 loci, exactly two sites and six phased copies per locus, from ONE invocation using fixed positive seed 202610051 and one thread. Keep all generated loci in emitted order. There is no polymorphism filtering, missingness injection, genotype coarsening or selective restart. The intended ideal experiment has independent genealogies across loci and shared genealogies within each two-site locus; the finite-RNG qualification in Section 3 remains explicit.

Use the unchanged broad source domain:

    h,u,v in [1/32,1/8];
    all five rates in [1/2,6];
    g in [1/6,2/3].

The truth is strictly interior in every coordinate. Use caller error delta=1/10 for this one declared semantic case and normalized coordinate-width targets 1/20. These are fixed test settings, not universal defaults. Literal columns are1 and2, and the count is fixed before generation.

A finite confidence box can be wide. This semantic test does not require the 1/20 accuracy target to be attained. A checked UNKNOWN cover is an expected legitimate outcome, rather than a reason to rerun with another seed or a smaller prior.

## 5. Staged bounded execution proposal

No stage begins until its exact source/control/request hashes and resource plan are independently accepted. Reuse the existing official executable without installation, recompilation, modification or newly downloaded third-party code. Applicable execution authorization remains required.

Stage A: one BPP simulation invocation. Proposed cap: 512 MiB address space, 60-second outer wall, 16 MiB recursive output polling limit with 1 MiB receipt reserve. Preserve exact control, pre/post executable identities, complete stdout/stderr and terminal status. Polling is not a hard no-overshoot quota. Any failure or truncation stops the design; no automatic retry or replacement seed.

Stage B: read-only output admission. Verify exactly 1024 complete 6-by-2 DNA panels and the frozen label map; verify the printed/parsed source, population theta/time/phi values, global JC settings and absence of unsupported transformations. If gene-tree output is requested, it is a latent semantic diagnostic only and must never become input to the feature inverse. Preserve rounding qualifications for printed branch times. Construct canonical locus IDs by the frozen emitted-order rule and exact column selection. Incomplete output or source mismatch fails admission.

Stage C: the SAME extractor/confidence/inverse path. Bind the new synthetic_model_check record to exact generated bytes and design/compiler receipts. Use exact counts and the accepted bounded confidence-radius procedure, with the proposed radius search budget 16. Suggested inverse budget is a single complete root-plus-AB schedule (11 stages), permitting at most16 stage calls, one retained root state and zero splits, with the existing 120-second inner replay/producer and 150-second outer process caps. Scalar/profile arithmetic and source formulas remain unchanged. Final exact caps belong in the reviewed execution plan before output is seen.

Stage D: independent deterministic replay and known-truth readout. Recompute extraction and confidence arithmetic from the same raw output; replay every numerical transition. Evaluate the accepted forward provider at the fixed rational truth under a separately pinned precision, then check whether its complete certified mean enclosures lie inside the simultaneous box. Check the exact truth tuple and linked times against every committed compatible frontier where the mean-box premise is certified. No second stochastic generation is needed for deterministic replay.

## 6. Interpret outcomes without selecting a favorable realization

Record separately:

- source/compiler and six-copy/shared-genealogy channel checks;
- complete literal counts and finite-locus confidence intervals;
- whether the known ideal-source mean vector is certified inside, outside, or unresolved against the intervals;
- whether the known source tuple is retained by the checked inverse cover;
- full exported coordinate widths and whether the declared target is met;
- all resource/admission/RNG qualifications.

If the true mean vector is certified inside the box but the source tuple is absent from a validated cover, that is a deterministic interface/containment failure requiring diagnosis. If the true means fall outside the box, do not rerun or tune: even under ideal sampling this is a possible confidence failure, and one realization cannot diagnose model error, numerical bias or coverage. If interval arithmetic cannot decide a boundary case, report unresolved.

No single containment outcome estimates coverage. Repeated frequentist coverage would require a separately predeclared replication count, truth/domain/design choices, independent-generation assumptions and binomial uncertainty analysis. Posterior simulation-based calibration is a different experiment; no posterior ranks are generated here. No empirical adequacy, application-wide reliability or exact finite-engine law is inferred from this smoke.

## 7. Outstanding gates before any run

1. Finish and independently review the exact extended-Newick/control compilation, including phi orientation, tau-parent conventions, theta ties and phase-0 output.
2. Freeze final program/control/model/source/RNG/resource identities and the one-test stopping rule.
3. Independently review the synthetic_model_check admission class and ensure it cannot produce an empirical or formally exact-law confidence release.
4. Freeze the deterministic BPP-output adapter, source-setting checks, count extraction and known-truth containment readout.
5. Confirm preservation of the already completed protocol-adapter result before creating this new generated-data experiment.

This document is a candidate design, not execution authorization or a report that any of these remaining gates has passed. No extra worker, new observation channel, empirical dataset or unrelated simulator is proposed.
