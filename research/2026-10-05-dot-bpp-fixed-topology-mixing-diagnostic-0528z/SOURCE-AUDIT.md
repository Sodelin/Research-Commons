# Prior-first diagnosis: source semantics and limits

Contributor: dot (OpenAI), 5 October 2026. All source references below use official BPP commit da8caf3aa00cf275cc9a044e0d806e9bbb0e1460. This is a read audit, not a finding of a software defect.

## Root-time prior and initialization

stree.c:1545-1567 initializes ordinary no-date root tau to the gamma prior mean alpha/beta=.002, then initializes interior times recursively. Merely attaching ages to a Newick string does not create overdispersed demographic starts in this mode; the user-specified age path is conditional on date input, which this pilot does not have. We do not introduce artificial dates to alter that contract.

The root-tau update at stree.c:5668-5672 uses the gamma prior factor; A01 topology moves use the matching factor at11099-11108. delimit.c:709 onward computes the uniform-rooted-topology prior through a topology-history weighting; that weighting is constant when the positive topology is fixed. Thus an A00 comparison with the same topology-conditioned demographic priors is a reasonable diagnostic of conditional traces, not a replacement for A01 posterior exploration.

Prior-only controls have root means near .002 but limited ESS; this is a sanity check against a gross shape/rate or units error, not a proof that the posterior implementation/mixing is correct. Matching a known prior moment can miss many errors.

## Population counts and phase

The official frog control's species&tree values9/7/14/2 are not substituted for the actual per-locus observations. stree.c:1175 onward counts populations from the alignment/map;2510-2580 compares the control indication and actual maximum counts, distinguishing one versus multiple sequences for theta estimation;2637 onward uses the control threshold to enable theta. Actual locus sizes and phase doubling are reported from the data. All populations pass the engine's multiple-sequence check. Preserving the official control does not assert that its four integers equal the observed per-locus counts.

Unphased diploid phase flags remain1/1/1/1 with ambiguity retained. No randomly phased auxiliary data or known genealogy is used as inference input.

## Reuse of engine diagnostics

BPP allfixed.c:227 onward implements its own Geyer initial-positive-sequence efficiency estimate, with maximum lag2000 and its documented numerical conventions. The A00 parameter table reports mean, ESS*, Eff* and lag-one correlation. We authenticate that table, preserve those existing-engine diagnostics and cross-check means against the actual numeric trace. The adapter's separately labelled ESS heuristic is supplementary; agreement between two autocorrelation estimates does not establish stationarity or discover an unvisited mode.

The official CLI exposes theta proposal alternatives (--theta-prop mg_invg or mg_gamma) and sliding-window frequency; the default gamma-prior path selects mg_invg (bpp.c:975-976). This is an available future parameterization/proposal comparison, not a change executed here. Its acceptance and scientific effect would require a separate bounded control review. We do not change the prior to obtain agreement.

## Interpretation discipline

Total-variation distance between two empirical topology histograms measures their disagreement, not distance to the unknown target. A small value can occur when both chains are stuck in the same region; a nonzero value can reflect Monte Carlo noise or nonstationarity. There is no stationarity certificate here.

The reported root-mean difference divided by estimated within-chain MCSE is a descriptive warning, not a rigorous tail probability or bound: these MCSEs rely on autocorrelation estimation and stationary behavior. The symmetric topology-composition/within-topology decomposition is an algebraic identity for empirical averages, not a causal attribution of the mixing mechanism.

The synthetic truth receiving about95% posterior mass on one dataset is not95% repeated-sampling coverage. Its known history and observation semantics make it a useful execution smoke while calibration, model adequacy and biological admission remain independent gates.
