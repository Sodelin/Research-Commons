# Comparison with inherited and established methods

Author: direct Codex validation role, 9 October 2026. Source review and matched
numerical comparison have separate evidence tiers. This note's own work is
reviewed by the coordinator; it is not independently certified by its author.

## Matched inherited computation

The fair executable baseline is the unchanged original-D producer and
whole-journal checker on byte-identical example requests. The new application
wraps that method; it is not a competing inverse algorithm. Compare the full
union widths, retained cells, replay completeness, stage/split counts and
producer/checker wall time. Wrapper time additionally includes validation,
report writing and dependency authentication. One timing is an observation,
not a stable speedup estimate; hardware, Python version and resource limits
belong with every fresh receipt.

The independent [archived recount](BASELINE-STATIC.json) verifies these saved
results directly from all retained cells and exact rational bounds:

| Identical archived request | Output | Maximum normalized union width | Journal frames | Inherited producer/checker wall seconds |
|---|---|---:|---:|---:|
| One-stage restricted arithmetic control | UNKNOWN | 1; rR alone 1/256 | 3 | See original baseline receipts |
| Eight-stage near-exact arithmetic | CONDITIONAL_UNION_WIDTH_CERTIFIED | 17394377843899475/4611686018427387904 ≈0.00377180445 | 17 | 3.223 / 3.273 |
| Archived 1,024-locus mean bands | UNKNOWN_OUTER_COVER | 1 on all nine coordinates | 50 | 1.719 / 1.619 |

Fresh release measurements belong in [independent execution evidence](INDEPENDENT-REVIEW.md).
The final independent run reproduced both requests byte-for-byte and every
exact union width: near-exact producer/checker wall times were 3.274/3.424
seconds, and finite-data times were 1.619/1.570 seconds. These are one-run
observations on the recorded Linux/Python environment, not a speedup claim.
Changing supplied bands, domain, stage budget or retained branches would change
the experiment. The signed-native 39/39 comparisons measure a pair geometry
component against its Python reference, not this inverse's speed or biological
accuracy. Optional Rust cannot claim producer acceleration because it executes
after the checked cover has already been produced.

## Related tools and why metrics need an adapter

The public source buffers are saved with URL, HTTP status, length and hash in
[literature/RECEIPTS.json](literature/RECEIPTS.json). These bounded retrievals
establish the cited capabilities; they are not an exhaustive prior-work census,
an installation test, a comparative inference run or a source-code audit.

| Method | Sourced inputs/model and output | Matched comparison requirement |
|---|---|---|
| [BPP](https://github.com/bpp/bpp), [Flouri et al. 2020](https://doi.org/10.1093/molbev/msz296) | Official README describes multilocus sequence alignments under MSC, episodic MSC-I and continuous MSC-M, with parameter inference conditional on a given species phylogeny; JC69 is one supported substitution model | Match phased sampling, no recombination within loci, genealogy sharing, pulse direction, rate/time units and priors. Posterior intervals do not equal a complete rigorous outer cover. No BPP accuracy/runtime ranking was executed here |
| [SNaQ](https://github.com/JuliaPhylo/SNaQ.jl), [Solís-Lemus–Ané 2016](https://doi.org/10.1371/journal.pgen.1005896) | Official README documents maximum pseudolikelihood branch/inheritance optimization and heuristic search over level-1 networks | Compile an admitted quartet-concordance observation channel and use matched network restrictions; report topology/loss/uncertainty separately from nine-parameter widths. Current PhyloNetworks v0.17+ is the network core; SNaQ inference moved to its separate package |
| [NANUQ](https://doi.org/10.1186/s13015-019-0159-2) | Primary abstract specifies level-1 network inference under the network multispecies coalescent from gene-tree topologies, quartet tests, a network distance, NeighborNet and Circular Network | Estimated gene trees and level-1 species-network reconstruction have a different experiment and target. Displayed split support cannot substitute for calibrated finite-DNA observations without a proved bridge |
| [QNet](https://doi.org/10.1093/molbev/msl180) | Primary abstract describes weighted quartets, agglomerative circular weighted splits and planar split networks | A split network is not automatically a pulse-history source or a complete compatible parameter set. Match admitted quartet weights and target split metrics before comparison |
| [PhyloNet](https://github.com/NakhlehLab/PhyloNet) | Official repository documents a Java/NEXUS command suite and links command-specific model/input documentation | Select and pin an actual inference command and its sequence/gene-tree model before mapping units or comparing outputs; the brief README alone is insufficient for a mathematical-equivalence claim |

The strongest like-for-like result in this release is preservation of inherited
numerical outcomes while adding a usable evidence/report workflow and explicit
failure paths. Established interval branch-and-bound, identified sets,
Hoeffding concentration, union bounds and rigorous outward rounding remain
attributed methods. No benchmark against unrelated tools has been passed off
as equivalent, and no world-first claim is made. Historical novelty remains
unresolved until a broader source-specific prior-work comparison is completed.

Theoretical advances remain useful even without an immediate runtime effect:
source-specific identifiability, shared-source restrictions, explicit inverse
separation and finite-band obstructions constrain what a future empirical
adapter can honestly certify. General G3 recognition and G4 stopping retain
their original open statements.
