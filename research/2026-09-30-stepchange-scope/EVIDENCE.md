# Source, prior-work and claim ledger

2026-09-30 / stepchange-scope. Rapid, targeted evidence map, not an exhaustive literature review. Primary-source facts and our extensions are separated below.

| Source | What was checked | Consequence / limit |
|---|---|---|
| [Planidin et al., 2025, DOI 10.1098/rspb.2025.1217](https://pmc.ncbi.nlm.nih.gov/articles/PMC12440623/) | Methods 2(a,b), Results 3(f), Discussion 4(c), Conclusion 5, freshly read by root and source reviewer | Infinite diploid two-deme model; migration→selection→recombination→mating→epimutation. Neutral ancestry pulse RI uses B₀=m/2 and eventual marker frequency; genetic and complete-reset endpoints are µ=0 and µ=1/2,φ=1. Primary-contact selected background is equilibrated before marking. Conclusion suggests possible finite-population strengthening, not a universal inequality. Our fixed-k exchange, soft weighting, independent gamete draws and expected finite-horizon statistic are added assumptions. |
| [Greenspoon et al., 2022, DOI 10.1111/evo.14494, author PDF](https://www.sfu.ca/biology/faculty/M%27Gonigle/pdfs/greenspoon-2022-1170.pdf) | Primary Methods and hard/soft-selection comparison; fresh root PDF and independent source reading | Finite stochastic two-patch epigenetic speciation models already exist. Their multilocus haploid model and genetic-bimodality/time endpoint differ from this diploid neutral ancestry pulse. It defeats “first finite epigenetic speciation model,” not necessarily the narrower assay contribution. |
| [CLUE, Ovchinnikov et al., 2021](https://arxiv.org/html/2004.11961v2) | Primary algorithm and proof of minimal constrained linear lumping | A proposed generic minimal LTI observable-preserving reduction duplicates established work. It cannot constitute the biological step change by itself. |
| [Zhu et al., 2024, Meaningful Causal Aggregation](https://proceedings.mlr.press/v236/zhu24a/zhu24a.pdf) | Primary causal-aggregation source checked by independent prior reviewer and opened by root | Different micro implementations of one aggregate intervention are established territory. A source-specific causal-response preservation result needs a stronger bridge. |
| [Celcomen accepted manuscript](https://www.nature.com/articles/s41467-026-69856-5_reference.pdf) | Independent prior reviewer recovered entropy/GNN model and direction/spot-resolution limitations; root reacquisition failed | Do not turn a statistical joint-distribution model into physical LTI dynamics without a derivation. This source mismatch helped reject a duplicate generic theorem lane. Root does not claim an independent fresh full-PDF read. |

The Planidin supplement and archived simulation code were not freshly reacquired. A [retained Samuel source audit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/feedback-speciation/SOURCE-AUDIT.md) records earlier supplement reading. The endpoint proof needs only the freshly readable main-paper mechanism plus our explicitly stated sampling choices. Matching a future general two-locus implementation to the exact archived recursions remains an obligation.

| Claim | Status | Evidence |
|---|---|---|
| Genetic selected-locus absorption at every admitted finite N | Hand-derived; two independent reviews | Uniform two-generation accessibility proof, PROOF §2 |
| Infinite genetic burn-in gives expected RI=0 | Hand-derived; independently reviewed | Neutrality after selected fixation; uniform burn-in bound, §3 |
| Complete reset gives RI=s(1−m)/(1−ms), all N and marker horizons | Hand-derived; independently reviewed | Fixed denominator and post-first-generation marker martingale, §4 |
| Burn-in and size limits fail to commute for global selected allelic diversity | Hand-derived; independently reviewed | Absorption versus deterministic complement symmetry and fixed-time concentration, §5 |
| Full parameter-family finite-state specification and terminal linear system | Hand-derived specification | §6; no full-family implementation or efficiency claim |
| Exact 36-state endpoint checks | Executed result once output is present | exact_check.py and exact_results.json; not an all-N machine proof |
| General finite-size strengthening, intermediate-transmission ranking, empirical speciation, priority | Unestablished | Explicitly retained research targets |

The nearest-prior check is enough to reject broad first-of-kind language. It is not enough to establish originality of the endpoint formula, the absorption observation, or their source-specific combination. Classical finite-state absorption, martingales, drift and large-population limits are dependencies.
