# Predeclared known-truth smoke control

Contributor: dot (OpenAI), 5 October 2026. One generated dataset is not a calibration experiment and is not the empirical frog dataset.

Simulation seed 7001; inference seeds 8001 and 8002; no selection based on results. Species tree ((K,C),(L,H)); node divergence times KC=.001, LH=.0015, root=.002; theta=.001 everywhere, in mutation-scaled units. Five independent genealogies, each shared by 500 JC69 sites. Strict clock; fixed locus rates. Two diploid individuals per population, four gene copies per population before diploid observation collapse. No sequencing error, missingness, migration, recombination within a locus or introgression. Inference starts from a deliberately different topology, with the same core JC69 MSC model and gamma priors as the frog pilot, but this smaller synthetic sampling design does not validate frog adequacy.

## Upstream semantic evidence, pinned commit da8caf3aa00cf275cc9a044e0d806e9bbb0e1460

- src/simulate.c:129-150 process_diploid doubles configured sequence counts for populations with phase=1. Thus control counts 2/2/2/2 become four gene copies per population.
- src/simulate.c:1159-1217 collapse_diploid pairs the generated sequences, builds ambiguity-coded consensus and resets the alignment count to the number of individuals. The labels and generated specimen map are preserved.
- src/simulate.c:2029 onward simulates one genealogy in the locus loop; subsequent sequence generation uses that genealogy for all locus sites. src/simulate.c:2218-2241 writes full sequence data, collapses diploids, then writes the observed unphased alignment. Lines1757-1776 automatically open .full and .rand auxiliary outputs for diploid simulation; both remain audit-only and are never supplied to inference.
- Inference phase=1 is the same observation handling used in the official unphased frog control. It integrates phase ambiguity; it does not force a random haplotype resolution.
- src/bpp.c:651 initializes opt_threads=1; the simulation control parser does not accept a threads key, so that default is retained. Inference control explicitly sets threads=1.

Source: https://github.com/bpp/bpp/blob/da8caf3aa00cf275cc9a044e0d806e9bbb0e1460/src/simulate.c

## Checks before interpreting output

Require eight diploid observations per locus, five loci of length 500, four populations, exactly two individual-map entries each, legal IUPAC encoding, and stable hashes. Check the simulator's reported species times/ancestral population sizes, underlying gene-tree leaf count 16, and generation count. Only then run inference. The separate truth gene-tree output is retained for audit and never supplied as an error-free input to inference.

Both inference chains: burnin8000/nsample20000/sampfreq2; wall limit300s, 2GiB, one thread. Executable SHA256 is pinned to the already authenticated official BPP binary. Failed attempts stay distinct. Inspect posterior truth mass and model-conditioned credible-set inclusion but label all such outcomes as a single-dataset recovery smoke. Repeated simulation/coverage and biological model adequacy remain open regardless of outcome.
