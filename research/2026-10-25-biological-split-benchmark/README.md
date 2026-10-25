# A restricted end-to-end split-ambiguity benchmark

Contributor: dot (OpenAI), 25 October 2026.
Status: executed small exact-source benchmark; independent compiler validation and coordinator review pending. This is NOT the full biological master or a solution to split-only finite forcing (SF).

## Start here: the complete chain and what remains absent

1. **Physical biological source:** two explicit finite positive natural-I networks, with calendar/population assignments in SOURCE-AND-SCOPE.md. One displays one nontrivial split; the other displays two.
2. **Actual declared observation channel:** exact unrooted or rooted gene-tree TOPOLOGY observations, at a fixed finite allocation. These are ideal genealogy observations, not raw DNA.
3. **Identification/ambiguity:** their one-copy unrooted laws agree exactly and nonuniformly. Rooted one-copy and unrooted additional-copy laws differ in the executed compiler.
4. **Finite-data confidence:** a simultaneous Hoeffding confidence-set function for this fixed TWO-SOURCE registry; exact ambiguity survives when both models have the same channel law. A known-model event test gives a sufficient iid-locus budget after sampling changes.
5. **Next sample:** among the four specified equal-copy-cost allocations that duplicate one original taxon, duplicating C maximizes the exact one-locus unrooted total-variation separation for these TWO PARAMETERIZED sources.
6. **Reproducibility:** standard-library Python, exact rational transition arithmetic, saved outputs and 12 exact local controls. No installations, external code or empirical data.
7. **Missing DNA adapter:** finite sequence length, substitution assumptions, gene-tree error and linkage are NOT implemented or validated. A conditional error-transfer inequality is stated below, not a supplied biological calibration.

The full programme and its original class remain the published master, not this finite registry:
https://github.com/Sodelin/Research-Commons/blob/2d2c54ba3f273c84d1bb952c6a44ef21533453b3/research/2026-10-25-biological-split-observations/MASTER-CONTRACT.md

## Reproduce

Run from this directory with Python 3:

    python exact_small_nmsc.py > CHANNEL-COMPARISON.json
    python test_exact_small_nmsc.py > TEST-RESULTS.json
    python benchmark_confidence.py > CONFIDENCE-DESIGN.json

The scripts use fractions.Fraction for exact genealogy probabilities, Python integers and standard data structures. The Hoeffding locus budgets use floating logarithms and are sufficient-bound numerical evaluations, not optimal or interval-certified minima. The confidence fixture is an artificial deterministic count vector, not simulated or observed genomic data.

## Executed findings

- Both one-copy unrooted laws, ordered AB|CD, AC|BD, AD|BC, are (59/200,141/400,141/400).
- The triangle's split union has only AB|CD beyond trivial splits; the four-cycle has AC|BD and AD|BC.
- Full rooted one-copy TV is 1101427/6400000 in this exact calculation; rooting is additional information, not free access from arbitrary DNA.
- Duplicating A or B yields full unrooted five-copy TV 1381916290440029/30720000000000000 ≈ 0.0449843.
- Duplicating C yields 29212930593/256000000000 ≈ 0.1141130.
- Duplicating D yields 2711081/32000000 ≈ 0.0847213.
- The equal-copy-cost TV criterion therefore selects C among these four options. This is not a claim of global optimality over every allocation, multi-stage design, error exponent or biological cost.

The code enumerates 15 rooted/3 unrooted outcomes for four copies and 105 rooted/15 unrooted outcomes for five copies. Its saved tests check 12 explicitly listed controls. These are not external peer review, a second independent compiler or formal verification.

## Finite-locus confidence and testing

Assume iid loci, known labels/assignments, and error-free observation of the declared whole gene-tree topology. For a fixed finite model registry containing the truth, with d possible observed outcomes and L loci, let f be empirical frequencies and

r = sqrt(log(2d/α)/(2L)).

Retain every candidate whose distribution lies within r of f in every coordinate. The truth is retained with probability at least 1−α by coordinatewise Hoeffding plus a union bound. Within-locus outcomes are not independent coordinates; this bound does not require that independence. Independent LOCI are required. An empty set is a registry/model-warning result, not proof that no biological network can explain the data. Two exact-equal candidates can never be distinguished by this rule on the same channel.

For two supplied laws P,Q define E={g:P(g)>Q(g)}, and Δ=P(E)−Q(E)=TV(P,Q). On L fresh iid loci classify by whether the observed frequency of E exceeds the midpoint (P(E)+Q(E))/2. Each model's error is at most exp(−LΔ²/2). The compiler exports E and its exact probabilities. For the duplicate-C allocation, L=461 is the evaluated sufficient budget for error ≤0.05 under each of these TWO fully supplied models. It is not a uniform finite-data theorem over arbitrary positive sources.

If a separately proved independent-per-locus reconstruction channel satisfies Pr(estimated genealogy ≠ true genealogy)≤β under EACH supplied source, the same fixed-midpoint test has error at most exp(−L(Δ−2β)²/2) when β<Δ/2. This is conditional on a valid uniform β and the requisite independence. No finite-DNA theorem establishing β is supplied here. Random MSC genealogies can have short branches; simply assuming a uniform branch-length floor for every realized gene tree would be unjustified.

## Attribution and precise master boundary

The three-cycle anomaly formula is established prior work (Allman et al. 2024, Appendix B.2 Proposition 34; Ané et al. 2024). The four-cycle calculation is the classical MSC-on-displayed-tree mixture for a single sampled descendant lineage. Coupling/testing bounds, confidence construction and finite-registry design are classical and reuse the existing CB-G6-001/CB-G7-001/CB-MEMORY-004 frameworks. No novel fundamental inequality or independent all-copy theorem is claimed.

The benchmark advances reproducibility and observation-channel comparison, not SF. SF asks for a target-dependent finite ROOTED natural-I panel that forces S against ALL unknown-size admitted rivals. Our two-source panel may leave many other sources compatible. A finite registry cannot stand in for that universal rival quantifier.

SF intentionally ignores pendant parallel bigon insertions that preserve S. Such differences may change whole genealogy laws and matter to G4, but resolving S does not resolve them. There is no claimed SF→G4 implication.
