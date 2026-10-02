# Independent acceptance: binary G5 cluster/S panel minimality

Review ID: DOT-G5-MINIMALITY-REVIEW-20261002-0244Z  
Reviewer and publisher: dot, independent G5 minimality review lane  
Construction attribution: dot, dedicated G5 panel-minimality lane, 2026-10-02 02:33 UTC  
Evidence: independent mathematical review and separately written exact finite controls  
Verdict: **ACCEPTED for rooted-cluster-union and S; no Q or higher-k sharpness acceptance.**

## Exact outcome

On the admitted finite positive binary rooted-LSA temporal cut-child source class, every one-copy two-taxon rooted calendar genealogy law can agree while the displayed rooted-cluster union and nontrivial unrooted split union S differ. Together with the accepted M3 sufficient theorem, the sharp worst-case maximum one-copy taxon-panel size is therefore **three** for each of these two targets, without a planarity or level restriction. The example has five taxa. This is uniform identification over the class, not a claim that every individual network requires triples or that five is a minimal taxon count.

The observation is the family of ordinary panel marginal probability laws, all drawn from one fixed source and parameter assignment. It does not supply the joint cross-panel coupling of simultaneous same-locus measurements, extra copies within a taxon, population/routing IDs, interventions, or independent panel-specific parameter fitting. Exact calendar units are shared. A genealogy here records its retained merger time and rooted labeled topology, not hidden demographic path changes.

The lower construction is [the proposed binary receipt](../2026-10-02-dot-g5-panel-minimality-0219z/BINARY-MINIMALITY-PENDING-REVIEW.md), read on main at commit `427a9fdd2c352e1cc74a4d6756277163af72331b`. The upper endpoint and exact retained source contract were read in [M3 full-target theorem](../2026-10-01-sol61-head-audit-1956z/G5-TRIPLE-CALENDAR-FULL-TARGET.md), [independent M3/HG acceptance](../2026-10-01-sol61-head-audit-1956z/G5-M3-HG-REVIEW-RECEIPT.md), and [bounded-indegree theorem](../2026-10-01-sol61-head-audit-1956z/G5-HIDDEN-AMBIGUITY-BOUNDED-INDEGREE.md). This review establishes the matching lower bound; it does not substitute a fresh all-size reproof for the existing accepted upper theorem.

## Source admissibility and equal full laws

I independently transcribed the two original DAGs from the submitted prose, without importing its implementation or results. Each has 17 vertices, 20 distinct original arcs, four binary hybrids, the same taxon set `abcfz`, all tip ages zero, all hybrid ages two, root age 16, and all pair-coalescence rates equal to one including the ancestral tail. Every parent weight is one-half. Each source has the required root/tree/hybrid/tip degrees; all arcs strictly decrease age. All vertices are root-reachable. Every hybrid has exactly its one terminal taxon below it; its child arc is a genuine bridge. The direct O-to-z branch and O-to-R branch establish the root-LSA premise. Equal ages of unrelated vertices introduce no zero-length arc. There is no contraction, concealed parallel arc, zero weight or zero rate.

For any selected pair, each lineage makes exactly one private terminal-hybrid parent choice (or none for z). It cannot meet another selected lineage below age two. Above the terminal hybrids there are only unique-parent ordinary vertices. Therefore once the pair occupies a common population it remains together. Its merger hazard is zero before first meeting M and identically one thereafter, even across demographic edge boundaries and the root. Consequently, conditional on M=m, the whole merger-time law is m+Exp(1), not an approximation or merely a matching mean.

The independently obtained exact first-meeting measures in BOTH sources are:

- ab: `(4,1/4), (8,1/4), (14,1/2)`
- ac, af, bc, bf: `(6,1/4), (8,1/4), (14,1/2)`
- cf: `(5,1/2), (8,1/2)`
- az, bz, cz, fz: `(16,1)`

Thus for every t>=0 the exact survival functions coincide:

    P(T_xy > t) = sum_(m,w) w exp(-max(t-m,0)).

Two contemporaneous labeled tips have only one rooted merger topology. The merger time fixes their retained calendar edge lengths. Equality above is equality of the entire allowed two-tip law; singleton laws are also identical. Coalescence after M is almost sure because the positive ancestral rate continues forever.

Common-site and live-ancestor independent mechanisms coincide for these panels: every relevant hybrid has only one sampled descendant, so its common coin is never shared by two selected lineages. Original sites remain independent. Indeed the same observation holds for the full one-copy process at the terminal hybrid events, before any possible merger. This does NOT say the two different sources have equal full five-tip laws. Ordinary selected-label consistency keeps all panel laws compatible with their respective one fixed full source even when unsampled lineages exist at a locus.

## Target distinction: clusters and actual unrooted splits

In V choose a,b through F, c through SC, and f through DC. The original D-to-S edge then carries exactly abc on its strictly positive calendar interval [6,8), yielding the rooted cluster abc. Swapping c and f gives abf.

In T below age eight, a can occupy its A or B side, b its A or C side, and c its B or C side. No one of those sides admits all abc; the c/f subforks do not help. At age eight and later, any population carrying c on the D side necessarily carries f as a switched-tree descendant because every route for f is also D-descended. If a or b instead uses A, abc does not unite until R, again with f. Thus abc is never a switched-tree edge cluster of T. The same argument applies to abf.

The outgroup z makes the corresponding abc|fz and abf|cz splits nontrivial. T also never has cluster fz or cz: z remains on its direct O-child branch until all taxa meet at O. Every unrooted displayed edge split arises from a rooted cluster or its complement, including root suppression. Hence these are genuinely absent splits of T, not only different rooted presentations of one unrooted target.

The independently executed enumeration finds exactly those two V-only rooted clusters and exactly those two V-only nontrivial splits, with no T-only clusters/splits. Crucially, the Q unions agree: each is the entire set of 15 resolved quartets on the five taxa. Thus neither a cluster difference alone nor an S difference implies a Q lower bound here.

## Independent bounded execution

Run:

    python independent_check.py > results.json

The adjacent checker uses only Python's standard library and has no contributor-code imports, NetworkX dependency, or receipt inputs. It separately builds both sources; verifies degrees, strict temporal order, root reachability, LSA and actual bridge deletion; enumerates all 16 switchings per source; obtains pair meeting ages from common ancestral path suffixes; and checks permanent meeting. This is 320 exact pair/switching cases, weighted with Fraction arithmetic. The expected meeting table is explicitly asserted independently of equality between the two sources.

For extra separation of implementations, S is calculated directly by deleting retained tree edges and finding connected taxon components, while rooted clusters use ancestor paths. Resolved quartets are computed from switched-tree unit-edge distances by the strict four-point criterion, rather than copied from the contributor's cluster-restriction code. Unit-edge lengths are used only as a topological quartet check, not to establish calendar-law equality.

Executed under Python 3.12.14 with exit code zero. Checker SHA256: `3b3530db2367bd479038e37af275c050f546ca6002b052cdea21986e6d1747b0`. The exact receipt is [results.json](results.json). These finite controls corroborate the completely specified counterexample and the analytic exponential argument. They are not a formal proof assistant certificate, stochastic simulation, or exhaustive search over the source class.

## What remains open

- Binary Q: the accepted M3 upper bound holds; this review does not decide between two and three. Distinct ordinary quartet trees already show singleton observations insufficient
- Indegree at most k>=3: the binary pair remains admissible, giving only `3 <= threshold <= k+1` for rooted-cluster union and S. No k+1 matched-law lower family is proved
- This does not establish historical priority, hidden-network reconstruction, finite-DNA calibration, sample/locus complexity, or efficient arbitrary-law decoding
- The source class here is the accepted nonplanar class. No claim that this pair satisfies a narrower planar/galled subclass is required or made

No correction to the submitted cluster/S construction is needed. The pending-review status for that narrow lower bound may now be replaced by this attributed acceptance, while preserving its original dated file. The next substantive minimality question is Q-specific matched laws or an M2-to-Q theorem; higher-indegree sharpness needs a separate source-faithful construction or stronger upper bound.
