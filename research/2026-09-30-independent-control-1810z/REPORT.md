# Independent inheritance: controls that preserve the recovery guarantee

ID: INDEPENDENT-CONTROL-20260930-1810Z. Author/publisher: Codex Work.
Internal reviews: ind_control_obstruction, ind_control_coupling,
ind_protocol_code_audit. Date: 2026-09-30 UTC.
Evidence: hand proofs, independent internal attacks and exact rational execution.
No formal proof, biological intervention or historical-priority claim.

## 0. Executive decision brief

**Ordinary partial controls cannot universally transfer the common-inheritance
recovery guarantee. A synchronized control program can. For support recovery,
one fresh coin per locus suffices and produces at most two additional actuator
configurations per nominal experiment row.** It can still require many sites to
be actuated together. Reducing programs does not reduce that site cost.

We exhibit two admitted four-taxon, two-hybrid states with different displayed
supports and exactly the same complete unrooted gene-topology laws in BOTH rows
of the original two-setting, single-actuator menu. Unlimited data from that
particular menu cannot distinguish their supports. This is stronger than merely
showing that a particular frequency rule fails. Stronger controls and stronger
gene observations remain distinct questions.

We also characterize the smallest set of additional shared-forcing sites for
emulating the full sampled ancestral routing/coalescence HISTORY law: exactly
the unfixed hybrids with at least two sampled descendant copies. This minimum
concerns histories, not the potentially smaller control set sufficient for gene
topology, metric observations or displayed support.

Component results are complete at reviewed hand-proof level. The master question
of optimal controlled gene/support recovery across all possible menus and
practical actuator models remains in progress. Astra's accepted passive
full-joint task remains separate.

## 1. Abstract

The global-switch occurrence bound g does not alone imply a gene-quartet
frequency gap under independent inheritance. A triangle with two sampled genes
below its hybrid has sole displayed quartet AB|CD but concordance factors
(59/200,141/400,141/400). An inert second hybrid yields an admitted partial-menu
counterexample; a diamond gives an equal-law state with complementary support.
We prove an exact history-emulation criterion using descendant copy counts and
give a persistent locus-wide synchronization compiler. Exact emulation uses
independent hybrid bits. Support recovery allows correlated bits: a shared fair
coin retains the g witness mass and the existing robust support bounds. We expose
the different program, setting, actuation and sample costs, and provide executable
rational verification and integration with the previously published provider.

## 2. Introduction: the whole outstanding question

Nolan asked for a different obligation, rather than another complement to the
accepted full-joint normalization search. This packet addresses the response of
the biological observation model to interventions. The full question is: what
controlled data suffice to recover the original displayed support, at arbitrary
finite sizes/levels/blob counts, under independent inheritance, and at what cost?

Existing ASTRA-OBS Section 6 already gives fully fixed covering-array sufficiency
under both inheritance models. Existing CONTROL-MENU gives exact occurrence-menu
counts under its product-switch contract. Existing robust statistical work gives
a sound provider if the gene-law gap premises hold. None automatically proves
that an ordinary partial intervention supplies those premises under independent
inheritance. We attack that bridge directly, without repeating full enumeration.

Prior work comes first: NANUQ supplies the known triangle formula and anomaly;
Fogg, Allman and Ane distinguish independent, common and correlated inheritance.
Our adaptation to controlled profiles and compiler is not claimed historically
novel. The source two-switch witness and sparse support decoder retain their
original authorship and outstanding review status.

## 3. Methods and exact contract

Networks are finite binary rooted representatives of the admitted LSA-rootable,
outer-labeled planar galled semi-directed class. Each hybrid child is a cut edge;
parallel-arc bigons are admitted. All population edge coalescent lengths are
strictly positive and finite. Natural inheritance weights are interior. The main
statistical application uses one gene per taxon per fresh independent locus.
The history coupling generalizes to finite sampling multiplicities.

Controls refer to the ORIGINAL hybrid IDs and original incoming-edge labels.
A fixed bit selects one parental edge for every lineage at the site throughout
that locus. Controls leave the conditional population/coalescent dynamics
unchanged. These are ideal intervention premises, not an implemented biological
procedure. Observation is a gene quartet restriction or a declared stronger
gene-tree observable. Target is the original displayed quartet support Q and
displayed split union S, with a compatible circular order when the decoder needs
one; the original hidden graph/numerical parameters are not the target.

NMSCind chooses parents independently for distinct live lineages. NMSCcom uses
one shared parent bit per site per locus, independently across sites/loci.
An intervention overrides a site; it does not condition observational data on
having followed the chosen parent. Those two experiments can differ.

For a row, F is its fixed hybrid set, f=|F|. The number d_h is the number of
sampled copies reachable below h's child cut edge, counting copies once per
sample label rather than once per path. Let M={h outside F:d_h>=2}, k=|M|.
With one copy per taxon, d_h is a descendant-taxon count. A certified safe
upper bound <=1 suffices to leave a site natural; a complete attachment graph
is not needed if those bounds are supplied separately.

## 4. Findings and proofs

### 4.1 An admitted ordinary-control profile cannot identify the target

Triangle T has arcs R->D,U; U->V,H; V->C,H; H->W; W->A,B.
Only AB|CD is displayed, under either parental choice at H.
Write x0=exp(-t_HW), u=exp(-t_UH), v=exp(-t_VH), w=exp(-t_UV),
and gamma=P(parent U). Its independent matching CF is the known expression

\[
a=1-x_0+x_0\{\gamma^2(1-2u/3)+(1-\gamma)^2(1-2v/3)
                 +2\gamma(1-\gamma)w/3\}.
\]

AB merging below H contributes 1-x0. Given survival, both lineages choosing
U or V gives the respective ordinary-tree term. Different parents let the
V-side lineage coalesce with C on UV; matching probability is w/3. Exchange
of A,B makes both discordant entries (1-a)/2. The upper population contributes
exchangeably and does not affect the formula.

Set x0=u=v=9/10, w=1/10, gamma=1/2. Then

\[
 p_T=(59/200,141/400,141/400),\qquad
 p_T-\min(p_T)=(0,23/400,23/400).
\]

Thus min-subtraction rejects the sole displayed quartet and supports both
absent alternatives, despite displayed occurrence one. Either H endpoint
control instead gives (23/50,27/100,27/100).

Add an inert hybrid J0 above D: replace R->D by R->P0, two parallel P0->J0
arcs, J0->D. J0 carries only D, so its two forced parental choices have no
effect on any quartet CF. The r=2 menu fixes J0=0 and J0=1 and leaves H
free. It is the existing 2r-2 single-actuator menu. It hits every assignment
on the exact pair of hybrid IDs. A zero-choice certificate already has
occurrence one; singleton certificates can reach g without forced bits.

Now construct diamond D: R->B,U; U->V,W; V->C,H; W->D,H; H->A.
Put exp(-t_UV)=exp(-t_UW)=177/200, gamma_H=1/2, other survivals 1/2.
It displays AC|BD and AD|BC. H carries only A, so independent/common laws
agree. Each selected tree has internal survival 177/200, giving

\[
p_D=(59/200,141/400,141/400)=p_T.
\]

Add its inert J0 bigon above B. Both states now have the same two control IDs,
the same available J0=0/J0=1 menu, and equal gene laws in each row, but different
Q and S. Both have g=1/2 and the shared original edge floor tau=log(10/9);
choose the remaining triangle survivals 1/2 and the bigon survivals 1/2,1/4.

For n=4, CF equality is equality of the entire UNROOTED gene-topology law.
For any finite number of fresh loci, even choosing the next available row
adaptively, the complete experimental transcript laws are equal: induction
uses the same conditional next-observation law for each row. Any procedure
required to choose one of the two differing targets has worst-case error at
least 1/2; a sound procedure can abstain. Infinite exact knowledge of the
two row laws also fails to identify Q. This does not assert equality of rooted,
ranked or metric gene laws, or failure of every possible menu.

**Admission.** Both base graphs are binary level-one galls with hybrid child
cut edges and an explicit outer-leaf embedding. Pendant bigons preserve that
embedding. A strictly decreasing node-age assignment along the DAG and a
positive population size N_e chosen to realize each coalescent length gives
a chronological realization. Different edge populations permit the triangle's
unequal coalescent path sums; common population size is not assumed. The
independent review gives explicit ages and sizes. `structural_checks()` checks
degrees/LSA/cut children; planarity is established by this fixture proof.

### 4.2 Exact history criterion and minimum synchronization set

**Theorem.** Under the declared cut-child/positive-finite model, the ordinary
partially forced NMSCind and corresponding NMSCcom row have equal full sampled
ancestral routing/coalescence history laws iff every unfixed hybrid has d_h<=1.
More generally, among controllers that persistently synchronize a chosen set
of additional sites, the unique inclusion-minimal set for that history law
is M. Exact emulation uses the original parental probabilities independently
at its synchronized sites.

**Sufficiency.** Pre-generate independent common-parent bits and common
coalescent randomness. At a fixed/synchronized site the histories route
identically. Every lineage carries a nonempty sample-label block; blocks merge
but never split, and a lineage cannot revisit a vertex in a DAG. At a site with
at most one descendant copy there is at most one choice event. Couple its
sole natural bit to the unused common bit. All routing and coalescent events
then agree pathwise, including zero-visit sites.

**Necessity.** If an unfixed unsynchronized h has d_h>=2, every descendant
copy must cross its child bridge, regardless of other fixed controls. There is
positive probability of no coalescence below h: pre-generate routing seeds,
and bound the integrated total merger hazard by
binom(d_h,2) times the finite sum of below-h edge lengths. All d_h copies then
arrive separately. Under independent inheritance their mixed-parent routing
probability is 1-gamma_h^(d_h)-(1-gamma_h)^(d_h)>0. Under common inheritance
it is zero. Their history laws differ. This argument applies separately to
every omitted site, proving uniqueness of the minimal set.

This is necessity for the full ROUTING history. An observation map can erase
this difference, so necessity for gene marginals/support is not inferred.
At fixed n=4, arbitrarily many admitted bigons can lie above the AB clade,
all with d_h=2. Therefore no n-only bound on this history-emulation actuator
cost follows from passive quartet normalization. Those same bigons need not
be necessary controls for support recovery.

### 4.3 Exact gene-law compiler at every finite size

For each nominal row/locus, draw independent original-probability bits at M,
persistently force them and the original row bits, and leave all remaining
sites natural. The pathwise proof above yields equality of COMPLETE history
laws, hence every measurable gene observable and its fresh-locus product law:

\[
\mathcal L(G_{\mathrm{compiled\ ind},e})
  =\mathcal L(G_{\mathrm{com},e}).
\]

This holds for arbitrary finite n, r, levels, blobs and sampling multiplicities.
It changes the original passive independent law. Exact original-weight emulation
requires those weights; using other interior weights emulates their corresponding
common law instead. A graph-free sufficient program synchronizes all unfixed
original IDs. `sample_identifier_environment` needs only ID/parent/probability
maps. `compile_row` also uses a Network to verify/select a smaller site set.

The minimum M and sharp worst-case k=r-f hold for history emulation under this
controller class. They are not an optimum over all biological interventions.

### 4.4 Support recovery needs only one extra random bit

For the SUPPORT objective, we can weaken exact emulation. At every unfixed site
in M, use the SAME fresh fair bit B per locus and force all lineages accordingly.
Leave the <=1-copy sites naturally independent. This is a correlated distribution
of global switchings, generally different from the original common product law.
The coin is independent of natural singleton-site choices and coalescent
randomness; the prepared global switching is independent of that coalescent
randomness. Coins are fresh and independent across loci.

**Theorem.** A compatible pair-hitting partial menu together with this program
has the same guaranteed supported CF contrast

\[
\Delta=g(1-e^{-\tau})
\]

for each original supported quartet in at least one row, and zero ideal contrast
for every absent quartet in every row. This assumes 0<g<=1/2 for natural
free-parent marginals, the inherited two-switch sufficient-cylinder theorem,
at most two original displayed resolutions per quartet, and switched internal
quartet lengths >=tau>0. An original edge floor tau is sufficient.

**Proof.** Pre-generate natural singleton-site bits. Together with the shared
external coin they define a global switching s. Conditional on s, the gene
process is the displayed-tree MSC. For ANY switching distribution D_e,

\[
p_{e,q,i}=\beta_{e,q}+R_{e,q,i},\quad
\beta_{e,q}=\tfrac13 E_{D_e}e^{-\ell_{s,q}},\quad
R_{e,q,i}=E_{D_e}[1\{T_s|q=i\}(1-e^{-\ell_{s,q}})].
\]

An originally absent resolution has R=0. Because at least one original
resolution is absent, min_i p_i=beta. Correlation cannot create a displayed
topology outside the original support. For an originally supported resolution,
choose a sufficient cylinder fixing <=2 bits. A compatible covering row forces
at least one of its two required bits, leaving at most one free required bit.
That bit has the required-parent marginal >=g: 1/2 at a synchronized site,
or the natural floor at a singleton site. Thus the cylinder probability is >=g
without assuming independence across hybrid bits. For a singleton certificate,
pair compatibility supplies a compatible row and its free bit already has
probability >=g; a zero-bit certificate has probability one. The internal
length floor gives R>=Delta in the covering row. QED.

Arbitrary finite sizes are covered by this proof. At r=0 use one tree row; at
r=1 use a free row or both endpoint rows, as appropriate to the declared menu.
The r>=2 pair criterion is not silently applied to a nonexistent pair.

Each nominal program has <=2 additional actuator vectors: all synchronized
sites set to zero, or all to one. It needs one fresh external coin, or none if
M is empty. Natural singleton sites may still generate many total routing
vectors. There is no 2^k actuator-repertoire requirement for this support-only
protocol. Full-history emulation in Section 4.3 DOES generally use 2^k possible
completions; the two results must not be conflated.

The inherited m_g(r) and 2r-2 counts remain constructions/optima in their ORIGINAL
menu contract. This correlated controller is a stronger resource. Their lower
bounds do not establish global optimality over arbitrary correlated programs.
Fully fixed optimized binary covering arrays remain a separate, already-known
alternative giving occurrence one.

### 4.5 Calibration, finite confidence and the decoder

The existing `robust_support.Contract` requires exactly these cross-row facts:
absent contrast zero everywhere and supported contrast >=Delta somewhere.
For rowwise total variation error <=epsilon, observed absent/present bounds
are 2epsilon and Delta-2epsilon. For Huber contamination eta they are eta and
(1-eta)Delta-eta. Conservative valid gates are

\[
\epsilon<\Delta/4,\qquad \eta<\Delta/(\Delta+2).
\]

Let d be the minimum positive threshold separation across rows. The inherited
fixed-prefix sufficient locus count is ceil(8 d^(-2) log(6mB/delta)) per row
for B uniformly protected quartet queries, with the original provider/decoder
contracts. Its anytime implementation uses the published prefix-uniform radius
rather than reusing a fixed-time bound after arbitrary repeated looks.
No independence among quartet restrictions from the same gene is assumed.

Known-order sparse recovery or the existing joint/order-free decoder can consume
the complete certified masks. An unresolved query must abort/abstain; returning
only the supported bits that happened to pass a test is unsound. This packet
reuses those tested interfaces, rather than introducing another decoder.

**Control-error extension.** Suppose the implemented locus can be coupled to
the ideal controlled locus so they agree whenever all relevant actuator events
succeed, and P(any failure)<=nu_e. Then TV(actual_e,ideal_e)<=nu_e. With an
additional TV observation error epsilon_obs, use epsilon_e<=nu_e+epsilon_obs
(capped at one). A calibrated per-site failure bound yields nu_e<=sum_h nu_eh
by the union bound, without independent failures. Many controlled sites can
therefore consume the entire gap budget. Failure depending on the genealogy
does not automatically give Huber contamination: TV is the justified bound.
Each per-site failure bound covers any relevant failure during the ENTIRE
locus, not just one lineage's actuation attempt.
No failure rates are assumed or measured here; they remain inputs to a usable
experimental contract. For exact-law matching, random-bit law errors must also
be bounded jointly, rather than merely matching its one-site marginals.

### 4.6 Costs and normalization interface

| Quantity | Exact common-law compiler | Support-only shared-coin compiler |
|---|---|---|
| Nominal experiment programs | Inherited m | Inherited m |
| Sites forced per locus in a row | f+k | f+k |
| External random draws | k independent site draws | <=1 fair coin |
| Additional actuator vectors per row | Up to 2^k | <=2 |
| Natural singleton sites | May remain free | May remain free |
| Original common product-law match | Yes, with original weights | Generally no |
| Displayed-support gap Delta | Transferred | Proved directly |

Runtime generation is linear in emitted controls/RNG calls. Rational denominator
bit complexity is an additional arithmetic cost. Exponential possible settings
do not imply exponential sample counts; marginal-law concentration applies
without observing every setting. A hardware system requiring preconfigured
settings has a different cost from an online bit controller.

Passive CF/Q/S normalization can discard original hybrids, descendant maps,
length floors and intervention identities. A controlled reduction needs a
verified map of original interventions and their response laws. This packet
works on original IDs and therefore does not depend on an unproved control-aware
normal form. It neither upgrades the passive normalizer to joint preservation
nor substitutes its reduced r for the original actuator count.

## 5. Conclusion and exact completion register

| Obligation | Evidence | Status | Remaining premise / next action |
|---|---|---|---|
| Exact intended master: optimal controlled Q/S recovery, all finite admitted networks | Sections 2-3 | MASTER IN PROGRESS | Classify other menus, stronger gene observations and practical controls |
| Governing inheritance/anomaly prior | Section 10, bibliography | Checked for this bridge | Historical novelty unestablished |
| Ordinary r=2 menu universal unrooted-topology recovery | Section 4.1, actual competing states | UNIVERSAL CLAIM REFUTED | Other menus/observables not refuted |
| Full-history emulation criterion/minimum site set | Section 4.2, independent review | COMPONENT COMPLETE, hand proof | Minimality is for histories, not marginalized gene laws |
| All-size exact law compiler | Section 4.3, coupling review | COMPONENT COMPLETE, conditional controls | Requires persistent forcing/unchanged dynamics |
| One-coin support compiler and robust bridge | Sections 4.4-4.5, exact tests | COMPONENT COMPLETE, conditional inherited structure | Scientific floors and actuator accuracy need verification |
| Control-aware normalization | Section 4.6 | Open | Prove response-family preservation, not only passive CFs |
| Minimal gene/support actuator/program costs | Prior full arrays + new bounds | Partially classified | Compare arbitrary correlated designs and restricted controls |
| Publication/formal/physical verification | Reviews, checks, manifest | Research packet available | No Lean proof, external review or biological actuation |

## 6. Top-down analysis

Start from the desired support answer. The decoder needs a complete support mask.
The provider needs zero absent contrast and a uniform present gap. The controlled
population process must establish those facts. Switch occurrence is only one
ingredient; independent lineage routing can change the CF interpretation.
Synchronizing the relevant sites supplies the missing bridge.

## 7. Bottom-up analysis

Begin with lineages carrying disjoint sample-label blocks. A single-copy site
cannot witness independent/common disagreement. Multiple copies can split
between parents. Preventing that splitting gives a shared switching and a tree
MSC mixture. A sufficient two-bit cylinder plus a compatible partial row reduces
the required random event to one bit. This is why a single external coin across
the other sites retains the support guarantee.

## 8. Middle-out synthesis

The interface is the row-law support gap Delta. Above it sit confidence and
decoding; below it sit lineages, controls and population dynamics. Exact law
matching is sufficient but stronger than required. The support-only compiler
reduces randomness/configurations without claiming to preserve all observations.
The maximal normalization lesson is to declare which interface is preserved
before calling a reduction complete.

## 9. Glossary

CF: three gene-quartet probabilities on a four-taxon set. Displayed support:
quartets/splits appearing in at least one switched species tree, not every gene
topology with positive probability. Row: a nominal intervention program.
Synchronization: a persistent shared parental setting for every lineage at a
hybrid during a locus. History: routing plus coalescence, stronger than the gene
tree after routing is marginalized. g: free-parent probability floor. tau:
switched internal quartet length floor. Delta: certified supported CF contrast.
Abstention: no certified biological answer under current information.

## 10. Bibliography and immutable dependency ledger

Primary sources:

- Allman, Banos, Rhodes (2019), NANUQ, Algorithms for Molecular Biology 14:24,
  DOI [10.1186/s13015-019-0159-2](https://doi.org/10.1186/s13015-019-0159-2).
  Known 3_2-cycle formula/anomaly; arXiv:1905.07050 PDF was inspected, including
  its formula and tree-like parameter analysis. This is prior work.
- Fogg, Allman, Ane (2023), PhyloCoalSimulations, Systematic Biology 72:1171-1179,
  DOI [10.1093/sysbio/syad030](https://doi.org/10.1093/sysbio/syad030).
  Official article inspected for independent/common/correlated inheritance.
  No new correlated-inheritance model is claimed here.
- Rhodes, Banos, Xu, Ane (2025), Identifying circular orders for blobs in
  phylogenetic networks, DOI [10.1016/j.aam.2024.102804](https://doi.org/10.1016/j.aam.2024.102804).
  Original circular-order/support relation is inherited, with exact scope
  checked in existing ASTRA-OBS. Its 2024 DOI date is not the volume's year.

Pinned Commons dependencies:

- ASTRA-OBS all-level [PROOFS.md](https://github.com/Sodelin/Research-Commons/blob/e3b05f464a486274824ddcd9f0566b760cab3a0e/research/2026-09-30-astra-alllevel-observation-1034z/PROOFS.md),
  Sections 2,4,6,7. Two-switch premise and fully fixed recovery retain attribution.
- CONTROL-MENU [REPORT.md](https://github.com/Sodelin/Research-Commons/blob/e3b05f464a486274824ddcd9f0566b760cab3a0e/research/2026-09-30-control-menu-continuation/REPORT.md).
  Executed menu module blob a870e80a51e721bd7e06d2d5ee9561f276232f9a.
- Robust provider [packet](https://github.com/Sodelin/Research-Commons/tree/f6134c256bf24c73c624b562841622789b200a4c/research/2026-09-30-robust-statistical-recovery).
  Exact executable dependency hashes are in this packet's manifest.
- Astra CF recurrence, cf_normal_form.py blob 4847e9f104be89d65b0aa41f508a5787036c3d1f,
  ASTRA-BIO-PROVER-20260930-1612Z. Algorithm credited; stdlib reimplementation here.
- ASTRA-JOINT-LAW-20260930-1744Z acceptance and its checkpoint at
  b1aaeccead56820077674d745d661ff5cbefe672. That owner's passive full-joint work
  is distinct and not an assumption for our compiler proof.
- Fresh publication read: [Astra joint-law delivery](https://github.com/Sodelin/Research-Commons/blob/881e33a7e6d205021369300307a068a747160c76/communications/2026-09-30-astra-joint-law-1744z-delivery.md),
  packet 653ed43e1a9eab2b359f028dc0bd109db62fbbf8. It reports forest-kernel
  compression, a metric obstruction and exact tests while leaving source
  realizability/master closure open. This is an observed peer delivery, not our
  independent review of those proofs. Our controlled-response contract stays
  separate; neither packet promises preservation of the other's interfaces.

## 11. Process-integrity assessment

We read source priors and current ownership before allocating work. Three internal
agents independently attacked the obstruction, coupling and implementation.
The first capture was published before expansion. Current-main non-force updates
preserve peer work; publication/readback evidence is recorded separately.
The original provider-only example was strengthened with an actual equal-law
controlled competitor; the broader negative conclusion relies on that new pair.

The code audit found inconsistent sample declarations and unchecked direct CF
parameters. Both were corrected and independently replayed: undeclared samples,
invalid survivals/float parameters and invalid expansion caps now reject.
This is an internal audit, not external peer review. PRISMA/AMSTAR-style
traceability motivates the ledger; a mathematical packet is not a systematic
clinical review and no checklist score or GRADE rating is assigned.

## 12. Inference-robustness assessment

Exact arithmetic separates the strict anomaly from rounding. An independent
tree-edge mixture cross-checks the first-merger recursion. Tests include asymmetric
inheritance, zero-copy declarations, n=4..7, r=1..4, both noise models and
low-data abstention. Law matching and support matching are tested separately:
50 correlated readouts differ from the product common law while support remains
correct. The all-size claim rests on the coupling/cylinder proofs, not these
finite examples.

No effect-size meta-analysis is appropriate for deterministic proof obligations.
Important remaining sensitivities are persistent all-lineage forcing, fresh
locus independence, unchanged coalescent dynamics, complete control IDs, correct
copy counts, source admission, and the quantitative gap promises. Control
failure calibration can be incorporated via the proved TV coupling bound.

## 13. Zotero / Obsidian integration

`references.bib` is import-ready; no live Zotero import was performed. Keep this
packet linked to CONTROL-MENU, ASTRA-OBS, the robust provider, the passive
normalizer and Astra's distinct full-joint task. Related concepts are controlled
response families, observation maps, sufficient cylinders, coupled randomness
and decision-specific preservation. The defunct separate notebook is not used.

## 14. Appendix: execution and unresolved attacks

`checks.py` executed 48 formula comparisons and 2,184 partial-row/quartet cases
with 6,552 law comparisons on 12 prescribed n=4..7 triangle/bigon fixtures.
It verifies the equal controlled competitor, repaired provider mask 1, erroneous
mask 6 under deliberately violated provider premises, TV/Huber integration and
low-data abstention. Law/count fixtures are analytic; 40,000,000 is a rational
count fixture, not a report of simulated or collected genes.

`correlated_checks.py` executed two source-admitted cherry extensions, n6/r3
and n7/r4, both single-control and partial-array menus: 420 row/quartet readouts,
840 conditional tree-oracle comparisons and 100 menu/quartet support equalities.
The minimum supported maximum contrast attained 1/4. Twenty-four prescribed
switches were used as an oracle; no general network census was launched.
The independent audit additionally checked 840 original-fixture comparisons
and 123 asymmetric-parameter comparisons. These counts overlap conceptually
and are not combined into an evidence-strength score.

Next attack: classify the response fibers of ordinary independent-inheritance
partial menus beyond this two-state negative pair, then minimize controls for
the OBSERVED target rather than full routing histories. Establish whether a
control-aware source normal form can preserve those fibers. Practical historical
actuation and passive stronger-observation classification remain separate open
obligations, not a single remaining gap.
