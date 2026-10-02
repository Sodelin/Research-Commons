---
title: "Research Commons methods and tools audit"
author: "GPT-6.1 Sol, distinct methods/tools audit lane"
coordinator: "dot"
date: "2026-10-02"
status: "Local report prepared for authorized open-research publication; no publication receipt yet; no new G1–G7 closure claim"
---

# Decision brief

The most useful change is **certificate-first computation using existing local tools**, rather than adding a large general-purpose system and repeating exhausted searches. Exact algebra is already fast for several current components; giant Lean kernel reductions and the missing scientifically calibrated observation channel are the harder boundaries.

Three bounded pilots were completed on synthetic/public inputs:

1. SymPy → explicit polynomial/rational certificate → pinned Lean check, including corrupted-output rejection
2. SymPy DomainMatrix/FLINT exact arithmetic and Arb interval smoke
3. A local aligned-FASTA → estimated quartet-label adapter that preserves locus units, validates its input and abstains without a calibrated G6 observation channel

No publication, paid service, account setup, credentials, security changes, external dataset upload or personal genomic input was used during these pilots. Work ran on the dot cloud filesystem. Original Lean source bytes, successful objects and existing research files were preserved. Coordination with the formalization worker avoided legacy heavy builds.

# 1. What the existing workflow actually did

This audit inspected receipts, source scripts and checkpoint claims. It did not independently re-prove the mathematical arguments or rerun their large control suites.

| Lane | Observed method and role | Evidence boundary |
|---|---|---|
| G1/G2 | Source graph/forest/register semantics, exact symbolic controls, source-critical hand arguments, targeted Lean premise/countercontrol modules | Conditional source-faithful components; not arbitrary DNA calibration or a whole-program build |
| G3 | Exact rational/polynomial identities, modular rank/resultant certificates, finite normal-form controls, analytic hand proofs; Wolfram for bounded eliminations | CAS/finite controls do not prove global all-factor attainment, input-effective factor bounds or arbitrary-cap recognition |
| G4 | Exact Fraction forest kernels, canonical labelled tree/forest states, cached merger skeletons, full-forest quotient/ordering controls, targeted polynomial Lean statements | Finite controls corroborate hand components. Same-L arbitrary-chain stopping remains a separate open endpoint |
| G5 | Original-source graph census/switchings, chronological support and route proofs, exact block tests; a small abstract bounded-domain Lean lemma | Exact calendar law/support is the input. The source chronology/stochastic law is not a sequence estimator |
| G6 | Exact rational forest/channel controls, local Z3 QF_NRA constraints, effective closure/robust-fiber hand construction | Declared finite-certification theory; no executed complete catalogue, calibrated DNA adapter or integrated inference engine |
| G7 | Exact original graph enumeration/census, same-source symbolic laws, response-rank/design controls and hand CAD/extraction procedures | Fixed source/profile controls and theoretical procedures are distinct from a universal executed optimizer |

The G4 scripts already use `functools.lru_cache` on canonical forest states and exact `fractions.Fraction` probabilities. Recommending memoization without checking this would merely rediscover existing practice. G3's current local small algebraic certificates already finish in subsecond time. The parent reported 0.07s for an independent rational/binomial global-obstruction checker, 0.58s for source constants and 0.21s for an exact algebraic-instance predicate; these are observed executions, not comparisons against identical hand work. The 0.58s source timing is also recorded in the adjacent cap-seven checkpoint.

## Lean resource evidence

Pinned source: Sodelin/Work-on-Samuel-Alexander-Research- commit `e2502c82ab9a77c00543932f775a71e5374221f7`; Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The exact terminal receipt has 96/114 successful original included modules, five resource-blocked certificates and thirteen unchecked dependents. All 117 top-level source files were hash matched, with three original exclusions retained. The official 8690-file mathlib cache completed. The original consolidated checkpoint and CanonicalTheta lack a complete fresh run in this lane. The final raw all-level NANUQ source theorem was absent from the pinned source.

| Actual attempt | Elapsed | Memory evidence | Outcome |
|---|---:|---|---|
| ThetaCertificate6 first run | 300.128s | Bounded timeout | exit124, UNKNOWN |
| ThetaCertificate6 later run | 576.025s | Formalizer reports process near the 9.7GiB cloud ceiling | external SIGKILL, exit−9, UNKNOWN |
| ThetaCertificate6 bounded retry | 436.878s | `-j1 -M6144`, explicit `memory_exception` | exit−6, resource failure |
| ThetaSupportCertificate3 | 5.690s | `-j1 -M2048`, explicit `memory_exception` | exit−6 |
| ThetaSupportCertificate4 | 10.497s | same | exit−6 |
| ThetaSupportCertificate5 | 11.597s | same | exit−6 |
| ThetaSupportCertificate6 | 5.885s | same | exit−6 |

The 96 successful module durations sum to 492.153s. This is **a sum of per-module measured durations**, excluding installation, caching, orchestration and failed attempts, not an end-to-end wall-clock benchmark. The largest successful checks were ThetaCertificate5 195.187s, ThetaArmMetric 76.513s and ThetaCertificate4 54.023s.

The blocked sources use concrete `checkTemplate`/`checkSupport` evaluations with `decide +kernel`. Support scans combine every gap pair, candidate anchor pairs, switching edges and terminal paths. These are computational proof-reduction workloads, not numerical optimizer failures. More RAM or identical retries do not establish completion. A replacement needs a semantics-preserving proof decomposition or verified checker; an external TRUE table alone is insufficient.

The separate aggregate receipt for eight new G components is exit-zero with explicit standard axiom lists. Two subsequently compiled G4 components were confirmed separately by the formalization worker, with their local logs/objects present. This audit does not silently upgrade the eight-module aggregate to a new aggregate receipt.

## CAS/tool-output failures

The original G3 checkpoint is more precise than the initial handoff: full nested real QE at cap four timed out at **20 seconds**; the cap-seven full-support symbolic resultant/rank extraction timed out at **25 seconds**, with a 600MB allowance. Both are UNKNOWN, not empty loci, nonattainment or solver proofs. No cap-eight QE was run there.

A cap-six full integer coefficient matrix export first encountered a pivot-selector error and then middle elision in tool output. What was retained is a complete 35×35 modular minor, determinant527 mod1009, row degrees and an executable integer-matrix construction recipe. Do not call the elided output a successful full integer-matrix serialization.

**Recommendation:** persist complete machine artifacts locally, hash them and summarize small metadata in tool output. For elimination/rank certificates, preserve coefficient domain, monomial order, denominator conditions, pivots, modular prime and the exact recovery/check procedure. Tool rendering is not an artifact-transfer guarantee.

# 2. Tested availability, rather than catalog presence

| Route | State on this host, 2026-10-02 | Scientific/method fit |
|---|---|---|
| Python 3.12.14, SymPy1.14.0, NumPy2.3.5, SciPy1.17.0 | Existing, importable | SymPy/Fraction for exact algebra; floating SciPy fit is candidate generation only |
| NetworkX3.5 | Existing isolated dependency under `/workspace/shared/g6-review-2005z/deps`, import tested | Source graph/census operations, not a coalescent observation channel |
| Z3 4.15.3 | Existing in the same isolated dependency directory; import and synthetic UNSAT smoke passed | Bounded encoded feasibility/countercontrols; G6 already has11 QF_NRA checks with10s per-query limits among11626 controls |
| Lean4.33.1/Lake/CaDiCaL/leanchecker | Existing official runtime outside default PATH; compiler operational | Kernel certificates and explicit trust/axiom inspection; no full-program completion implied |
| Wolfram evaluator | Synthetic algebra invocation passed; version15.0.1; reported kernel computation0.004434s | Independent exact CAS route. That kernel timing excludes connector latency |
| Wolfram context endpoint | Invocation returned internal error | Per-endpoint failure; does not imply evaluator failure |
| python-flint0.9.0/Biopython1.88 | Pinned PyPI wheels installed only into this audit's local `deps`; imports and pilots passed | Exact integer/rational/interval arithmetic; standard sequence/tree format and small phylogenetic operations |
| NGS Workbench | Skills discovered, but no compute-target/catalog/readiness/planning/run APIs exposed in this tool registry | Executable backend readiness unestablished; do not promise a run or configure SSH infrastructure |
| PubMed/alphaXiv/ClinicalTrials.gov | Relevant exposed research endpoints; no invocation required for these computation pilots | Literature/evidence retrieval, not raw sequence analysis |
| SageMath/Singular/cvc5/Logos/Walnut/biological ARB | No located executable/default module or exposed connector; not installed or piloted | See short fit comparison below; absence from PATH alone was not treated as a final absence test |

A concrete missed-route lesson: Z3 was absent from the default interpreter and PATH, yet present in a prior lane's isolated dependencies and working. Reuse a documented import path before proposing another installation.

The probable product name is **Rosalind Workbench**: the official August28,2026 OpenAI article includes NGS Analysis Workbench and sequence/alignment viewing. This is an evidence-based name resolution, not certainty about the user's utterance. It is distinct from commercial ROSALIND.bio and the Rosalind programming-exercise site. The official NGS examples cover FASTQ QC, RNA-seq and single-cell workflows; none supplies the missing source-specific G6 mutation/time channel. [Official OpenAI overview](https://developers.openai.com/blog/rosalind-workbench)

# 3. Pilot measurements and certificates

## Pilot A: local algebra → independent Lean certificate

`export_certificate.py` asks SymPy for coefficients of a synthetic cubic, emits an explicit Lean theorem, and separately validates a rational bracket for a nonnegative real satisfying x²=2. Arb/SymPy values are proposals, not axioms in the Lean proof.

- Generation: 0.0409s
- Successful check: 1.7315s, `-j1 -M2048`, exit0, new object present
- Cumulative child peak through the successful check: 1,713,792KiB, approximately1.635GiB. This includes compiler import/runtime overhead and the prior tiny `--version` process; it is not a measured per-tactic allocation
- Both declarations print only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, `ofReduceBool`, custom oracle or native-decide axiom
- Changing a generated coefficient from3 to4 yields exit1, an unsolved goal and no object. Its diagnostic contains `sorryAx`, and is explicitly rejected
- Initial512MB checks failed with `memory_exception` at0.648s/0.707s. A2GiB check then revealed a missing explicit Real import; the final source fixes that import and supplies explicit positivity products. Both failure receipts/logs are retained

This validates the **export/check contract**, not any G theorem. It shows why success must require exit0, current-source object provenance and an accepted axiom list: an error run can still print a theorem containing `sorryAx`. Source-polynomial G3/G4 components already use this general route; reusing their receipts is preferable to duplicate builds. [Lean validation/trust boundary](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)

## Pilot B: exact representation substitution and intervals

Three repeated calculations per method, same synthetic seeded35×35 integer matrix; all determinant hashes agree. Only operation timing is compared, not Python startup, installation or total workflow time.

| Exact determinant method | Median | Process max RSS |
|---|---:|---:|
| SymPy Matrix Bareiss, Python ground types | 0.193198s | 49,548KiB for that entire benchmark process |
| SymPy DomainMatrix, Python ground types | 0.013961s | same process |
| SymPy DomainMatrix, FLINT ground types | 0.000708s | 63,872KiB for that entire benchmark process |

Matrix Bareiss in the FLINT-ground process was0.219071s, so merely setting the environment does **not** speed every high-level algorithm. Use a domain-aware exact representation. The input determinant has292 digits; digest `e6a0f69e9dcb8ede8f687641f481d4c5a8b78228f6b7a9cb481f30dc80149100`.

Arb at128bits returned `[1.4142135623730950488016887242096980786 +/- 3.69e-38]`; exact rational endpoint squares straddle2. Pilot A validates the bracket independently. Arb's rigorous library arithmetic is still a trusted external implementation unless its output is converted to a Lean-checkable certificate.

**Expected benefit:** exact dense matrix/rank/resultant subcalculations can avoid slow generic expression arithmetic. **Measured benefit:** only the synthetic determinant times above. No current G3 elapsed-time reduction or general speedup factor was measured. The real cap-six coefficient ring/degree/sparsity must be benchmarked before substituting in its pipeline. [SymPy DomainMatrix](https://docs.sympy.org/latest/modules/polys/domainmatrix.html), [python-flint/Arb](https://python-flint.readthedocs.io/en/latest/)

## Pilot C: safe G6 observation-contract adapter

`g6_observation_adapter.py` uses Biopython on designed aligned-FASTA fixtures. It performs uncorrected-identity NJ and100column-bootstrap replicates per resolved fixture, exports labels plus provenance, and keeps one independent-observation unit per locus ID. It does not analyze raw FASTQ, align unaligned reads or implement a validated substitution model.

Nine engineering controls pass in0.6000s, peak process RSS32,984KiB:

- Each of three designed quartet split fixtures is recovered twice
- A zero-information star fixture emits UNRESOLVED
- One identical same-locus duplicate is ignored:7 locus units, not8 records or2048 alignment columns
- Different measurements at the same locus are rejected until a joint-outcome schema is supplied
- Empty input, duplicate taxon IDs, missing taxa and unsupported ambiguous bases are rejected
- Final G6 target output is explicitly ABSTAIN

The predeclared alphabet includes UNRESOLVED. A union-Hoeffding TV radius applies only **conditionally to iid draws of the estimated-label channel**, for one prespecified profile. With7 units the bound is1, hence uninformative. These deterministic fixtures were not an iid molecular/coalescent simulation, so the pilot does not validate statistical coverage.

The output sets known sequence-to-topology channel=false, calibrated beta=null, calendar bins=null and Lean-checked=false. Column bootstrap support is not a proved TV error bound and is never substituted for beta. Related sites share a genealogy; they cannot be counted as independent target-law draws. An empirical site-pattern or estimated-tree confidence set is not a calendar-law confidence set.

**Expected benefit:** standard parsing, input validation and a locus-preserving schema remove preventable ingestion/pseudoreplication errors. **Measured benefit:** the synthetic format/control pass and timing only. **Scientific validation still required:** assay/locus definition, linkage/recombination treatment, missing-data channel, mutation/substitution model, coalescent/clock calibration, source-mechanism fit and simultaneous/adaptive error control. There is no certified DNA→G5 or DNA→G6 target pipeline here. [Biopython phylogenetic formats/operations](https://biopython.org/docs/latest/Tutorial/chapter_phylo.html)

# 4. Short catalog: when other existing tools would genuinely help

| Tool/route | Good substitution | Why it is not a current closure shortcut |
|---|---|---|
| SageMath + Singular | Exact polynomial domains, Gröbner/elimination/ideal-membership workflows if expression growth becomes a demonstrated bottleneck | Larger installation not needed for the passed subsecond local certificates. Ideal elimination alone does not enforce real positivity, finite-source integer counts or arbitrary-factor bounds. Return membership identities/Bézout witnesses for Lean checking. [Official interface](https://doc.sagemath.org/html/en/reference/interfaces/sage/interfaces/singular.html) |
| Z3 | Reuse existing QF_NRA or finite combinatorial model-finding route with explicit domain constraints and UNKNOWN propagation | An UNSAT result is not a Lean theorem; general mixed integer/nonlinear real formulas are not a guaranteed complete procedure. Do not erase original-source constraints. [Official arithmetic guide](https://microsoft.github.io/z3guide/docs/theories/Arithmetic/) |
| cvc5 → CPC → Logos | Potential proof-producing SMT route with formal SMT-LIB semantics, especially bounded Boolean/arithmetic constraints | Current docs identify a Lean-written checker, synchronized CPC signature/version pins, safe-build fragment and incomplete/trust-step exclusions. Not installed or tested here. A verified checker verdict is not automatically an imported theorem about our graph semantics. End-to-end translation and actual returned trust status must be validated. [Current official CPC/Logos docs](https://cvc5.github.io/docs/latest/proofs/output_cpc.html) |
| Lean bv_decide/CaDiCaL/LRAT | Existing fixed-width Boolean/bitvector goals after a proved faithful encoding | Original Θ proofs are list/rational kernel reductions, not automatically bitvector problems. Official validation docs distinguish native reflection's larger trusted base; do not substitute it into a strict standard-axiom endpoint without an explicit trust decision. [Official implementation](https://lean-lang.org/doc/api/Std/Tactic/BVDecide.html) |
| Arb vs ARB | Arb: rigorous numeric enclosures for root/sign candidates; biological ARB: alignment/tree workflows | Different tools. Arb enclosures need completeness/denominator handling for a global claim. Biological ARB outputs are inferred sequence phylogenies, not exact stochastic calendar laws. [Biological ARB manual](https://download.arb-home.de/documentation/arb.pdf) |
| Walnut | Automatic-word/finite-automaton combinatorics when the theorem has an automatic-sequence encoding | DNA sequence inputs are not automatically automatic words; arbitrary real hazard/signature problems do not fit by naming similarity. Not installed/piloted. [Maintainer repository](https://github.com/firetto/Walnut) |
| NGS Workbench | Traceable approved QC/read processing and assay-matched standard workflows when live backend APIs and scientific inputs exist | Orchestration does not supply the G6 mutation/time observation theorem. Installed skills do not prove target/runtime/approval readiness |

Earlier scope comparisons for PhyloNet, MSCquartets, RevBayes, SINGER and BayesFlow/LF2I already exist in the cross-domain bridge report; they were not rediscovered or re-piloted here.

# 5. Precise next actions

1. **Adopt the certificate/receipt contract immediately for new exact algebra:** explicit inputs/domains, source and output hashes, complete local artifacts, Lean success/axioms/current object checks, known-corrupt rejection, runtime/RSS where available. Use focused imports. Reuse current G3/G4 receipts.
2. **Refactor the five legacy certificate workloads before another heavy build:** separate each concrete obligation, export small positive witnesses and negative classification evidence, memoize shared arithmetic by proved lemmas, or introduce a streamed verified certificate checker. First prove equivalence to original `checkTemplate`/`checkSupport` semantics and run one bounded small case. Do not overwrite the original source or certify an external answer table. The saved successful96 objects remain the baseline.
3. **Use DomainMatrix/FLINT selectively, not as a blanket setting:** pilot the actual coefficient domain and sparse/dense structure locally when the G3 worker identifies a slow algebraic substep. Modular nonzero rank certificates are valuable; modular zero alone is not a characteristic-zero vanishing proof. Preserve denominator and degree conditions.
4. **Make the G6 observation channel the next scientific deliverable:** select one narrowly declared biological observation experiment, retain independent loci/joint same-locus outcomes, and validate a known source-to-observation channel or conservative bound on synthetic data from that exact model. The current adapter is reusable engineering scaffolding and remains an abstaining prototype. Do not substitute protein-structure/disease-expression tools or molecular trees for missing calendar-law observations.
5. **Treat cvc5/Logos as the next conditional certificate route, not an installation checklist:** only pursue it if a concrete obligation is expressible in its verified fragment and existing certificate-first algebra cannot meet the endpoint. Check translation, version compatibility, returned completeness and axiom/trust status on a tiny public case before scaling. No new account/SSH infrastructure is justified by this audit.

No token accounting, hand-work timing comparison, universal tool speedup or whole-program completion is claimed. No publication was made by this audit lane. At00:16UTC the coordinator relayed the resolved instruction: open research/proofs/checkpoints may publish on Commons main, while product-specific implementation belongs only in the verified private repository. This report contains methods research and public/synthetic pilots, not a proprietary product implementation.

# 6. Alt-G and Samuel-transfer workflow: role split

Use one small **source-to-observation contract** per proposed transfer, rather than a universal engine: original source class; legal graph/state/register semantics; hidden versus measurable information; target; observation channel; exact/approximate status; independent units; effectivity/quantifier obligations; admissible certificate. This is a research interface, not a product design.

- **Hand proof owns the all-size mathematics:** prove the cross-domain construction really satisfies the biological/source premises, that restriction/gluing preserves one common source, and that the desired target is transported. Identify where positivity, calendar units, source finiteness and effective encodings are used. A weaker interface whose fields already assert the conclusion is not a generalization.
- **Computer algebra/model finding owns discovery and small evidence:** use existing Fraction/SymPy, the tested DomainMatrix/FLINT route and existing isolated Z3 to find legal exact witnesses, countercontrols and decomposition identities. Encode actual source constraints, not merely a convenient stochastic state model. Wolfram is a bounded independent CAS fallback on shareable inputs. Timeout/UNKNOWN stays UNKNOWN.
- **CLI owns reproducibility:** pinned inputs and tools, declared domains, deterministic seeds, job limits, dependency provenance, immutable complete artifacts, hashes, elapsed/RSS and explicit PASS/FAIL/UNKNOWN receipts. Resume unchanged successful objects and avoid identical exhausted retries. One manifest connects the hand statement, computational witness and exact Lean declaration.
- **Lean owns checked transport and finite certificates:** first formalize the precise contract and quantifier order, then source-admission, observation restriction, positivity and the algebraic/countermodel certificate. Prove equivalence to original definitions. Use small entry/row-operation lemmas and determinant transport instead of one giant expansion. Check exit0/current object/axioms together; external solver verdicts and error-run declarations are not proof.

For Samuel transfer, reuse each existing theorem according to its own pinned source, dependencies and actual verification receipt; do not imply fresh replay when only a historical receipt was inspected. The96/114 limit applies to the specific audited NANUQ formal-full baseline, not eligibility of the entire Samuel library. PairingCore/PairingGARG/PairingBridge and other Samuel tracks have separate source/verification receipts outside those114 modules, which this methods audit did not freshly replay. Within the audited NANUQ baseline, conditional AnchorComposition/CircularComposition facts can be components when the new source actually proves their hypotheses. Do not cite that baseline's CanonicalTheta, consolidated original checkpoint or absent final raw all-level source theorem as freshly established endpoints. The eight-component G aggregate and later G4 source-polynomial checks are separately scoped evidence.

A sensible first transfer packet has one source-instantiation theorem, one observation/target compatibility lemma, one exact countercontrol for a deliberately dropped premise, one small executable certificate and a Lean declaration/axiom receipt. Scientific observation/calibration remains an explicit obligation; the FASTA adapter does not discharge it. No new platform build is proposed.

# 7. Local evidence and replay

Audit directory: `/workspace/scratch/281dd7169401/methods-tools-audit-0002z`.

- `certificate-receipt.json`, `SyntheticCertificate.lean/.log/.olean`, `CorruptCertificate.lean/.log`
- `certificate-512mb-failure-receipt.json`, `certificate-missing-real-import-receipt.json`, preserved diagnostic logs
- `benchmark-python.json`, `benchmark-flint.json`, `benchmark_exact.py`
- `g6-adapter-receipt.json`, `g6_observation_adapter.py`, `synthetic-loci.json`
- `tool-inventory.json`; pinned local dependency directory `deps`

Replay commands, with no publication or external data transmission:

```sh
SYMPY_GROUND_TYPES=python python3 methods-tools-audit-0002z/benchmark_exact.py
PYTHONPATH=$PWD/methods-tools-audit-0002z/deps SYMPY_GROUND_TYPES=flint python3 methods-tools-audit-0002z/benchmark_exact.py
python3 methods-tools-audit-0002z/export_certificate.py
PYTHONPATH=$PWD/methods-tools-audit-0002z/deps python3 methods-tools-audit-0002z/g6_observation_adapter.py
```

Primary audited receipts:

- `/workspace/shared/lean-formalization/receipts/baseline-independent-completion.json`
- `/workspace/shared/lean-formalization/BASELINE-TERMINAL-PARTIAL-RECEIPT.md`
- `/workspace/shared/lean-formalization/receipts/VerifiedComponents-receipt.json`
- `/workspace/shared/g6-review-2005z/independent-results.json` and `independent_audit.py`
- `g3-boundary-resume-2124z/0003-neutral-resume-checkpoint.md`, `0004-exact-tail-checkpoint.md`, `cap6-modular-minor.json`, `CONCRETE-ALGEBRAIC-CAP7-NO.md`
- `g4-allcopy-2237z/obstruction-replay.json`, `placement-replay-resume.json`, forest/composition/tomography scripts
- `sol61-head-audit/checkpoint/CURRENT-G-STATUS-2310Z.md`, `LOCAL-INDEPENDENT-ACCEPTANCE-2357Z.md`

These paths point to local work artifacts and receipts, not public repositories or proof of peer receipt.
