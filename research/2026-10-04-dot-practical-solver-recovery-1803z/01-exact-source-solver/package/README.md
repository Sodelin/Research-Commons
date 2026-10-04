# Practical actual-source solver, 2026-10-04

Contributor: OpenAI dot, for Nolan's Research-Commons project. This is implementation and reproducible execution of previously accepted research. It does not claim a new general recognition theorem or Lean verification of the Python engine.

The runnable workflow takes finite declared exact unranked genealogy-law rows, searches the actual original-ID source class, returns one coherent admitted source or a justified finite-catalogue exclusion, recomputes the delivered certificate, and can distinguish a uniquely determined target from two source witnesses with different targets. A separate bounded search handles an incomplete hybrid registry with positive witnesses and honest UNKNOWN outcomes. The G7 design exporter now joins the original actual-source census and forest compiler to its accepted real-QE programme predicate.

## Install and run

Use Python 3.11–3.13 on Linux or another system supporting Python's POSIX interval timer. The tested environment is Python 3.12.14, SymPy 1.14.0, NetworkX 3.5 and Z3 4.15.3. Runtime dependencies are pinned separately from the preserved upstream requirements.

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python tests.py
python solver.py examples/hybrid-independent-sat.json --output my-run
python verify_certificate.py my-run/RESULT.json
```

For a general nonlinear exclusion, explicitly request a fresh reconstruction and same-backend replay:

```sh
python verify_certificate.py runs/nonlinear-shared-row-unsat/RESULT.json --replay-backend
```

The checker rederives the actual source constraints. A supplied false SMT query with a matching hash cannot replace them. Witness and rational contradiction checks remain enabled under Python's `-O` mode.

## Actual source and observation contract

The original source is a finite binary rooted DAG, with root LSA of all labelled taxon leaves, a literal undirected bridge below every hybrid, and an embedding with all taxa cofacial. Parallel original edge occurrences and incoming parental bits are preserved. There is no fixed level or blob-count restriction. For a COMPLETE registry of r original hybrid IDs and n≥2 taxa, the original finite census has V=2n+2r−1 and E=2n+3r−2. This is the accepted original binary census, not an unknown-size compressed-core bound.

All original survivals x_e and natural inheritance probabilities gamma_h lie strictly in (0,1). One original graph, inheritance mechanism and parameter assignment must fit EVERY supplied row. COMMON routes the whole current forest using one original-site bit; independent inheritance draws per CURRENT carried root. Original-ID forcing operates at the same source node. The compiler stores the entire joint frontier, so shared paths, current-root coalescence and common bits survive. Several quartet records from one locus are projected from that same gene tree jointly.

Clocks are freely positive and edge-specific. Every positive witness includes a strict calendar with contemporaneous tip age0: each internal vertex is one unit older than its oldest child. On an original edge, rate = −log(x_e)/duration is an exact positive real definition. Extra tied clocks, tied rates, metric readers and calendar-time outputs require their own actual source encoding.

Input probabilities and static random-program weights are exact integers or rational strings. Floating estimates are rejected. Rooted outcomes are child-order-quotiented binary trees; `unrooted_splits` records the complete nontrivial cut system of a gene tree; `joint_quartets` records a tuple of quartet cut systems from that one tree. Each law is normalized exactly. The current Python engine requires a nonempty total sample panel.

The displayed targets are computed by actual original complete switchings: either the union of NONTRIVIAL displayed splits or the family of whole co-occurring switching split systems. Pendant cuts are excluded. A union of splits is never substituted for a whole cut-system family. Engine taxon L_i is mapped to request taxon `taxa[i]`; original declared hybrid ID i maps to H_i with its ordered original incoming0/1 edges.

## Request interface

See the complete examples rather than inserting informal observations into the solver.

- `observation_kind`: `exact_unranked_law`
- `n`, optional n distinct `taxa`, and `registry: {complete: true, hybrid_ids: [...]}`
- `mechanisms`: a nonempty tagged subset of `common` and `independent`, chosen once per candidate source
- `task`: `find_source` or `identify_target`; the latter also declares `target_kind`
- `rows`: original taxon→copy-label sampling panels, one common readout, and the full exact finite probability law
- Each row has either `forced: {original_ID: 0_or_1}` or `program`, a finite positive rational-weight mixture of such deterministic rows. All operations retain the SAME source parameters
- `limits`: positive seconds, source-count limit and SMT milliseconds. A limit produces UNKNOWN

The solver never evaluates input probability strings as Python or symbolic code. Exact rational parsing and finite structured outcomes are used instead.

## Verdicts and certificate trust

`SAT_ONE_COHERENT_ADMITTED_SOURCE` delivers an actual admitted graph and positive rational/algebraic source assignment. The independent certificate path recomputes its complete joint law with exact SymPy arithmetic, its actual switching target and physical calendar construction. This is software exact-algebra verification using the inspected upstream compiler, not a proof-assistant theorem that Python or SymPy is correct.

`UNSAT_COMPLETE_KNOWN_REGISTRY` requires every admitted original graph and specified inheritance mode in the supplied complete census to be covered. Rational multiplier identities that force a nonzero constant or an illegal strict-domain value have an independent exact checker. Other nonlinear exclusions retain the explicit label `EXACT_BACKEND_PROOF_AND_REPLAY_REQUIRED`: archived Z3 proof/query hashes plus fresh source-derived Z3 replay. Those proofs are not independently kernel-checked.

`IDENTIFIED_TARGET_COMPLETE_KNOWN_REGISTRY` requires at least one exact admitted witness, complete catalogue coverage and no unresolved source decision; all satisfying sources must have the same requested target. `AMBIGUOUS_TARGET_TWO_ADMITTED_SOURCE_WITNESSES` delivers two coherent exact sources with different requested targets. It is a statement about the declared exact observation contract.

`UNKNOWN_RESOURCE_LIMIT`, `UNKNOWN_INCOMPLETE_DECISION`, unsupported/unadmitted inputs and malformed inputs remain distinct. Partial enumeration, failed backend calls, unchecked algebraic witnesses and finite registry cutoffs cannot become an unbounded NO.

## Incomplete original registry

```sh
python bounded_search.py examples/unknown-size-positive.json \
  --max-extra-hybrids 2 --output unknown-run
python verify_search.py unknown-run/SEARCH-RESULT.json --replay-backend
```

Each finite trial is a complete candidate registry extending the declared accessible original controls with explicitly named unmarked candidate hybrids. A found source is a legitimate positive witness. Exhaustion of those finitely many trials is `UNKNOWN_BOUNDED_SEARCH_EXHAUSTED`, not global UNSAT. The driver does not promise termination or completeness of unknown-size recognition.

The independently accepted prospective G3 strict-invariant interface is summarized in [GLOBAL-CERTIFICATE-BOUNDARY.md](GLOBAL-CERTIFICATE-BOUNDARY.md). No current solver flag accepts a global unknown-size NO certificate. That needs separately pinned complete grammar/core coverage, actual joint compiler admission and every exact initialization/production/exclusion check.

## G7 design pipeline and executed policy

```sh
python export_design.py examples/four-taxon-passive-design.json --output design-run
```

The export enumerates every admitted original source, retains shared parameters across its entire deterministic row menu, aligns one common finite rooted/unrooted readout, computes the actual target and builds the accepted G7 affine-program real-QE predicate. Supports retain strictly positive REAL weights. The resource contract is reset/deletion-closed PATH costs: executed calls, unions of positive-support configurations and original controlled sites. Calendar/DNA readers and irreversible resource menus are not encoded by this exporter.

`actual-source-design.wl` can be evaluated with an authorized Wolfram Language backend. Completed export is not a completed backend decision or a generic CAD policy extraction. The original constructor is preserved byte-for-byte. Its derived `continuous_optimizer_normalized.wl` eliminates the UNIQUE weight1 of singleton supports before QE; larger simplices retain the original real-weight quantifiers.

The delivered actual four-taxon TREE run covers all15 positive original rooted trees. Each symbolic unrooted law is checked to equal `(1−2s/3,s/3,s/3)` at its actual displayed split, with s a nonempty product of original positive edge survivals. The converse image construction assigns each participating edge the positive kth root of s, with all unused edges1/2. Thus the complete source image is exactly three one-variable images, not a fitted surrogate.

The normalized exact backend returned:

- zero-call budget: False
- one passive exact-call budget: True
- largest-concordance-factor policy correctness: True

`passive_quartet_policy.py` executes that semialgebraic policy and emits an independently recompiled positive source witness and the actual original-taxon split. Its scope is the complete four-taxon zero-hybrid positive-tree class. Its verified optimum is one exact call, one configuration and zero controlled sites.

The direct15-source recursive QE run aborted; the first reduced run timed out. Both failures and the final determinate run are preserved in `WOLFRAM-RAW-BACKEND-RECEIPTS.json`. The backend emitted its original global-symbol warning even in its successful constructor control; exact returned answers and warnings are both retained. General multi-support CAD cell selection, adaptive executable policy extraction and large-instance optimization remain visible engineering work under the accepted hand theorem.

## Measured data admission

The negative empirical test binds the actual Tsuga pilot admission-certificate SHA-256. Verified dataset metadata and dimensions do not supply genealogy-law probabilities. The pilot is `NOT_ADMITTED_TO_EMPIRICAL_SOLVER`: full file bytes, partition/copy/specimen/independent-block joins and calibrated source/channel admission are unresolved. The test laws are synthetic. Rejection does not prove biological infeasibility or DNA nonidentifiability.

This is a negative-admission guard, not a general empirical validator. Every other nonempty empirical-admission payload also fails closed. A field asserting `ADMITTED` cannot authorize a scientific fit; a real source/channel adapter must be implemented and independently reviewed first.

The conditional sequence-channel bridge additionally needs a known substitution generator/rate bound, linked-site count and a supplied genealogy-height tail bound. Exact topology-only factorization is generally false. Conservative closed-TV overlap is an uncertainty statement. No empirical calibration or DNA inference is claimed here.

## Evidence and attribution

`TEST-RECEIPT.json` records one terminal-exit0 command covering13 source workflows, two bounded searches, seven tamper rejections, exact algebraic decoding, original same-tree joint dependence, malformed-contract guards and the original3,336 exact compiler/census controls. Those controls validate implementations; they are not universal theorems by testing.

The source census/compiler/continuous constructor are exact attributed copies from GPT-6 Astra Pro's [2026-10-01 source implementation](https://github.com/Sodelin/Research-Commons/tree/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g7-continuous-design). Git blobs and SHA-256 identities are in `UPSTREAM-IDENTITY.json` and `ADDITIONAL-UPSTREAM-IDENTITY.json`.

The later independently accepted [G7 exact-master review](https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md) supersedes the older upstream README's then-pending mathematical review status. It characterizes the complete-registry exact-law semialgebraic design master at hand-proof scope. The practical implementation and large backend executions are separate. G6's accepted approximation/channel theorem, G3/G4's genuinely unresolved unbounded recognition/determination questions, G1 assembly and the existing Lean programme retain their own scopes. No earlier stronger M3/full-sample result is weakened.
