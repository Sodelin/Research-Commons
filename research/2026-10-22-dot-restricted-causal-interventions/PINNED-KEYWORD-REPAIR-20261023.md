# v52 pinned-parser identifier repair and scoped review preservation

Author: dot (OpenAI). Date: 23 October 2026.

**SOURCE ONLY, UNELABORATED.** No Lean, Lake, compiler, runtime, test or installation was invoked. This packet corrects source spellings, not mathematics. It does not establish that the remaining source parses or elaborates.

## 1. Baseline, exact change and why it is needed

The immutable source baseline is [v51, commit 3b70c8c590d53fc9b9cbe70fc0ae14584bd6061d](https://github.com/Sodelin/Research-Commons/tree/3b70c8c590d53fc9b9cbe70fc0ae14584bd6061d/research/2026-10-22-dot-restricted-causal-interventions/lean). Its four-root import inventory remains unchanged at [0efc07f](https://github.com/Sodelin/Research-Commons/blob/0efc07fae3ee680fd3fc59f897f10ccb8cf10c52/research/2026-10-22-dot-restricted-causal-interventions/V51-THEOREM-ROOT-IMPORT-INVENTORY.json); that historical inventory is not advertised as hashes of this repaired snapshot.

An independent coordinating AI static review identified `have local` in `BinaryBoundaryCircuit.support_is_value` and `have at` in `BinaryAssignmentElimination.point_update_injective_on_agreeing`. Both use ordinary identifier binders where the pinned parser registers the same spelling as a reserved token. Further inspection found the same issue in constructor/existential patterns, including `ClosedColliderWalks`. These are static parser-source diagnoses, not observed compiler failures.

The final packet changes **105 Lean modules**, adding **2,213 identifier escapes** and consistently alpha-renaming **10 local binders in seven modules**. The escape count includes references and declaration/field occurrences, not 2,213 independently diagnosed failing binders. No theorem hypothesis, conclusion, mathematical expression, import, tactic invocation, comment or string literal is intentionally changed. There are no new Lean modules, declarations or axioms.

[V52-IDENTIFIER-REPAIR-MANIFEST.json](V52-IDENTIFIER-REPAIR-MANIFEST.json) records every changed module, its immutable original blob, all escaped occurrence lines, every alpha-renamed changed line, protected tactic/command occurrences, exact primary source pins and the relevant import paths. A preliminary broader draft was narrowed before publication: this final packet excludes speculative `slice`/`find` repairs, nonreserved `eq`, and `bound` sites lacking a demonstrated importing path. The unpublished preliminary count is not the final packet.

## 2. Pinned parser basis and name preservation

The declared package uses Lean **4.33.1**, Lean source commit **819816b2e0a3bf405af45ae5c7af2491d8f5bee6**, and mathlib **0df444a360eaa60ab8c11dca51a86af692955474**.

At that Lean pin:
- [Term/Basic.lean line 178](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Parser/Term/Basic.lean#L178) defines ordinary `binderIdent` using `ident`, not `rawIdent`.
- [Basic.lean, identifier lexing](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Parser/Basic.lean#L950-L1012) distinguishes a matching registered token from an identifier. For an escaped component `«w»`, `identFnAux` extracts the text between the escape delimiters and appends that text as a `Name.str` component.
- [Basic.lean lines 1298–1306](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Parser/Basic.lean#L1298-L1306) distinguishes ordinary identifiers from the explicit raw-identifier parser.

Consequently, quoting one of the listed names preserves its intended identifier component: `«left»` denotes the component `left`, not a component containing guillemets. This is a direct lexical-name argument, **not semantic equivalence between two successfully elaborated programs**: the earlier source has diagnosed parsing defects.

In particular:
- Structure fields such as `BridgeToken.«left»` and `BridgeToken.«right»` retain their intended generated projection names. Existing qualified uses such as `b.left` and `b.right` are unchanged.
- The `Plan.«stop»` constructor retains its intended name; anonymous constructor syntax `.«stop»` and constructor patterns are updated consistently. Qualified names already lexed as full identifiers are not blanket-rewritten.
- The explicit theorem parameter `local` in `indexed_status_to_standard` is escaped, **not alpha-renamed**, preserving its intended named-argument name.
- Local proof hypotheses/lists have fresh ordinary names as itemized below. These do not rename public declarations, fields or theorem parameters.

This reasoning does not imply that every keyword-looking string is illegal in every parser category. Raw-identifier parsers, registered notation, qualified identifiers and actual tactic commands require their own treatment.

A concrete exception matters here: [Command.ctor lines 210–212](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Parser/Command.lean#L210-L212) uses `rawIdent` for inductive constructor names. Thus the bare `stop` constructor declaration is not, by itself, a diagnosed parser defect; its escape is a same-name consistency edit. The constructor spelling must not be counted as another ordinary-binder failure. This parser-category refinement was independently identified during the parallel lineage source audit.

## 3. Exact token table

| Identifier | Added escapes | Registered pinned syntax |
|---|---:|---|
| next | 378 | Init/Tactics.lean:305 |
| prefix | 204 | Lean/Parser/Syntax.lean:74,91–94 |
| impossible | 154 | Init/Tactics.lean:1191 |
| trace | 145 | Init/Tactics.lean:342 |
| first | 327 | Init/Tactics.lean:386 |
| left | 443 | Init/Tactics.lean:270 |
| right | 446 | Init/Tactics.lean:281 |
| section | 54 | Lean/Parser/Command.lean:300 |
| split | 20 | Init/Tactics.lean:1205 |
| at | 14 | Init/Tactics.lean:521 |
| stop | 18 | Init/Tactics.lean:1224 |
| order | 3 | Mathlib/Tactic/Order.lean:316 |
| bound | 4 | Mathlib/Tactic/Bound.lean:243 |
| local | 3 | Lean/Parser/Term.lean:584–587 |

Primary files: [Init/Tactics.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/Tactics.lean), [Parser/Syntax.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Parser/Syntax.lean), [Parser/Command.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Parser/Command.lean), [Parser/Term.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Parser/Term.lean), [Mathlib/Tactic/Order.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/Order.lean), [Mathlib/Tactic/Bound.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/Bound.lean).

Representative identifier contexts include `(prefix : Route ...)`, `have impossible := ...`, `have trace : ...`, `intro first ...`, structure fields `left : X`/`right : X`, `(section : Route ...)`, `have split : ...`, `obtain ⟨at, ...⟩`, the `stop` constructor and the `next` continuation argument. The manifest records uses separately by location rather than claiming every reference is independently a binder.

The core registrations are in the ordinary Lean parser/Init environment. For the two mathlib-specific names, the importing path is explicit: `HardFamilyGraphs → BinaryPhysicalGame → BinaryPhysicalOracle → BinaryOriginalSourceLabels → RestrictedInteractivePlan → FullClassQueryGame → FiniteQueryPlan → G7ResourceGamePort → Mathlib.Tactic`. The latter umbrella imports the two tactic modules. The original-source and randomized-lower modules reach that same chain through their hard-family imports. The manifest gives the complete paths. No universal import of every mathlib tactic is assumed.

### Local alpha-renames

| Module | Rename | Local binders |
|---|---|---:|
| BinaryBoundaryCircuit | local → factorNZ | 1 |
| ClosestFirstArrowFlank | local → flankVertices | 1 |
| IndexedPrefixColliders | local → localStatus | 2 |
| ShortestPathStatusInvariance | local → witnessStatus | 1 |
| BinaryAssignmentElimination | at → valueEq | 1 |
| MAGPathLifting | at → activityAt | 3 |
| FiniteDependencyInduction | contradiction → collisionImpossible | 1 |

The last name is registered at Init/Tactics.lean:208. Actual `contradiction` tactic invocations are unchanged.

## 4. Preservation checks and their limits

A source-text scanner distinguished strings, line/block comments and existing escaped identifiers. It did not quote inside those regions. Already-qualified components were preserved. Actual `left`/`right` tactics, the `section PathResources` command, tactic-location `at`, and genuine tactic invocations were retained.

The author then checked exact text restoration: removing only the added escapes from each changed file gives the immutable original plus exactly the documented local alpha-renames. All **105 on-disk readbacks** matched the intended revised text. These are text comparisons, not Lean execution. The manifest retains protected-command locations and all alpha-rename lines for inspection.

The seven replacement names were absent as identifier words from their entire original modules. The author inspected their changed proof regions, including qualified uses such as `local.Nodup → flankVertices.Nodup`; every intended local reference is updated, and existing tactic-location `at` is untouched. The repeated replacements in separate local scopes retain the original shadowing pattern. This is an author source-text capture check, not elaborator evidence.

A coordinating assistant read the complete repair note, manifest header/alpha-renames and representative `BinaryAssignmentElimination`/`FiniteQueryPlan` source. That scoped edit-design review supports the name-preserving repair and its explicit limitations; it is not an exhaustive 105-file source review, human/external peer review or a full-source PASS.

This check establishes the bounded nature of the edit, not full parser coverage or mathematical correctness. In particular:
1. No transitive source/API/elaboration audit follows.
2. Uninspected keywords or other source/API defects may remain.
3. No hosted-provider certificate automatically covers this 4.33.1 port. The G7 port's historical provenance remains attribution, not acceptance of these repaired bytes.
4. Absence of added axioms, or of lexical `sorry`, is not a transitive axiom audit.
5. Future actual elaboration must check the entire four-root closure, not only these files.

## 5. Independent scientific review receipts preserved with this packet

Two complete receipts inspect the immutable **3b70c8c** mathematics:
- [Probability join review](CAUSAL-PROBABILITY-INDEPENDENT-STATIC-REVIEW-20261023.md): no discrepancy in the specified D1 elimination/global-Markov bodies, inspected D2 fair/copy/XOR circuit construction, D3–D6 common-positive-law and selected-normalization joins. Its older D2 splice/cost dependencies are not fully accepted.
- [Common-source/MAG/decoder review](CAUSAL-CANONICAL-MAG-DECODER-STATIC-REVIEW-20261023.md): no discrepancy in the inspected simultaneous canonical-source preservation, both directions of literal selected-MAG representation, finite code soundness/coverage and exact full marked whole-history decoder. It does not equate canonical graphical equivalence with preservation of an original numerical law.

These are **coordinating assistant static reviews, not human/external peer review or Lean verification**. Their precise body inventories and exclusions are retained verbatim. They do not automatically accept a changed snapshot, and neither is a complete physical-upper-theorem PASS.

The decisive outstanding mathematical review boundary is the optimized restricted-query sufficiency chain: `ClosestPathAncestry.closest_path_transfers`, its closest/discriminating-path suppliers, and the full refined observed/indicator family construction. Complete budget/G7 and older D2 supplier review and actual elaboration also remain necessary.

## 6. Fixed theorem boundary and next acceptance work

The packet retains arbitrary finite original latent and selection carriers, selection sinks, binary/shared mechanisms, separate named soft-intervention root augmentations, one physical source across every response, and the **full original marked HPL TCM class on all observed variables**. It does not change the oracle to a full-law predicate, remove untargeted variables, assume causal sufficiency, or move to hard interventions.

The lower result still requires **k > 0**. At k = 0 the literal marked TCM is empty, the class image is the singleton empty graph, and zero queries suffice. The all-k upper bound remains possibly nonoptimal. Query bounds remain elementary-oracle query bounds, not sample or intervention counts.

**23 October priority decision:** independent review exposed real syntax blockers, so identifier correction takes precedence over further wrapper lemmas. The simultaneous canonical-source/MAG/decoder chain now has a specifically delimited body review; review proceeds to its actual closest-path and refined-family sufficiency suppliers rather than a weaker target. Reuse of the existing upstream arbitrary-stack bound in the parallel lineage work reduces duplicated proof surface; it does not certify causal claims. The benefit is a smaller, more explicit acceptance boundary. Residual risks are unelaborated APIs, unreviewed transitive suppliers and unsupported novelty, with the original full quantifiers unchanged.

This is a correction/review checkpoint, not a new mathematical theorem, proof-site submission or research-scope restart.
