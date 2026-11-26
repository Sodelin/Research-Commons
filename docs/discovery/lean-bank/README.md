# Discovery Lean bank

Start with [question/theorem/artifact links](catalog.json), [what retrieval actually does](PULL.md), and the [two Thue–Morse extensions](THUE-MORSE.md). Three linked views, one set of stable IDs. Record whether a result is ours or an external provider, whether it resolves this exact question or a narrower component, and what actually verified it. Suggested dependencies never silently become proof dependencies.

```sh
node docs/discovery/tools/query.mjs --lean-bank "Thue Morse"
python docs/discovery/lean-bank/tools/search-bank.py "exact component" --layer commons_git_source
python docs/discovery/lean-bank/tools/catalog.py docs/discovery/lean-bank/catalog.json show problem.alexander.formal-assembly
python docs/discovery/lean-bank/tools/catalog.py docs/discovery/lean-bank/catalog.json lock theorem.thue.phase-alias
```

## What is in the index

- Curated typed links for recent actual questions and exact artifacts. The Alexander binary portfolio is a scoped hand proof; the formal assembly and fixed-source portfolio are separate open questions. The abstract paired-quartet result does not establish original-network admission.
- **537 overlapping Commons historical metadata rows** from [12 pinned source inputs](legacy/inputs.json), not a proof count or a complete archive crawl. The separate existing [Lean registry](../tools/lean-registry.py) has historically listed named modules and source-store entries; those entries are not necessarily distinct proofs. See the parent [Discovery README](../README.md).
- Pinned external metadata, not wholesale downloads: **225 named entries** from [OpenAI math's formalization manifest](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/formalization.yaml) and **1,901 file paths** in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/tree/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures). These count different things. [Provider pins](external/providers.json) also contain a mathlib locator; current master is not automatically the right dependency for our Lean pin. The externally indexed files were not rebuilt here.
- The [phase result lock](phase-alias.lock.json) selects only two source files; the [height count lock](zero-height.lock.json) selects eleven including its existing provider modules. These don't require downloading an external corpus just to search it.

## GitHub to Discovery worker

The workflow indexes committed research notes, Lean files, and receipt locators after a relevant push to main. It reads Git objects, never executes scanned proof texts or interprets instructions from them. Path-stable SHA-256 shards keep unchanged source buckets reusable between pushes. The generated snapshot, battery receipt, and exact ordinary-CLI query smoke result are placed in `docs/discovery/generated-source-index/`, and federated search reads them automatically. A pushed code file is then findable even if nobody wrote a catalog entry. Exact problem closure, labels and declaration-level attestations still require a verified typed record.

The battery reports separate statuses for indexing, catalog validation/tests, Lean, and SMT. Running a compatible installed Lean can replay the explicitly pinned regression; arbitrary new Lean source and arbitrary solver commands never execute automatically. A missing runner toolchain or missing registered proof job reports `not_run`, not verified or disproved. Its output records whether any supported check actually ran. Fast-forward publication is guarded against stale main and does not force push. GitHub's workflow job summary also shows the stage statuses.

A full staged Lean pull/readback example is in [PULL.md](PULL.md), with status and exact types in the receipt. No private Drive-wide inventory or bulk external Lean execution was performed.

**Backend coverage pass:** [listener, exact coverage gate, provider intake and evidence contracts](BACKEND.md).

**Scale tests:** [broad metadata search, exact lookup, and one bounded proof-job registration](SOURCE-SCALE.md).
