# Optional offline molecular demonstration

Execution: **FRESH_OFFLINE_FIXTURE_COMPUTATION**. Evidence: **MOCK_SYNTHETIC**. Live calls: **0**.

Matched REF/A/B/AB sequences use one reference window, tissue, transcript, model and endpoint definition.

| Endpoint | Family | Scale | Synthetic interaction |
|---|---|---|---|
| expr | expression | log | -0.0219702145057 |
| splice | splice_usage | linear | -0.00714285714286 |
| pas-proxy | polyadenylation | log | 0.182254914563 |

Interaction = yAB − yA − yB + yREF on each declared scale.

- Expression is a declared transcript-exon coverage proxy from RNA_SEQ.
- Splice usage is a separate declared SPLICE_SITE_USAGE aggregate.
- PAS is a derived two-annotation-window RNA coverage ratio, not direct PAS output or isoform usage.
- The deterministic synthetic provider is not AlphaGenome inference or experimental validation.
- Human-labelled synthetic context does not supply plant or hemlock ancestry observations.

Exported REQUEST.json and RESULT.json retain settings, sequence digests and per-scenario values. Current live-access setup and terms review remain separate; this command reads no credential and creates no SDK client.
