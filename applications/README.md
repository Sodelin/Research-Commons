# Research Commons applications

These recovered applications are now publicly integrated under [Apache 2.0](LICENSE), following Nolan's authorization. They reuse the existing mathematical and software work. [Migration provenance](MIGRATION-PROVENANCE.json) distinguishes inherited source pins from the newly written common entry point. Earlier private-location references in inherited documents describe their history; [the current publication authority](AGENTS.md) applies to these named applications.

From the Research Commons repository root, run:

```sh
python3 applications/scientific-integration/run.py cwu
```

This requires Python 3.10 or newer and no installation. It creates a fresh dated directory containing `REPORT.html` and `RESULT.json`. The default displays saved, explicitly labeled evidence for Linda Raubeson's hemlock nuclear/chloroplast question. It does not download data, contact a professor or make model-service requests. Actual control replay and sequence analysis have separate dependencies and commands below. A report is evidence of the stated computation, not a biological endorsement or a whole-application Lean certificate.

Other offline applications use the same report entry point:

```sh
python3 applications/scientific-integration/run.py workbench
python3 applications/scientific-integration/run.py molecular
```

The workbench demonstrates exact and conditional finite-catalogue genealogy inference, including ambiguity and refusal. Its finite catalogue, source class and statistical promises are explicit. It does not admit empirical hemlock observations automatically. The molecular command reuses RNA-processing fixtures with a synthetic provider. Expression, splice usage and derived PAS outputs remain separate; unavailable outputs remain unavailable.

For the recovered native haplotype core, Rust 1.90 was used in this continuation. The crate has no external dependencies:

```sh
cargo build --release --locked --offline --manifest-path applications/molecular-analysis/core/Cargo.toml
python3 applications/scientific-integration/run.py molecular --core-binary applications/molecular-analysis/core/target/release/molecular-haplotype-core
```

Haplotype predictions compare matched REF/A/B/AB sequences. Single-variant scores are not combined-haplotype effects. These demonstrations use hypothetical/synthetic scenarios, not measured expression or plant-specific predictions.

For an exploratory sequence comparison, use an isolated Python environment with the exact recovered optional dependency:

```sh
python3 -m venv .venv-research
.venv-research/bin/python -m pip install -r applications/genealogy-compatibility-workbench/requirements-sequence.txt
.venv-research/bin/python applications/scientific-integration/run.py cwu --replay-sequences
```

[The CWU evidence packet](../research/2026-10-08-codex-integration-0825z/g6/README.md) records public data, preprocessing, original specimen/taxon labels, exact replay commands and the baseline's limits. Marker bootstrap support is descriptive. A calibrated sequence-to-source observation channel, orthology/independence justification and biological source admission are still required before the mathematical solver can certify a capture explanation.

The actual small baseline uses a 1,048-site nuclear 4CL1 marker and a 1,428-site chloroplast rbcL region from four published specimen/accession joins. Their estimated splits disagree in the selected published pattern. One rbcL region is inferred by explicit homology checks because its deposited record has no gene annotation. The report discloses that decision. The computation replays the original workbench adapter and its receipt verifier; it is not a reproduction of the paper's complete dataset or a new capture finding. The default displays these saved results; `--replay-sequences` recomputes them offline from the included public GenBank records.

The original public source-control solver can be replayed separately with its pinned Python dependencies, as documented in that packet. The [practical Rust integration](../research/2026-10-08-codex-integration-0825z/practical/README.md) has a different nine-parameter clock-JC observation contract; the CWU adapter refuses substitution of empirical hemlock records into that contract.

AlphaGenome access is unresolved. [The access design](../research/2026-10-08-codex-integration-0825z/ACCESS-PLAN.md) specifies credentials, supported operations, input bounds, retries, quotas, logging and revocation before activation. No credentials, live pilot or persistent service are activated. The common entry point uses the mock provider and removes its API-key environment variable from child processes. This is a workflow restriction, not isolation from other processes running as the same user.

External data, dependencies and service outputs retain their own terms. Inherited example receipts are saved historical receipts; newly executed commands label their own execution and preserve prior artifacts. [The integration checkpoint](../research/2026-10-08-codex-integration-0825z/README.md) separates tested components, reviewed hand/source work, accepted Lean modules and remaining scientific obligations.
