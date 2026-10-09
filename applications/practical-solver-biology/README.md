# Biological input and optional molecular helpers

These standard-library helpers complement the integrated [practical
solver](../practical-solver/README.md). They reuse public inherited source;
they do not admit new empirical inputs or implement a live model service.

From the repository root:

```sh
python3 -B applications/practical-solver-biology/ingestion.py
python3 -B applications/practical-solver/run.py molecular --output /tmp/rc-molecular-integrated-new
python3 -B applications/practical-solver-biology/offline.py --output /tmp/rc-molecular-new
python3 -B -m unittest discover -s applications/practical-solver-biology -p 'test_biology.py' -v
```

The output path must be new. The offline molecular command exports a fresh
readable Markdown/HTML report, request and machine-readable result. It uses
matched REF/A/B/AB equal-length hypothetical cis sequences with one context
and inherited deterministic provider. Expression, splice usage and the
derived two-window PAS proxy remain separate. No key, client, SDK install,
live prediction or experimental validation is required or performed.

The ingestion command freshly replays the SHA-authenticated literal
1,024-locus extractor, exact fixed-band arithmetic, one affine mean
conversion, and the two-point containment/separation obstruction. It checks
inherited forward enclosures rather than claiming a fresh forward run or new
confidence event. Scientific confidence and biological accuracy stay false.

Current official API-source checks, secure future setup requirements, better
statistics proposals, hemlock admission limits and exact evidence are in
[BIOLOGICAL-INPUTS.md](../../research/2026-10-09-codex-practical-release-0207z/biology/BIOLOGICAL-INPUTS.md).
Owned derivatives use the application Apache 2.0 license; external SDK,
reference assets, model weights and service outputs retain their own terms.
