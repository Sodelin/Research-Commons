# Reproduction

Use the independently acquired, pinned official BPP runtime/source/fixture and original admission record described in the prior A01 packet. Merge this packet's code/ sibling directories with that layout; no existing run directory is overwritten. Python 3.12.14 and NumPy 2.3.5 were used; no new package was installed. The ESS helper is pinned to its prior reviewed SHA256.

From code/:

```
python bpp-fixed-topology-diagnostic-20261005-0514z/test_fixed_leading.py
python bpp-fixed-topology-diagnostic-20261005-0514z/test_fixed_summary.py
python bpp-fixed-topology-diagnostic-20261005-0514z/run_fixed_leading.py A00-fixed-leading-seed9101 --analysis A00 --seed 9101 --burnin 20000 --nsample 50000 --sampfreq 2 --usedata 1 --timeout 600
python bpp-fixed-topology-diagnostic-20261005-0514z/run_fixed_leading.py A00-fixed-leading-seed9202 --analysis A00 --seed 9202 --burnin 20000 --nsample 50000 --sampfreq 2 --usedata 1 --timeout 600
python bpp-fixed-topology-diagnostic-20261005-0514z/summarize_fixed.py
python bpp-fixed-topology-diagnostic-20261005-0514z/audit_controls_and_logs.py
```

The root-time decomposition additionally requires the two completed longer A01 traces from the preceding packet:

```
python bpp-a01-continuation-20261005-0450z/diagnose_root_time.py
```

The copied controls preserve the source A01 priors and sampling map, set speciestree=0 and a single fixed topology, then change only the recorded seed/budget/output/finetune/thread settings. Source hashes and each terminal input/output inventory are retained in evidence/. Third-party frog alignments, compressed data, vendor source/binaries and full traces/logs are excluded. Different numerical hardware may change stochastic trace bytes; compare the scientific/diagnostic contract and disclose differences rather than silently substitute receipts.
