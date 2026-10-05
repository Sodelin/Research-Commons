# Reproduction commands for the declared instrumented attempts

Status: execution/format gates are recorded separately; this file lists commands, not success.

Use the same pinned BPP runtime, source fixture and admission record from the previous published packets. Keep all three code directories as siblings. The output monitor is a polling stop rule with a 256 MiB aggregate cap and 1 MiB receipt reserve; it does not claim an OS filesystem quota.

```
python bpp-instrumented-diagnostic-20261005-0535z/test_watchdog.py
python bpp-instrumented-diagnostic-20261005-0535z/test_runner.py
python bpp-instrumented-diagnostic-20261005-0535z/test_summary.py
python bpp-instrumented-diagnostic-20261005-0535z/run_instrumented.py A00-instrumented-seed10101 --analysis A00 --seed 10101 --burnin 20000 --nsample 5000 --sampfreq 20 --usedata 1 --timeout 600
```

Validate the first terminal outcome and actual labelled per-node/genealogy format before the second command:

```
python bpp-instrumented-diagnostic-20261005-0535z/run_instrumented.py A00-instrumented-seed10202 --analysis A00 --seed 10202 --burnin 20000 --nsample 5000 --sampfreq 20 --usedata 1 --timeout 600
python bpp-instrumented-diagnostic-20261005-0535z/summarize_instrumented.py
```

The accepted runner pins its watchdog source. The summarizer pins the earlier scalar helper and that helper pins the earlier A01 ESS source. Existing run directories cannot be overwritten. Retain partial evidence on size/time/error termination. Do not run either command merely because this document exists; follow the declared review/execution gate and any later stop instruction. No automatic extension is part of this procedure.
