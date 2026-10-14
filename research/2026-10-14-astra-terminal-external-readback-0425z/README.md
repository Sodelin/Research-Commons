# Terminal external-batch readback proposal

This is an unexecuted source successor for the last batch of the fixed3591 dependency plan. The original owner wrapper and Rust checker remain unchanged. The original wrapper correctly refuses this boundary because its provider expects `complete=False` and a next module.

`terminal_provider.py` differs from the byte-preserved predecessor in only four boundary checks/fields, shown in `SOURCE-DELTA.diff`: exact terminal start+count, exact plan length, literal `complete=True`, and `next_module=None`. All existing source/command/log/object/capture/guard/pause/no-active checks and the256MiB/20CPU readback limits remain. The wrapper pins both provider bytes and their retained source-pin record, executes those verified bytes without Python bytecode lookup, and writes separate exclusive owner-terminal outputs.

Run only after an actual closed successful final guard and the existing explicit detached `finish` operation, with no active compiler:

```text
python3 -B research/2026-10-14-astra-terminal-external-readback-0425z/terminal_readback.py BATCH START FRESH_COUNT
```

`START + FRESH_COUNT` must equal3591; count is1..64. This does not choose or launch a batch, weaken resource limits, alter old evidence, repair failures or synthesize an outer guard. Its actual successful result would authenticate the final batch's receipts and its literal completed-plan report. The prior prefix is rechecked by the actual pinned guarded builder; this final readback separately rehashes only fresh final-batch artifacts. Complete historical provenance export and all owned-provider/Lake/type/axiom audits remain separate. Original042/057/059 outer outcomes remainUNKNOWN.

Status: AST/source inspection only. No checker imports, tests, compilation, object scans or production readback have run. Independent source review is required before future execution; source creation is not verification of the terminal boundary.
