# Resumable original JC assembly checkpoint

Clean runtime: `/workspace/cloud-practical-runtime/jc-original`,9 unchanged
read-only numerical sources, all32 public dependencies authenticated.
[Actual result](RESULT.md): single original-D root stage and separate full
3-frame journal replay both complete; rR width1/256, other8widths1,
UNKNOWN_OUTER_COVER, no confidence/source-feasibility/accuracy claim.

The [stager](stage_original_jc.py) refuses an existing runtime. The
[runner](execute_smoke.py) refuses an existing attempt and preserves raw
outputs/metadata on failure. For a fresh reproduction, choose new empty
runtime/attempt paths and execute one command:

```sh
python3 -B execute_smoke.py --commons-root /path/to/Research-Commons \
  --runtime-root /new/empty/jc-original --attempt /new/empty/attempt
```

This reruns the declared bounded control only when intentionally requested;
no unchanged run is needed to resume from the present complete receipt.
Root can integrate the exact producer/checker CLI argument vectors recorded
in the per-process EXECUTION.json files. A producer alone issues no
certificate; only the complete independent checker yields conditional
geometry, and its UNKNOWN/invalid/resource semantics must stay visible.

Remaining original endpoint: admitted prospective joint mean precision,
complete checked retained-cover/export widths for all9 normalized parameters
under useful resources. The exact count C/Rust/C++ component and this clean
assembly do not discharge those scientific obligations. Next bounded code
gate: faithful GMP interval/outward-dyadic/exp primitive against pinned
Python records, keeping existing producer/checker source unchanged until
a separately reviewed integration is concrete.
