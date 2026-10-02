# SCFG2 raw-provider schedule premise check

Attribution: dot. Public-source diagnostic, 2026-10-02.
Pin: `TakumiOtagaki/PKProbDesign@27afdd054272dbda8a74c8aad156970a44c23cd8`.

## Outcome

The pinned span-first schedule does **not** put every raw provider child
before its parent. A balanced, canonical-pair21nt input gives a nonroot
cached-cell/recurrence mismatch with exact unit-factor natural counts.
The same input's root has no future dependency in its raw reachable cone,
and its root count is unchanged. This refutes an unrestricted all-cache-cell
source admission premise; it does not establish a defect in the intended
root law or RNA observable model.

The existing Lean universal interpreter theorems retain their explicit
`EarlierChildren` premise and remain valid. Applying them to the full raw
source provider without a carrier/order refinement would be unsound.

## Reproduced source witness

Sequence: `GAAAAAGGAAACGACAAAACC`

Scaffold: `(......(......)....).`

Fixed pairs are (1,20) and (8,15); both are canonical G:C pairs and satisfy
the three-interior-base minimum. The pairing context admits exactly the
six canonical ordered RNA pairs. The source's actual tree, generator,
validity predicate and exact schedule are compiled unchanged.

Parent WMBP(7,21) is at schedule index3311. For split13, rule
WMBP_SPLIT_BE_WMBP_VP emits:

- BE(1,20,8,15), schedule index3662
- WMBP(7,12), schedule index1654
- VP(13,21), schedule index2305

The deduction is source-valid. The source border values are b(7,21)=−2,
bp(7,13)=8, B(13,21)=20, Bp(13,21)=15. All the selected generation guards
pass. BE is read before its scheduled computation.

Sources:
[exact generator](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/deductions/generate_exact_basic.hh),
[WMB geometry](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/deductions/wmb_geometry.hh),
[exact schedule](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/engine/basic_schedule.hh),
[runtime normalization/scan](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/replay/w_final_exact_inside.hh).

## Exact unit-factor recurrence check

The diagnostic interpreter uses natural local factors1, zero-default chart,
the source ordered active-child product, and the source WMBP_DIRECT_VP
VP_DIRECT→VP lookup normalization. Each unsigned multiplication and addition
is checked for overflow; no floating arithmetic or unchecked wraparound is
used. This is a custom reference interpreter over the unchanged provider and
schedule, not an unchanged physical API run.

After the full original schedule:

- cached WMBP(7,21) =7
- its recurrence recomputed using the final chart =9
- the omitted rule44 split13 contributes BE2 ×middle1 ×VP1 =2
- the analogous rule45 has middle WMBW(7,12) value0 and contributes0

The first simpler split9 witness has an empty middle provider. It would be
safe to remove that particular production in exact semiring semantics.
Split13 demonstrates why empty-provider pruning is not a general resolution.

This obstruction does not require guessing a new physical factor, clipping
the BE span, or relying on one numeric tolerance.

## Whole tiny graph and the root distinction

For the same source input/context:

- 3699 scheduled keys,17551 normalized dependency edges
- full raw provider:72 future edges,0 missing scheduled children
- raw root-reachable cone:884 keys,3011 edges,0 future edges
- productive unit root cone:171 keys,189 edges,0 future edges
- root W(1,21) count207 under both original and reference orders

A reference order by increasing right endpoint j, BE first for that j,
then ordinary keys by decreasing i and the existing family phase, has
zero future/missing children on this graph and gives parent value9. It
was evaluated only in the custom diagnostic. No saved source schedule or
physical model was changed, and no all-input correctness is claimed for
this candidate order.

The source-specific all-input proof must therefore choose and prove one
of the following contracts, rather than silently assuming the raw premise:

1. Original execution: an admitted root carrier with actual reachability,
   zero-support/frame and source-order laws, sufficient to prove the root
   and observable result while tolerating unused auxiliary cells.
2. A separately validated ordered provider/schedule refinement: exact
   normalized-child coverage plus an all-family well-founded measure, and
   an explicit implementation/equivalence acceptance contract.

The second candidate measure uses right boundaries rather than assuming
BE outer-span containment. BE children end earlier; ordinary same-j tail
children start later, while equal-start wrappers use earlier family phases.
Those are proof targets against all source guards, not established global
invariants from this screen.

## Evidence and reproduction

`SCFG2-PROVIDER-PREMISE-RECEIPT.json` pins six public source hashes,
the diagnostic source/binary SHA256, compiler version and exact result.
`SCFG2-RAW-PROVIDER-NONEMPTY-PROBE.json` is the final machine-readable output.
`probe_scfg2_raw_provider.cpp` contains the public-source-only diagnostic.

With the pinned CParty source tree available, set CPARTY_SRC to its src
directory, then compile and run:

```sh
g++ -std=c++17 -O0 -I "$CPARTY_SRC" probe_scfg2_raw_provider.cpp \
  "$CPARTY_SRC/sparse_tree.cc" -o /tmp/scfg2_provider_probe
/tmp/scfg2_provider_probe 13
```

This check complements established weighted-hypergraph/DP correctness by
testing its concrete source premise. It is not a new generic DP principle,
not another Lean PASS module, and not a full C++/IEEE/physical-law proof.
