# COMMON menu to native profile compatibility

Contributor: Astra Rust integration lane, 13 October 2026, 21:06 UTC.
Status: tested executable compatibility component; full solver integration remains open.

The existing exact COMMON certificate/query interface and selected native forward
profile cannot yet be connected directly. Every legal padded query keeps all
`n` baseline copies and `k+1` selected copies. The menu requires `4 ≤ n ≤ 8`
and `k ≥ 1`, so even the smallest query needs six distinct copies. The pinned
RC1 LAW parser/validator and native snapshot Context accept at most four.

`compatibility.py` reuses the byte-pinned `common_packet` and `fixed_queries`
providers. It authenticates the existing restored native source inventory and
five selected native source files. It does not introduce a decoder, execute a
native solver, prune baseline copies or modify the recovered core.

The report preserves:

- Original request bytes/hash separately from canonical JSON identity.
- Typed taxon, protected-edge, protected-hybrid and configuration IDs. The same
  text is legal in different namespaces; input ordinals are not graph indices.
- Every tagged copy allocation, directed pair, certificate hash, query hash,
  supplied exact normalized moment and derived event-probability requirement.
- All original joint configurations, including zero mass and natural (`null`)
  masks. A separately labelled exact distribution over complete masks permits
  comparison under configuration reordering; it is not a rewrite of the input
  and does not equate configuration IDs or replace joint laws by marginals.

The current result is `UNKNOWN`, with `compatibility_report_complete=true` when
the source checks and report finish. No physical source existence, source
exclusion, native refinement or arbitrary-input G3 conclusion is certified.
Malformed menus and nonempty protected-parameter constraints retain the reused
provider's refusal. Missing/changed native source authentication returns UNKNOWN
with an incomplete report. Unsupported mathematical work is never converted
to a NO decision.

The parameter convention is explicit. RC1 LAW routes `incoming[0]` with `G:i`.
The canonical snapshot/calendar interface uses original parent bit 1 with
`Gamma`. The existing `source_fit_bank.rs::run`, exposed by `bind`, already
performs `Gamma = 1 - old_parent_zero_probability`, preserving the original
incoming edge-occurrence order. This report cites that established conversion;
it performs no actual parameter or candidate-source binding. Parallel edge
occurrences must not be identified by equal endpoints, and incoming parents
must not be reordered to hide the convention difference.

From the repository root, with the existing public source restoration available:

```sh
python3 -B research/2026-10-13-astra-native-common-compatibility-2106z/compatibility.py \
  --request research/2026-10-13-astra-unified-solver-0645z/examples/correlated-menu.json \
  --native-sources /workspace/scratch/astra-recovered-parity-0702 \
  --output /workspace/scratch/new-common-compatibility-report
```

The output directory must be absent. The example returns exit 2/UNKNOWN. Its
48 full padded rows require 6–8 copies, all outside the selected four-copy
profile. Restoring sources uses the existing baseline `restore_parity.py` and
its pinned manifest, not another implementation.

Actual receipts:

| Execution | Result and limit |
|---|---|
| `evidence/python-contract-tests-v1` | Ten tests passed; guard exit 0/no stop, 0.502 seconds, 17.24 MB peak child RSS. Includes malformed JSON/PMFs, duplicate IDs within namespaces, legal shared text across namespaces, tagged-copy collisions, zero mass, exact fraction aliases, joint correlation and missing native sources. |
| `evidence/correlated-menu-v1` | Real CLI report complete, intentional child exit 2/UNKNOWN, no guard stop, 0.502 seconds, 12.85 MB RSS. The generic guard wrapper exits 1 for a nonzero child; this is not an exit-0 receipt. |

Both used the frozen guard with 256 MiB virtual, 4 GiB physical stop, 20-second
wall/10-second CPU, 16 MiB per-file limit and existing disk/RAM floors. There
were no Lean or Rust compiler invocations. Python modules were freshly executed;
the existing provider/native source identities were authenticated reuse. Finite
tests do not prove universal native correctness. There are no new Lean theorems
or axiom claims in this packet; the separate adapter and generated-proof builds
retain their own execution/audit obligations.

| Intended obligation | Current status | Remaining action |
|---|---|---|
| Source-faithful menu and typed ID ledger | Tested bounded component | Preserve exact source/receipt identities on publication. |
| Full padded row in native profile | Blocked by four-copy profile | Review the isolated six-copy COMMON proposal in `EXTENDED-PROFILE-PROPOSAL.md`. |
| Original graph occurrence and shared-parameter binding | Unbound | Supply authenticated source occurrence maps and use existing exact convention conversion. |
| Joint mask/readout to actual source law | Open | Bind the full joint configuration and passive readout to the same supplied source. |
| Supplied certificate to physical bounded COMMON representative | Conditional/open integration | Complete selected Lean provider, physical admission and interface checks; this report is not that theorem. |
| General G3 / end-to-end source solver | Open | Preserve UNKNOWN where the accepted mathematics or executable bridge is missing. |
| Publication | Local packet ready for coordinator publication | Sole Git owner publishes and verifies immutable remote bytes. |

See `SOURCE-LEDGER.json`, `VERIFICATION.json` and `PACKET-MANIFEST.json` for the
exact selected sources and receipts. No older frozen packet was changed.
