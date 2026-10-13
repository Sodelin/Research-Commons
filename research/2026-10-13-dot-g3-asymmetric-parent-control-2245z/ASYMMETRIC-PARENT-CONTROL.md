# An observable one-arm parent-convention regression

Author: dot, 13 October 2026. Hand-derived finite regression using the reviewed positive source construction. No compiler or native source-law execution. No new G3 recognition or source-count claim.

## Exact inherited source and sole physical mutation

Start with the [published nine-edge four-taxon fixture](https://github.com/Sodelin/Research-Commons/blob/336ba90d280d6dd8a076d96b313383b47014bc7d/research/2026-10-13-dot-g3-physical-singleton-fixture-2200z/PHYSICAL-FIXTURE-AND-DERIVATION.md), whose physical JSON SHA256 is `7552a9e8ae32ee759ed3665bd9a9176deeb6dcbf4be6605b55f8afbb0c7633ba`. Keep every original vertex, edge occurrence, parent label, copy tag, sampling map, mask and date. Keep the original parent-one probability Gamma=1/3, the native parent-zero probability 2/3, and incoming order `[3,4]` at H_A.

Change only the survival of original edge occurrence e4 from 8/9 to 4/9. Since its calendar duration is 1, its positive pair rate changes from log(9/8) to log(9/4). The other parallel occurrence e3 retains survival 8/9. The surrounding A-path edges e2 and e5 each retain survival 3/4. Every other edge survival and rate, and ancestral rate 1, remain unchanged. This changes one physical parameter, not the graph or its admission. The resulting graph is still rooted binary, root-LSA, outer-labelled and cut-child, with strict calendar and an interior COMMON coin.

The accompanying `ASYMMETRIC-PHYSICAL-FIXTURE.json` contains the complete tuple and the same three actual padded allocations. Its added provenance identifies the original fixture and the one parameter mutation. It is an inspectable mathematical fixture, not a claim that the current native parser accepts a new schema.

## Exact source-derived expectations

Condition on the one original COMMON bit, retained through all current roots. Parent 0 uses e3 and gives directed A→B survival X0=(3/4)(8/9)(3/4)=1/2. Parent 1 uses e4 and gives X1=(3/4)(4/9)(3/4)=1/4. Their probabilities are 2/3 and 1/3. Both routes first meet B at U_AB on the same calendar cut as before.

For lambda=choose(k,2), the normalized legal comb moment is

`m_k = (2/3)(1/2)^lambda + (1/3)(1/4)^lambda`.

This follows from the same original-source conditional forest formula and the selected `actual_randomized_legal_moment` theorem used by the original fixture. One physical tuple is used at all k. The retained observable is the single B-first comb after passive pruning of the four baseline copies; its coefficient remains `c_k=2^k/((k+1)! k!)`.

| k | Full padded copies | c_k | Correct m_k | Correct raw probability | Wrong one-sided binding m_k | Wrong raw probability |
|---:|---:|---:|---:|---:|---:|---:|
|1|6|1|1|1|1|1|
|2|7|1/3|5/12|5/36|1/3|1/9|
|3|8|1/18|17/192|17/3456|5/96|5/1728|

The correct-minus-wrong differences are respectively (0,1/12,7/192) for normalized moments and (0,1/36,7/3456) for raw probabilities. Seven copies already detect the mismatch. Six copies remain a zero-exponent control and cannot do so through this scalar row.

## Wrong binding versus a transported coordinate change

Write g0=2/3 for the native probability of the first incoming occurrence e3. The exact whole entering-forest kernel of the hybrid is `g0 E(8/9)+(1−g0) E(4/9)`. The correct original selector parameter is Gamma=1−g0=1/3.

The following are semantic errors against this fixed input:

1. Feed Gamma=1/3 into the native parent-zero slot as though it were g0. This reverses the two arm weights.
2. Preserve the weights but interchange which original occurrence is assigned to parent bit 0 and bit 1. This gives the same reversed mixture in the natural row.
3. Interchange only the physical survival values attached to original IDs e3 and e4. This changes the actual physical tuple and likewise gives the reversed natural-row mixture.

For the first two errors, the discrepancy at any positive exponent is `(1−2 Gamma)(X0^lambda−X1^lambda)`. Here both factors are positive, proving that the mismatch is observable, rather than merely a differently named hidden parameter.

A simultaneous reindexing of the two internal coordinates, their attached edge occurrences, their probabilities and every parent-bit mask is an abstract lawful change of representation: `(g0,K0,K1)` becomes `(1−g0,K1,K0)` and the complete mixture kernel is unchanged. It is not permission to rewrite the fixed original parent registry or actuator IDs. The correspondence must still map external original bit 0 to e3 and bit 1 to e4. With forced controls, the mask bits must be transported too. The present natural-only configuration does not by itself validate that controlled-mask transport.

The pinned [source_fit_bank.rs](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/source_fit_bank.rs), SHA256 `e31b80a3648e6aa15c8c99f30f4eb94e3fb06c6487f7241064391c05c12ffa5a`, already implements the correct complement and requires ascending original incoming occurrence order. Thus an actual request with incoming `[4,3]` is not an authorized alternate encoding in that API. This regression tests preservation of its existing convention, rather than proposing a new conversion.

## Same copy/event contract and certificate negative control

Use exactly the earlier [copy-label transport](https://github.com/Sodelin/Research-Commons/blob/336ba90d280d6dd8a076d96b313383b47014bc7d/research/2026-10-13-dot-g3-physical-singleton-fixture-2200z/COPY-LABEL-TRANSPORT.md): fixture `selected:A:i` maps to executable `selected:A(i+1)`, B and all baseline tags remain fixed, and the executable B-first enumeration is explicitly bound. The event is one rooted labelled unranked comb with A copies grafted in order, not the union of comb orders. Keep all four baseline copies until the output readout. Graph occurrence IDs and the physical tuple do not change when copy labels are mapped.

Do not reuse the old singleton certificate as a positive certificate for this unequal-arm source. For `P(x)=(x−1/2)^2(x+1)`, the correct expectation is `5/192>0`; the wrong-binding expectation is `5/96>0`. The correct moments also fail singleton equality: `17/192−(5/12)^3=7/432>0`. A singleton-only generator should therefore decline this case according to its existing UNKNOWN/refusal contract. This is a certificate negative control, not a physical source NO. Two positive support atoms are explicitly realized here.

## Exact encoding and intended next execution

Calendar ages and durations remain exactly those of the original fixture and the inherited maximum-child-height binding. Whole-edge survivals and coin probabilities are rational. The physical rate on e4 is the exact logarithm log(9/4); this is not inserted as a rational inverse rate or rounded decimal. All interval coordinates must still derive from their one physical edge rate. The only changed whole-edge native coordinate is x4=4/9; the final inherited variable `g_H_A` stays 2/3.

The existing integration owner can run the same full-table-to-pruned-row path as for the singleton fixture, once its guarded 6–8-copy profile is available. Expected correct and deliberately wrong outputs are listed above. Bind every run to its actual parameter/occurrence record so a wrong-binding run cannot be mislabeled as the original source. No new source count, generic certificate theorem, support-grid search or compiler is required for this test. The native full-table correspondence and any Lean fixture instance remain separate pending execution/proof gates.
