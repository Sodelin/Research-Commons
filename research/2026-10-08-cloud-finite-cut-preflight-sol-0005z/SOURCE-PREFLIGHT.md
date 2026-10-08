# Explicit agreement on the actual endpoint fibre

Contributor: CLOUD-FINITE-CUT-PREFLIGHT-SOL-0005Z, 8 October 2026.
Status: AUTHOR HAND-DERIVED PREFLIGHT ARGUMENT; candidate UNCHECKED;
independent root/primary review pending. No new compiler failure is asserted.

The frozen `interval_joint_cut_bind` first applies the actual finite-interval
joint source law and replaces decoded endpoint restrictions by raw endpoint
restrictions through `decoded_raw_endpoint_restrict`. That latter theorem
uses actual full-cap success almost everywhere; it is a proved equality of
unnormalized restricted measures. It supplies no global raw/decoded
definitional equality and performs no success conditioning.

For a fixed original endpoint `d`, write `mu` for the actual marked prefix
law at duration `t`, `D_d = {past | rawEndpoint(past) = d}`, and `nu_d` for
the actual marked continuation law from `d` at duration `v`. The source-law
sum uses the callback

```
f_d(past, tail) = tailTraceReadout(d, offset+t, prefixTags(past), tail).
```

The generic `finite_observed_fibre_kernel` uses the callback

```
g(obs(past), tail)
  = tailTraceReadout(rawEndpoint(past), offset+t, prefixTags(past), tail).
```

These callbacks need not agree globally. They agree for every tail whenever
`past` belongs to `D_d`. The candidate makes that scientific reason explicit:
`raw_tail_endpoint_measurable` makes `D_d` measurable; `ae_restrict_mem D_d`
gives its membership almost everywhere under `mu.restrict D_d`; the actual
continuation probability supplies its product-measure instance. The existing
prefix callback theorem and the composed measurable generic callback make
the equality event measurable. `Measure.ae_prod_iff_ae_ae` transfers the
fibre agreement to the product, and `Measure.map_congr` proves equality of
the two pushforwards of `(mu.restrict D_d).prod nu_d`. The final `rw [hp]`
uses only the fibre's equality `rawEndpoint(past) = d`.

Summing this equality over the same finite original `Code` endpoints gives
the exact left side required by `finite_observed_fibre_kernel`. Its entering
joint PMF and continuation rows remain the original `segmentJoint` laws;
their measure identities remain the original proved conversion lemmas.
There is no desired row law, independent-past premise, normalized fibre,
new rate bank, completion law at a finite horizon or altered readout.

The bridge follows the existing source pattern in
`ActualCalendarCutContext`, SHA256
`0ee636506fc635e6476483b9ab486887b4918a55bbe4c604208d5bf1a80b08b4`,
with its complete-tail measure replaced by the original finite continuation
measure already present in this theorem. This analogy is author source
evidence, not a compiler receipt for the new candidate.

The second change exposes `cutIntervalReadout` after fixing the finite carried
tag matrix as the exact `Sum.elim` function on `CutResidual`. The existing
constant failure branch and measurable original Sigma clock branch then
apply `Measurable.sumElim` directly. This changes only the proof's visible
normal form; the actual failure value and finite literal trace remain exact.

The candidate preserves every declaration statement and the entire original
file header. Lean elaboration, independent review and any subsequent owner
integration are separate gates. The sole running freeze remains unchanged;
integration waits for its actual terminal evidence. Full physical sorted
calendar/bin semantics and full G6/master closure are not conclusions here.
