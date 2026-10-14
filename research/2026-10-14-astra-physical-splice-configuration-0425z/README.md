# Proposed whole-configuration and mask transport

This is an **uncompiled, unselected source proposal** over the exact 0400 registry and 0410 original-bank restriction sources. No existing selection, dependency, configuration or compiled state is changed.

The first identity maps only the bank coordinate of the existing `configurationBankPMF ν q`: `(cfg,coin)` becomes `(cfg,f coin)`, yielding `configurationBankPMF ν (q.map f)`. It follows from the existing `PMF.map_bind` and `PMF.map_comp` laws. The source-specific theorem then uses the **derived** 0410 original-bank pushforward under `restrictBank`; the caller supplies no desired bank-law equality.

The same complete `ν : PMF Config` occurs on both sides. Its configuration identities, joint dependence and zero-mass atoms are not replaced, discarded or renormalized. The existing constructor draws one whole configuration and one original natural COMMON bank; the proof does not factor the configuration into site marginals or introduce per-lineage/per-row bank draws.

The remaining definitions pull back an original `Option Bool` mask by the actual retained-hybrid injection `J`: `masks' cfg h = masks cfg (J h)`. The existing `overrideBank` uses `Option.getD`; pointwise none/some cases show that override commutes with restriction on every retained coordinate. None remains natural, while forced false and true remain the same original ordered arm bits. There is no refitted parameter.

These statements concern the paired configuration/bank measure and retained-coordinate masks. They **do not prove a physical output law or authorize deletion of a protected/controlled original site**. In particular, defining a reduced mask says nothing about admissibility of omitting the deleted site's external control. Conditional weighted-tree/forest-law transport, external protected-ID and trace binding, outer admission, finite reduction and the bounded representative remain separate obligations. No claimed result concerns native execution or source feasibility.

`SOURCE-PINS.json` records exact proposed dependencies and the inspected selected library contracts. The aggregate and Lake supplement are proposals only. The source's `#check`/`#print axioms` commands are future requests, not audit output. Official namespace/import authentication, actual elaboration, theorem-type/axiom audit, aggregate Lake execution, evidence capture and verified publication remain pending. Preserve any failure and predecessor bytes before repairs; no axiom or placeholder is an authorized substitute.

Only source preparation and byte/lexical readback occurred. No research module import, compiler, import query, test, materializer, native run, object scan or Git operation was performed for this packet.
