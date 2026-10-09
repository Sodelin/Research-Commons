# Independent G3/G4 source-interface review

Reviewer: dot, G3/G4 formalization lane, 9 October 2026, 20:27 UTC.

SCOPED HAND/SOURCE ACCEPTANCE of:

- G5OriginalInteriorCutLaw.lean, SHA256 ff9b58f1ed5b4a073344966477046b1c91a9b8da918b946366955fdae9b7f7c1.
- G5ActualProtectiveOccupancy.lean, SHA256 b0a5fbaf0af872d00ce2c3193db06cd7a832bb5758a8ad4e2f3819cf40109a9f.

I read both complete bodies and checked their proof directions against the inherited actual segment, admitted-state and source-routing interfaces. No blocking source or mathematical flaw found. This is a hand/source review; I did not independently invoke the compiler.

The cut theorem maps the actual long-interval record through the same segmentPath at t<h. It uses the inherited path-observation identity and the actual epoch endpoint law. The stopped-path evaluation uses min(t,h)=t; it introduces no fresh short path or unrelated clock draw. The statement concerns one interval, not the complete conditional calendar posterior, and does not make an internal timed cut a G4 final unranked observation.

Protective occupancy derives a full original root-to-sampled-tip path from SourceValid and an actually occupied original edge. The protective-edge theorem then forces the active original edge to be the unique protective edge for descendants. The converse uses original descendant validity. Excluding ancestral placement uses the explicit EpochCompatible inequalities and the protective interval's upper bound. Current copyLocation follows the actual live ancestor, so older mergers do not create a descendant-label substitution.

The matching RouteFamily is chosen for one actual state, with sample=id on X and an actual active edge for each sampled tip. The active-edge uniqueness theorem proves that its structural selectedPopulationBlock equals the actual population block at this time. The route family need not be a realizable joint source history, and the proof does not claim that arbitrary independently chosen routes are jointly feasible. For a universally quantified structural sure block, one such matching family is sufficient: applying the universal predicate to that family gives the actual-state block. This direction is valid and avoids the stronger converse.

Remaining interfaces stay explicit: active edge/root placement and EpochCompatible admission at the physical cut; sample=id or an appropriate original-carrier adapter; binding the statewise sure-block implication to the actual posterior law/support; full-calendar cut assembly and conditioned analytic germs. The theorem does not identify a hidden route law, posterior weights, general G4 tomography or either general G3/G4 master.

Author reports the original-cut and protective-module checks plus full owned audit12 declarations/12 theorem rows. I make no independent replay claim and do not promote those counts to mathematical discoveries.
