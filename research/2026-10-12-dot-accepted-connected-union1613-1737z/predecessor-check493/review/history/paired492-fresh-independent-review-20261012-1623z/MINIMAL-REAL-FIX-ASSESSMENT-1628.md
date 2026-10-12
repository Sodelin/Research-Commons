# Post-attempt12 minimal proof-term repair assessment

Reviewed 2026-10-12 16:28 UTC. No further execution is admitted by this note.

Attempt12 has exact source exit -6 after 27.407 seconds. The raw transport final register marker7 was reached, but its after-proof marker was not. No ordinary error is visible. The local unusedSectionVars suppression did not resolve the abort. This run cannot attribute the failure to the later linter because it did not establish that the proof had finished.

The raw helper context contains raw States, IDs, explicit Valid witnesses and field equalities, with inherited finite/equality instances. It has no original graph, sample, bank, Choice, SourceValid record or large geometry let. The section scan found no explicit include directive carrying such data. The unused section instances are small; their presence is not evidence of the abort cause.

Accepted SourceForest transport at d6e5b2b57cf03091f8b5b5a2c80cf49de39bab938c50a467b46b30e08f12871d only updates location/history. Accepted encodeSnapshot at 4628112bbbc69528748bbc93f8a3f8200bc802a6e72417fb90c39e7acd49f744 copies the register directly. New renameSnapshot also copies it. Consequently both raw helper final register goals reduce definitionally to s.register = t.register. The existing simp only invocation unfolds full records, including dependent encoded genealogy fields, unnecessarily.

Recommend the smallest real repair in both raw helpers: an explicitly typed register equality target followed by hReg.symm. Preserve all headers, assumptions, imports and prior proof bytes; remove the diagnostic lint option and markers. This changes proof construction rather than any source law or mathematical premise. If the complete source still cannot fit, independently proved opaque field identities and a short Snapshot.ext assembly are a targeted next proof-organization option. Current evidence does not establish cumulative environment allocation or justify module splitting/cap changes.

The author will freeze the exact marker-free delta and measured current-stage retry proposal for separate review and root admission. Complete paired Boolean/future BOTH endpoint, kernel checks and full1611 baseline remain mandatory. No novelty or partial acceptance is claimed.
