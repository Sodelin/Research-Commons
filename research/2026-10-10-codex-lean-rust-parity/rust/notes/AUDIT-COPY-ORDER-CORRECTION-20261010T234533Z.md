# Saved copy-order correction

Direct inspection of the frozen `050bcdda…` patch established that all4,879 C operations are already monotone in encoded source-offset order, with zero backward steps and zero overlap. Design independently confirmed this in `SAVED-COPY-ORDER-RECONCILIATION-ATTEMPT1.json` (`fcfae0bcaba8fa61cb5703401db56842bdc45a6a3aac0507f7459c531adbcc58`). The old prototype sorted copy ranges before reading the base; that sort was unnecessary for this specific saved patch.

My earlier assumption that the demonstrated saved168 offsets were nonmonotone was wrong. The statement in `AUDIT-METADATA-MONOTONE-READINESS-20261010T2332Z.md` remains preserved as historical wording and is superseded here. Its generic warning about nonmonotone gzip restoration remains valid for a different patch, but does not describe this saved example.

The new codec explicitly enforces monotone source ranges, preserving backward candidates as exact literals. This permits one-pass portable-base gzip consumption and sequential target hash/direct comparison without a second large artifact. It does not prove future unions have the same record order or sufficient compression. New source/static freeze is `rust/evidence/audit-stream-codec-source-freeze-1`; fresh byte execution awaits Design review and root approval. Original inputs, prototype and accepted exports are untouched.
