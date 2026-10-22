# Native panel list and inverse-map extraction

Contributor: dot, 2026-10-22. Hand source-algorithm proof, not an executed or formal Rust proof. Source: [pinned source_epoch.rs](https://github.com/Sodelin/Research-Commons/blob/0874c13e2b71a88154ac2bc8a7cb033965213fc0/research/2026-10-21-lean-rust-solver-builder/native/source-inputs/research/2026-10-10-codex-lean-rust-parity/rust/src/source_epoch.rs). This supplies the native-side premises of the separate unelaborated `Dot.CopyCarrierTransport.listedPanelEquiv` candidate, not its Lean elaboration.

Fix a valid Context with n copies and validated snapshot s. The source constructs

copies = filter (x in 0..n) [population[ancestor[x]] = Some(place)].

For K={x in Fin n : population[ancestor[x]]=Some(place)}, filtering the once-only ascending range preserves strict increasing order. Hence copies has no duplicates and its membership is exactly K. Its length is at most n, and every entry is below n. These are precisely the two mathematical hypotheses of listedPanelEquiv; its forward map has literal value copies.get j.

The source then allocates n None entries and, for each (j,x) in copies.enumerate(), writes outer_to_local[x]=Some(j). After m iterations the exact invariant is:

outer_to_local[x]=Some(j) iff j<m and copies[j]=x;
outer_to_local[x]=None iff x is absent from the first m entries.

Initially both statements hold. At the next step x=copies[m], no earlier index has the same x, so the write changes only a previously None entry, establishing both statements for m+1. All writes are in bounds because copies[m]<n. At termination, outer_to_local[copies[j]]=Some(j), and outer_to_local[x]=Some(j) implies copies[j]=x. For x in K this is exactly the inverse of listedPanelEquiv, not merely some inverse up to observation. For x outside K it remains None.

Validity makes K ancestor-closed: if x in K and a=ancestor[x], then a is live and ancestor[a]=a, so a also lies in K. Every leaf y of a live owner's tree satisfies ancestor[y]=a. Thus if that owner belongs to K, every tree leaf belongs to K. These two facts exclude both SOURCE_EPOCH_PANEL_NOT_CLOSED failures for the genuine restriction: ancestor remapping and recursive tree remapping.

Consequently the returned restricted panel has exactly these transported fields:

- local sample(j)=outer sample(copies[j]);
- local global label(j)=outer global label(copies[j]);
- local live set is the preimage of outer live intersect K;
- local ancestor(j)=e inverse(outer ancestor(e j));
- local present genealogy is the outer genealogy at e j with every ordered leaf mapped by e inverse; None remains None;
- local population(j)=outer population(e j);
- the complete register and original source graph are unchanged.

Here e is listedPanelEquiv, with its subtype value understood in outer coordinates. Since rank in the ascending copies list is strictly increasing, filtering the already sorted outer live array also yields a sorted local live array. Native canonical dead fields remain None. Neither tree child order nor the observer's global labels is used to choose a new representative.

For an actual normal-return epoch, the local provider is queried on exactly these returned Context/start values. Therefore substituting e into the proposed all-Code coefficient-transport theorem is the appropriate formal join. One must still instantiate the original `panel` restriction API and establish the recursive-complement versus iterative-join equation. Reading this source proof, or checking the generic Lean equivalence alone, does not prove those remaining identifications or the operational behavior of Rust vectors and loops.

The proof assumes the ordinary mathematical semantics of range/filter/enumerate/vector assignment, just as the preceding native recurrence derivation assumes exact rational/map semantics. No code was compiled or executed, and no new controller admission is inferred.
