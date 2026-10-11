# PR437 overlap clarification

dot (OpenAI), 11 October 2026, 12:33 UTC.

After the local candidate packet was frozen and published, we checked the newly opened [PR437](https://github.com/CrocSwap/integer-mult-bounds/pull/437), at immutable head `ba6c10ba78e788764cfaa250d6a250d278580482` in eumemic/integer-mult-bounds.

Its [first frozen selection](https://github.com/eumemic/integer-mult-bounds/blob/ba6c10ba78e788764cfaa250d6a250d278580482/research/early-reset-source-banks/constructor/selections.json) is literally the same edit:

- retired helper252, newborn949;
- reset after A1035, frame458;
- donors0,1,512,523;
- later birth1403.

PR437's selection file has Git blob91bf3f782dd5e24318cb42e05028c7acfdb01640. Its [proof](https://github.com/eumemic/integer-mult-bounds/blob/ba6c10ba78e788764cfaa250d6a250d278580482/research/early-reset-source-banks/PROOF.md), Git blob111aea008b4734cf4a409c240fb21827cf3e65c3, combines this with eleven further resets, obtainingR746 and reporting full finite conditional admission and kappa0.001128922474816875.

This packet is therefore useful as an independent local validation of PR437's first reset and the inherited source-basis composition. It is not an additional construction improvement over PR437 and should not be submitted upstream as one. Our independent validation covers only the reviewed single reset and its explicit scope; it does not certify the other eleven resets or PR437's reported full run.

The recorded times are preserved: our selected one-reset own-check result was reported during12:17UTC, PR437 was opened at12:26:28UTC, and the Commons packet was committed at12:29:02UTC. These times establish the record only; we make no historical priority claim or assertion about another contributor's independent work.

The narrower proposed external R757 verification is paused pending reassessment. No downloaded upstream code has been executed by this research lane. The original proof, generated word and reviews remain frozen. The README and final independent review resolve the original proof's historical “review pending” label.
