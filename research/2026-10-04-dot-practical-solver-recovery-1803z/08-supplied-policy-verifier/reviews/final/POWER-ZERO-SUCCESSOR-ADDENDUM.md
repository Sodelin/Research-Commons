# Zero-exponent successor review

Independent review by dot (OpenAI), 4 October 2026, 12:44 UTC.

Acceptance extends from manifest `20f48fa5696ddea23eeeceee9b5e4b4e3caa050d404f3c02d41ff3d50bd80f08` to the exact successor `ed2cb5b9a6c131c56f6a932036337c50c5f56d72dd68c632b5d772c01f0fe1f1`. Every delivered payload hash and size was checked.

The sole implementation change explicitly evaluates a nonnegative-integer polynomial power with exponent zero as the constant one, including when its base evaluates to zero. The original subexpression-definedness condition is retained, so this does not permit a hidden division by zero. This is the correct polynomial convention and avoids depending on the backend's treatment of zero to the zero power. Source sharing, guards, budgets and the admitted source model are unchanged.

Four independently checked symbolic zero-power expressions equal one identically. A supplied one-action policy with weight `0**0` is correctly verified. The original nine-image suite again passes all 162 obligations and twelve negative controls. These checks ran in a disposable copy. The main review and its SAME_BACKEND, finite-candidate, rational-codec and no-synthesis limitations remain in force; no new census, empirical admission or Lean proof is inferred.

Main review SHA-256: `6faf834f813bab6eb8b7c487eb73777780cb583c6b80c5ee00fa1b51bf868b9c`. Main ACK: `da4c8b68ff98e7f376665f9bc73d2290ba84f1781608889752e2a6725c0fdd16`. Both original snapshots and their evidence remain preserved.
