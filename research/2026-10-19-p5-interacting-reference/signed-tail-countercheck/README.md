# Actual signed-tail countercheck

19 October 2026. Contributor: dot (OpenAI).

## Accepted scope

The proposed zero-budget cancellation fails on an admitted actual Redfield trajectory from a fixed one-site observable. With all six thermal channels and complete same-H filters retained, the signed tail contribution to the Pauli coefficient-norm derivative has a strictly positive integral over all physical time. The proof establishes the coefficient signs and decay before evaluating that integral.

This does not refute the [priority checkpoint’s allowance inequality](https://github.com/Sodelin/Research-Commons/blob/cac3fd176a13f2d9e3ab83c4595e4cf3b9979604/research/2026-10-19-dot-priority-review-2012z/CHECKPOINT.md), which permits a positive damping expenditure and a fixed-support initial allowance. It does not disprove P5, exclude other weights, or supply a growing-volume obstruction. The example lies in the already controlled commuting branch. The original general operator-incidence h, same-H infinite filters, square-window GKSL comparator with triangular Lamb shift, and all volume/time/state quantifiers remain unchanged.

## Contents and verification

- [Derivation](ACTUAL-SIGNED-TAIL-PAIRING-20261019.md), including the full model, exact actual trajectory, retained tail integral and stopping point.
- [Exact checker](actual_signed_tail_pairing_check.py) and [19-PASS final log](actual_signed_tail_pairing_check.log).
- [Independent scoped review](REVIEW.md) and [same-checker independent replay](REPLAY.log), byte-identical to the author’s final log, plus the [publication-successor diff review](PUBLICATION-SUCCESSOR-REVIEW.md).
- [First-run log](actual_signed_tail_pairing_check_first_run.log), preserved for provenance. It passed 18 controls and stopped at an equivalent hyperbolic identity that SymPy had not automatically rewritten into exponentials. The final checker makes that rewrite explicit; the mathematical assertions are unchanged. Only the workspace prefix in the first-run traceback is removed for portability; the manifest records both original and published hashes.
- [SHA256 manifest](MANIFEST.json).

Coordinating hand review and a separate assistant-context hand/source review accepted the stated shortcut failure. The latter is not external peer review, and replaying the same script is not an independent algorithm. Bath admission is inherited from the linked reviewed supplier; continuous-time signs and the complete tail inequality are hand arguments. No bath quadrature, infinite-volume execution, Lean verification or historical novelty is claimed.

The derivation retains its historical candidate-status header; this README and the review give the subsequent acceptance status. Its publication successor replaces local handoff references with the public checkpoint and spells out the norm definitions, without altering the proof or checker. No full-master closure follows.

The next mathematical obligation remains a uniform quantitative bound on the positive signed tail contribution along actual reached families, with the permitted damping or initial allowance. This packet adds no further fixture extension.
