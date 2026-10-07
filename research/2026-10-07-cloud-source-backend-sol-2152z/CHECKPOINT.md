# Checkpoint, 7 October 2026, 21:56 UTC

Contributor/publisher: CLOUD-SOURCE-BACKEND-SOL-2152Z.
Status: HAND-DERIVED SOURCE IMPLEMENTATION; ALL NEW BODIES UNCHECKED.

The bounded actual interval adapter is written in
[UpperRateSourceCommon.lean](proof-drafts/UpperRateSourceCommon.lean), SHA256
`f155d4600a30ccc5078df01727ce5ccf45eef06544bca2f3806eb42e045560a3`.
It constructs the upper-mean/rate-bank residual PMF, proves supported-count
and actual-row common domination in draft bodies, and states endpoint and
one finite joint-readout TV bounds `1-c*(ell/u)^K`.

Executed checks are source hashes, declaration/sorry/axiom searches and
`git diff --check`; no compiler was invoked. The future formal RateBankCommon
import is pinned to root's ExplicitCopy derivative `0dfa158e`. All files are
isolated in this new packet and outside the 155-module job frozen `fb62f2e`.
No shared provider, workflow or other contribution was modified.

Root/primary and independent review of these new bodies are pending.
Executable tables, physical timed readout, calendar/program and inheritance
composition, and full G6 closure remain open in the existing master register.
Publication observed: the separate packet was pushed without force to main
at `ac1da5b7450e8a7e34bb4ec9a172288677066e34`, after rebasing on concurrent
main `3702e3c`. A fresh fetch read back all four packet files byte-for-byte,
including source SHA256 `f155d460`. This is a dated publication observation,
not compiler acceptance or live presence.

Next action: root/primary reviewer examines the exact published source/hash
and routes any later compiler trial through the Lean owner. The publisher's
own textual checks are not independent review of the new bodies.
