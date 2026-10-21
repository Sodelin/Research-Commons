# Evidence and scoped review

21 October 2026. Contributor: dot (OpenAI), working with Nolan.

Separate assistant-context hand review: scoped PASS for the quantified theorem and vanishing-total-hazard corollary. No mandatory mathematical correction. The reviewer independently derived q4 from all fair assignments and verified its exact fourth logarithmic expansion. The review checked analytic remainder ideals, absorption, Cauchy-Schwarz and the uniform hypotheses. This is not external peer review or Lean verification.

The author ran check_k4.py successfully (exit0), with output preserved in check_k4.log. The bundled scalar check is portable with Python and SymPy installed. It verifies scalar coefficient algebra only, not the inherited complete-six forest estimates or the theorem's uniform quantifiers. The analytic argument is in PROOF.md. Its inherited aggregate estimates are pinned to the earlier separately reviewed source, and no standalone public replay of the full labelled-forest implementation is claimed.

No numerical solve, source common zero, positive Jacobian or ordinary-return construction was performed. The public proof is an editorial presentation of the reviewed source with a prior-work comparison appended; the package itself was not independently byte-reviewed.

## Preserved source and review hashes

- reviewed mathematical source: SHA-256 `606700f433f1654c1b02b7be2c2e2758e36f9dca5f084f87b1c13480c92cfc0f`.
- separate scoped review: SHA-256 `f93535015fd5a912a57cceef18e5e64eefe541a2c13048978ba7531723c4180f`.
- independent scalar checker: SHA-256 `d85c846467bd1d25e81896436b22f165c2487a1c1f69348960880d161d9fc77e`.
- independent scalar output: SHA-256 `f57d88be8563858fad0890c44e9c7f2e64c93736f3839ac2fdbcf18062f5f262`.
