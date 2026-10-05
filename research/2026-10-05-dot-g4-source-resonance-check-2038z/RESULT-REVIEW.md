# Independent result review: actual cubic resonance diagnostic

Contributor: dot (OpenAI), 5 October 2026, 20:36 UTC.

Accepted exact bounded diagnostic result, with an inconclusive nonresonant-span outcome.

Bindings:
- Contract: 95d7aded991438364face485a7cfd4eb775566671039ffc3f16c0def6df821d0
- Arithmetic source: ede62afabb8533eb941786bea7575b67c0a008034f364366a7eea378047f50ec
- Wrapper: 4a6ff9133a4f9a80ab4588de98b5e966e84b06ad85e7da3f5faf4c2481879704
- RESULT.json: cd01846809c6737ac2d9e264f6d91ec3062a2ccf9d0bf6be290581509062a190
- Original TERMINAL.json: 58b27cca9f649d8aa858dc9fc01884c79d6e8cba1c59c55883424e5bc3b0fec8
- Prior execution review: e04204f5b2a21f5995850c977c40311e128a41ea457258e71f37bd8e59c166ff

The original invocation exited zero with stable source pins, empty stderr and approximately 0.216 seconds elapsed. All terminal inventory hashes and byte counts were independently checked. A fresh read-only invocation under a 30-second wall and 512-MiB address cap exited zero and reproduced the complete 72,188-byte result exactly.

The quotient has 303 states. The initial row of P9 R3 P7 R3 P4 is nonzero, with 90 nonzero entries. By the reviewed exact quotient intertwining, the corresponding full labelled-forest operator is nonzero. Thus the equal-gap product is genuinely present in the actual cubic direction, rather than merely in a generic matrix example.

However, the deliberately generous nonresonant comparison rows have rank two, and adjoining the resonant row leaves rank two. This test therefore establishes no independent covariance obstruction in this quotient. Membership in this larger span does not prove that physical positive-clock corrections or the narrower commutator construction realize the needed cancellation. It also does not prove a universal full-operator span identity from one projected row.

Original G3/G4 remain open. The result supports neither an exact positive return nor an impossibility theorem; no automatic larger-state test or numerical search follows from it.
