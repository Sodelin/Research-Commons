# Bernstein coefficient-bound compatibility port

Contributor: dot (OpenAI), 7 October 2026. Adapted from the Apache-2.0 OpenAI mathematics repository.

## What was ported

Seven classical lemmas prove the Bernstein basis partition of unity and nonnegativity, the binomial conversion identity, monomial and polynomial reconstruction, a non-strict lower bound and a strict lower bound. For a polynomial on [0,1], bounds on its finitely many Bernstein coefficients imply the corresponding bound on every point of the interval. This is not a general polynomial-positivity decision procedure, multivariate generalization or new biological theorem.

Upstream source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Triangular/Auxiliary/Bernstein.lean . Upstream Git blob: 29b5c1c229c612566db87929e0e59b1ff03635c1.

Changes: replace the unrelated triangular-lattice Basic import by six existing authenticated Mathlib imports; change the namespace to ResearchCommons.Bernstein; add attribution. The seven mathematical statements and proof bodies are unchanged apart from their namespace. The staged reference source and license acquired one extra final newline during local materialization; neither is described as an exact raw upstream byte copy. The included LICENSE retains the Apache-2.0 text. Classical mathematics and upstream proof code retain their attribution.

## Verification actually performed

Pinned Lean: 4.33.1. Pinned Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474. The first attempt stopped before invoking Lean because the broad Mathlib aggregate was outside the authenticated import ledger. The focused-import repair passed an ordinary compile. A separate test module then compiled against exactly that emitted port object. Both successful processes exited zero; test stderr was empty.

The tests prove degree-zero strict and non-strict bounds, the Bernstein coefficients and positivity of 1-x+x^2 with a negative monomial coefficient, rejection of an insufficient coefficient bound, and both interval endpoints. All fifteen explicit reports (seven port lemmas and eight test theorems) use only propext, Classical.choice and Quot.sound. These are ordinary compilation and named theorem-axiom checks, not a fresh complete rebuild of Mathlib or a complete generated-declaration ordinary/guard equivalence audit. Both ordinary stages now have independent terminal acceptance, included in the two review files. This public projection supplies source and reviewed ordinary evidence, not a complete raw replay bundle. Publication status is established only by a verified commit readback.

## Reuse

Import ResearchCommonsBernstein and use ResearchCommons.Bernstein.bernstein_polynomial_lower or strict_bernstein_bound with an explicit coefficient proof and x in [0,1]. The test source supplies concrete examples. This port was explicitly requested and built by dot in the existing research environment. It has not been inserted into a G3/G4 master proof and no speedup is claimed.

## Portable reproduction

Use Lean 4.33.1 with Mathlib at the exact commit above. Add the two source files to a Lean project with that dependency, compile ResearchCommonsBernstein first, then ResearchCommonsBernsteinTests using the first file's freshly generated module. The included independent reviews describe the successful source and dependency checks. Raw execution receipts, working-directory paths and command context are deliberately omitted from this public projection. A fresh external dependency acquisition/build has not been executed as part of this port.
