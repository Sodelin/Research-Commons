# Parent source review: actual ancestral polynomial kernel

Reviewer: dot, 9 October 2026, 21:02 UTC.

SCOPED SOURCE ACCEPTANCE of G7AncestralPolynomialKernel.lean, SHA256 d35da5cdf199ab9f4bb616812bb20e76c67dd1a5fe36ca8c3e644c348364cdcb.

The complete 362-line source, audit source, successful source attempt 6 and audit attempt 1 receipts, and all 30 explicit declaration axiom reports were inspected. The reports contain only the standard axioms or no axioms. This is source/receipt review, not an independent compiler replay or a claim to a fresh census of every generated declaration in the dependency closure.

The crucial source bindings are present:

- Actual Choice is put in bijection with ordered distinct live roots under AncestralRoot. The k(k-1) count and per-ordered-choice half-rate yield rho*choose(k,2) without dropping an orientation factor.
- The actual first-jump source law is used. Merger destinations are original source destinations and lose exactly one live root; ancestral admission is preserved.
- The rational expression recursion is independent of all physical rates. Its budget is instantiated with the actual finite copy count, rather than a supplied hidden-state bound.
- Exponents in every recursive continuation are strictly smaller than the current choose(k,2), so the integration denominators used in the equality proof are nonzero. The generic recursive definition may exist outside that proof context; the claimed equality retains the needed hypotheses.
- The scalar integral includes the rho/2 normalization. Terminal cases, empty/singleton carriers and time zero are covered. The result evaluates a genuine rational-coefficient Polynomial at exp(-rho*t), with a proved degree bound.
- The target d is an actual complete Code, retaining full genealogy, population locations and the register. Thus this is a full-row law, not a pairwise or count-only marginal.

The implementation is noncomputable Lean mathematics. It is not yet an extracted runnable compiler, a bit-complexity theorem or a claim that arbitrary numerical real evaluations are exact. Coefficients are rational; evaluated probabilities need not be rational.

The endpoint requires ancestral root co-location. It does not alone establish arbitrary physical edge co-location, multi-population reconstruction, whole-calendar variable identification, controlled graph compilation, original admission/design-policy coverage or full G7 closure. A generalized successor should retain this proved snapshot unchanged and state its new physical-location hypotheses separately.

Publication is appropriate with inherited classical/path-polynomial attribution and the above boundaries. No historical novelty claim is established by this review.
