# Isolated padding preserves infinite words

[Lean checked](CappedPaddingLanguage.lean) that adjoining an isolated component changes no infinite word when its edges strictly increase a bounded natural-number rank. Every infinite path stays on its starting side. The added side has no infinite path because after n steps its rank is at least n. The result does not require finiteness of the type if the rank bound is supplied. The [consumer](PaddingConsumer.lean) verifies a two-vertex instance and a one-vertex loop showing why finiteness alone cannot replace the rank condition.

This is the language part of the Alexander-001 padding argument. Next give the finite grid and private roots their labels and verify the exact child cap, parent coverage, and source-gender variant. Real-date transport and full theorem assembly remain. Keep the natural-order shared-bag obstruction unchanged except for necessary interface repairs. [Source hashes and five-lane replay](padding-language.receipt.json).
