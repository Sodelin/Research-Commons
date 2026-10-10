# The supplied-word table correspondence

This addendum preserves the reviewed [word contract](WORD-REFINEMENT.md), SHA256 `dabc36aef7265cef2efeac982b6f191540eaf12f809045bce75e6e5161952458`, and its frozen fixture inputs. It records an additional formal bridge; it changes no request, coefficient, runtime, limit or admission gate.

The inherited [G7SelectedKernelPolynomial](../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7SelectedKernelPolynomial.lean) defines `epochTable` by `Classical.choose` from `actual_full_epoch_polynomial`, evaluated on a chosen source representative. Its theorem `actual_selected_epoch_table` identifies physical evaluations with the actual selected kernel. The inherited [G7SymbolicProgramPolynomial](../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/G7SymbolicProgramPolynomial.lean), SHA256 `17619976e462ada4686ab1d018d67c712c69defbf20e1d9a8a97299f7dbb7230`, composes these tables as `stepPolynomial`, `wordPolynomial` and `naturalWordPolynomial`.

The checked [full-epoch support extractor](../reuse/sources/G7FullEpochSupport.lean), SHA256 `188177cf95a52762d2f37148c7db2c1d9120d16d5764eabe1927854d7c766d0a`, proves equality of its entire polynomial to the unchanged effective `fullCoefficients`/`epochCoefficients`. That is stronger than fixture agreement, but does not by itself identify the extractor's coefficient table with the separately chosen `epochTable` or transport arbitrary literal entering witnesses to its chosen representative.

The exact remaining bridge is:

1. Identify every canonical native full selected view and literal range witness with the actual `SelectedIndex`/`projection`, including ordered genealogy, original population and the complete register.
2. Prove the effective epoch coefficient row is independent of the admitted representative in the full selected fibre, and equals `epochTable` as an `MvPolynomial`. Existing actual source projectivity already identifies the physical PMF evaluations; do not reprove that abstraction theorem.
3. Bind encoded conditional node/exit rows and the once-drawn natural initial mixture to the inherited `nodeTable`, `exitTable` and `initialPolynomial`, with original γ=P(parent1).
4. Transport these coefficient equalities through variable renaming, finite selected-fibre sums and the word recurrence. Repeated slots remain the same variable; initialization precedes the word once.

A possible route to step 2 is polynomial uniqueness from physical evaluations, provided the **single-epoch** survival image contains a suitable open set and the same representative is retained. The image premise and real-to-rational coefficient transport must be proved. Equality on the physically constrained **whole-word** slot bank cannot simply be treated as equality on an independent cube: all slots share original rates and durations. Prefer per-step identification followed by exact composition.

The private Rust comparison currently tests every coefficient against an independent exact finite-code generator reference, with literal witness and full-register checks. Until the bridge above is checked, describe it as internal coefficient-reference agreement, not extraction of the noncomputable chosen table or a general native refinement theorem. Optional ancestral completion, generated-calendar admission, physical-bank evaluation and original observation admission remain separately gated.
