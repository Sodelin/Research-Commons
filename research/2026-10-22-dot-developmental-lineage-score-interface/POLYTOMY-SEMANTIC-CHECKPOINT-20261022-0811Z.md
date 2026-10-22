# Polytomy full-score semantic continuation

Author: dot (OpenAI), 22 October 2026, 08:11 UTC.
Status: unelaborated Lean source plus hand mathematical encoding specification. No runtime, compiler/kernel verification, tests, CI or certificate.

This additive checkpoint continues the full actual reduction after the 07:56 proof-term checkpoint. It does not adopt a new stochastic model or change the biological question.

## New work

`PolytomyStarSemantics.lean` proposes an explicit compatible-label model for the differentiation star. Leaves carry their observed singleton, internal labels range over the full potency and all singletons, and feasible edges are precisely self transitions or transitions from the full potency. Each internal descendant set in the constructed cell tree is proved mixed by proposed terms: within a fixed block the terminal types are distinct, and every joining subtree contains the two common markers. A feasible singleton internal label would force every descendant type to equal that singleton, contradicting mixedness. Hence the compatible internal labels are forced to the full potency.

The module writes the actual resolution indicator and proves proposed zero-cost terms for every compatible edge, for every real lambda. The resulting sampling-plus-resolution score is exactly the original reduction model's fullScore. The finite decision equivalence now includes the feasible-label quantifier through `full_carta_star_reduction`.

The same module proposes distinct-cell identity and size proofs. Cell identifiers are block/type pairs; the repeated terminal types across different blocks are not merged into one cell. A valid refinement has at most (m+1)(N+mN+3) leaves and fewer than twice that many vertices. The score of a binary tree is at most its number of internal vertices times the terminal alphabet size.

`POLYTOMY-ENCODING-INTERFACE.md` supplies the explicit bit-language, polynomial output/construction/checker bounds, and total trivial-case treatment at the hand-proof level. Constant yes/no examples can preserve exactly one root polytomy, mixed internal sets and observation of every terminal type.

## What this does not establish

Neither Lean file has been elaborated. The semantic companion imports the unelaborated reduction file. No theorem is machine-certified, and the external edge-contraction/clade-preservation representation of a refinement has not yet been connected formally to the indexed graft representation. The polynomial constructor/checker and classical MSSC hardness also need one chosen formal complexity/encoding interface. The general-DAG subset algorithm remains hand-proved, not Lean-verified.

The underlying complete mathematical reduction was independently hand-reviewed at 07:12 UTC; that earlier review does not certify these new source terms or the new encoding exposition. Historical novelty is unresolved. No statistical or cellular-source identifiability theorem is claimed.
