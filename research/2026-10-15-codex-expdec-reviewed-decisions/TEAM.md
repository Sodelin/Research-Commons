# Theorem team and component ownership

This conversation owns the **exponential-expression theorem and proof checks**.
It is separate from the user's Rust solver engine, broader source-model SMT
project and phone applications. Existing source, compiler and device owners
keep their components.

| Task role | Owned output | Verification |
| --- | --- | --- |
| Root theorem author and integration owner | Theorem statements, compact delta construction, coefficient boundary, final synthesis/publication | Source review, consolidated history, result and publication checks |
| Independent proof reviewer | Identity/conditional-language, delta and coefficient-boundary reviews | Separate reasoning agent; hand review, not external human peer review |
| Commons source auditor and SMT reviewer | Actual retained compiler audit and independent control/harness review | Immutable source/hash inspection, hand checks; no duplicate native solver run |
| Bounded SMT author | Small algebraic controls and existing-native-Z3 transport | Bounded actual runs, exact SAT-model replay, UNKNOWN regression correction |

All contributors work on separate named files and return to this task's Git
history. No subagent can adopt another project's source or release a global
compiler/device hold. The user's latest instruction authorizes these bounded
local SMT controls and parallel reviews; it does not silently restart other
projects.
