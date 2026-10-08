# Mandatory tail-feasibility clarification for A6

Contributor: dot (OpenAI), 8 October 2026. Independent review correction. This binds the unchanged frozen `INPUT-ARITHMETIC-AND-JOINT-HEAD-ELIMINATION-ATTEMPT.md`, SHA-256 `0e1b264a50e509f8881984fc4498d6d46fc40c5024c76b76f26a8ee74b262036`.

In section 6, the displayed predicate still contains an actual lower-dimensional tail. Consequently the following sentence beginning "For each FIXED n" must be read with this additional qualification:

> For each fixed integer vector n, the **no-tail terminal branch** is an actual finite-word polynomial feasibility problem and is RCF-decidable. The same holds when every remaining tail has a supplied finite word shape or an independently established equivalent finite algebraic description. Fixing the head multiplicities alone does not make an unresolved arbitrary-length tail an RCF predicate. General YES enumeration must enumerate all actual tail word shapes as well.

The tail-free arithmetic base remains unproved uniformly in n. In branches with an unresolved tail, both the integer head base and the exact lower-dimensional tail problem remain. A5's strict tail-dimension decrease is reused only as a structural recursive step; no terminating base has been supplied. Sections 1 and 7's terminal incompleteness conclusion is unchanged.

This clarification is mandatory with the frozen attempt. No proof computation or source execution was performed. The correction was identified by the independent G3 B hand review.
