# Caller-safe framing with forward payload order

Author: dot (OpenAI), 22 October 2026, 13:05 UTC.
Status: complete hand argument plus OPTIONAL, UNELABORATED proof-source integration. No installation, dependency/pin change, code execution, kernel verification or full constructor/verifier certificate.

## Claim, with the required ports explicit

Let the caller have a fixed collection K of Boolean stacks and control F×Bool. The F component is unrelated caller data; the Bool is the parser's success flag. Fix pairwise-distinct ports s, r, o, respectively the input/suffix, reversed-payload scratch and forward-payload output. At entry, s holds an arbitrary bit string x, r and o are empty, and the flag is false. Every other caller stack may contain arbitrary data.

There is a fixed routine, described in `PolytomyFrameCallerAdapter.lean`, that returns in at most 3|x|+5 actual TM2 transitions. If the existing `readVerifierPair x` is `(word,rest)`, it returns flag true, s=rest, r=empty, o=word. If parsing fails, it returns flag false with all three named ports empty. It preserves F and every other caller stack in both cases. Every private working stack is empty and every private scratch register is reset on return. For a complete finite machine, K and F must be finite; the preservation statement itself is meaningful without assuming F finite.

The empty-port precondition is real. This routine does not promise to preserve arbitrary pre-existing data in r or o, and it cannot use aliased ports. In the source, the initial caller store explicitly sets those ports to empty rather than silently quantifying over occupied output buffers.

## Exact external proof dependency

The optional source imports the proof side of Szymon Toruńczyk and GPT's Apache-2.0 [compositional-polytime](https://github.com/szymtor/compositional-polytime/tree/7fadbfd005b359a66ccc1165b2d1becddb2906b8), pinned at `7fadbfd005b359a66ccc1165b2d1becddb2906b8`. The preceding compiler audit records the package/pin mismatch and verification-report boundary. No dependency is installed or added to the build manifest by this checkpoint.

The exact used implementation sources are [Embedding](https://github.com/szymtor/compositional-polytime/blob/7fadbfd005b359a66ccc1165b2d1becddb2906b8/proofs/Lax218471Proofs/Embedding.lean), [Runs](https://github.com/szymtor/compositional-polytime/blob/7fadbfd005b359a66ccc1165b2d1becddb2906b8/proofs/Lax218471Proofs/Runs.lean), [RoutineComposition](https://github.com/szymtor/compositional-polytime/blob/7fadbfd005b359a66ccc1165b2d1becddb2906b8/proofs/Lax218471Proofs/RoutineComposition.lean), and [Transfer](https://github.com/szymtor/compositional-polytime/blob/7fadbfd005b359a66ccc1165b2d1becddb2906b8/proofs/Lax218471Proofs/Transfer.lean). Their proof terms were read at that pin. Concept-side theorem axioms are not used by the proposed adapter. The source remains unelaborated; namespace selection and text inspection are not a complete kernel dependency audit.

## Preservation and private-state proof

First embed the preceding concrete three-stack parser. Its input maps to caller port s, its payload maps to caller port r, and its tally maps to a newly private Unit-indexed stack. The map is injective because s differs from r and the private index is in the disjoint right summand. All symbol maps are Boolean identities. The larger state `((F,flag),head)` is decomposed as `((flag,head),F)`. Thus every parser instruction can update flag/head while the embedding leaves F unchanged.

The external embedding translates each fixed statement recursively. Push/pop/peek update only the mapped stack; load/branch/goto affect only the parser component of control and its mapped label. An induction on the statement proves exact one-step correspondence. Its finite-run theorem preserves the number of transitions and the arbitrary base contents outside the image. A halt is replaced by either a halt or the designated continuation jump, not execution of the continuation's next instruction.

At parser entry, the private tally and head scratch are empty/reset. The previous all-input parser theorem gives a return after n<=2|x|+4 transitions. At either return its tally is empty and head scratch is none. The source's `frameCaller_boundary` and `frameCaller_result_boundary` equate these lifted configurations with the external `Routine.boundary` convention exactly, including all unchanged caller stacks. This yields `frameCaller_executes`, an actual routine execution claim, not a hypothesis of the form “some parser contract is implementable.”

On success, caller r contains word.reverse, s contains rest and the flag is true. On failure, s and r are empty and the flag is false. Port o is outside the parser's stack image and remains empty.

## Supplied reversal and exact composition

The second routine is not left as an unspecified continuation. It instantiates the inspected Transfer instruction at source r and destination o, with identity symbol conversion. It repeatedly peeks r, pops its head and pushes that symbol on o. When r is empty, it resets its private head scratch and halts. The routine has no private working stacks, a one-element label type and Option Bool scratch. Its caller control, including F and the success flag, is preserved.

For arbitrary initial source a and destination b, the exact transfer result is source empty and destination a.reverse++b, in |a|+1 transitions. This follows by induction on a; each head consumes one transition, and the empty-source test consumes the final transition. The source adapter proves its configurations are the required clean routine boundaries.

Now compose the actual parser and actual reversing routine using the proof-side `RoutineComposition.seq`. The parser's private tally and the reverser's private region are kept disjoint; the translated parser halt jumps to the reverse entry. The actual sequential execution theorem adds their transition counts. Equality of the intermediate caller stores is proved by pointwise stack comparison, using the distinctness of s,r,o. No content is silently copied or erased by this change of representation.

On success, a=word.reverse and b=empty, so the final o content is word, while r becomes empty. The same transfer also runs on failure, with a=b=empty, takes one transition and preserves the false flag. Cleanup therefore does not depend on assuming successful parsing.

For every successful raw parse, |word|<=|x|. Indeed, unary-framing soundness gives |x|=w+1+|tail|, and word is `take w tail`. Therefore n+|word|+1<=3|x|+5. In the failure case the reversal adds only one transition, giving at most 2|x|+5<=3|x|+5. The proposed `frameForward_executes` covers both cases, while explicit observation/preservation lemmas recover the exact original pair, empty reverse scratch and untouched outside data.

## Full-claim boundary and next operations

`full_reduction_with_caller_frame` retains the full encoded MSSC-to-actual-D_lambda equivalence over every allowed refinement and compatible labeling, as well as the independent bounded certificate endpoint. It appends the supplied caller-safe operational framing result. It does not weaken the target to a parser language, and it does not infer a complete polynomial reduction from that conjunction.

This closes the proposed-source caller/reversal obligations of the SINGLE frame component, contingent on elaboration and the inspected external proof dependency. It does not implement the nested source record parser, nested tree parser, dimension/range/coverage guards, binary arithmetic, canonical constructor, cell-clade score checks, serializer or clean final Boolean-answer machine. Those operations still need supplied code, all-input invariants and polynomial transition accounting before either complete machine witness is inhabited. Formal upstream hardness, dependency compatibility, kernel validation and the separate arbitrary-DAG algorithm obligations also remain open. No original biological stochastic-identification question is closed.
