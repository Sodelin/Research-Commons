# Original verifier: physical legal-node mask and exact clade navigation

Author: dot (OpenAI), 22 October 2026, 23:16 UTC.

Status: hand derivation and OPTIONAL UNELABORATED Lean source. No research-code execution, compilation, build certificate, independent review or novelty claim. This continues the SAME original independent verifier. It is not the complete VerifierMachineWitness.

## 1. Why a mask is needed

The previous checkpoint exhibited a false-positive route: a valid leaf's unary payload can itself contain a parseable tree suffix. Therefore an arbitrary successful tree-prefix parse cannot establish that its starting byte is an actual node. The repair below follows the original grammar's syntax phases, retaining every original byte and both unary leaf fields. Arbitrary binary fixed trees remain allowed; no comb-only or constructor-origin promise is added.

For a raw leaf with codes (a,b), the mask is true followed by a+b+2 false bits. For an internal node it is true followed by its left and right masks. Thus every actual node token is marked, but every unary payload bit and its delimiter are unmarked. The mask length equals the original tree-word length.

## 2. Exact all-word semantic interface

`PolytomyRawTreeNodeMask.lean` supplies rawForestMaskParse using the same original rawForestSkip grammar. Projection onto the returned suffix is exactly rawForestSkip on every word and fuel, not only on valid encodings.

For every word b, q, suffix r and mask z, the proposed exact theorem says:

    rawForestMaskParse (length b) q b = some (r,z)
    iff there exist exactly q raw binary trees ts such that
       b = rawForestWord(ts) ++ r and z = rawForestNodeMask(ts).

The proof combines the all-word raw grammar theorem with the mask parser's exact encoding theorem. It also yields length(z)+length(r)=length(b). Specification fuel is proof-side recursion, not machine control.

`rawNodeViews(T,r)` enumerates each real subtree U together with the suffix after U in the surrounding word. For a left child the suffix includes the right child's full bytes, so intervals do not accidentally omit sibling data. The mask-driven scan `rawMarkedSuffixes` satisfies the exact identity

    markedSuffixes(bits(T) ++ r, mask(T) ++ z)
      = nodeViews(T,r).map(viewSuffix) ++ markedSuffixes(r,z).

The leaf proof skips the entire all-false unary payload mask. The internal-node proof applies the two induction hypotheses with the correct sibling suffix. No arbitrary parseable interior suffix is selected. Mapping each returned view to its subtree's leaf list gives exactly the existing scanClades(T), in the same preorder, and the number of views is the actual vertex count.

This identifies the same fixed-tree clades the independent checker must preserve. It does not by itself implement the nested cell-set comparisons or the score.

## 3. Actual finite mask-logging program

`PolytomyTreeMaskMachine.lean` emits an explicit three-Boolean-stack, five-label TM2 program. Input, pending slots and the reversed mask are physical stack data. Finite control remains Bool times Option Bool.

- read logs true only after it actually consumes a node token. It then takes the same original internal/leaf branch as the previous grammar machine.
- block and type each log false after every actually consumed unary-field bit, including its terminating delimiter.
- a missing token or delimiter logs nothing for the missing byte, then clears both pending slots and the accumulated mask before returning failure.
- a zero pending count succeeds without reading or marking the remaining suffix.

The program is fixed, with no tree-shaped code generation, natural-number control register, host parser oracle or assumed payload operation. It appends physical marks by actual TM2 push instructions. Each label has uniformly bounded statement size.

For arbitrary starting input length L, physical pending count q and existing reversed-mask accumulator o, the proposed all-word run bound is

    3L + q + length(o) + 3.

Success appends the newly generated reversed mask before o. Failure clears all three owned stacks, and the bound explicitly charges the whole existing accumulator. From the singleton start with both work stacks empty, the bound is 3L+5, including the real pending-slot creation.

### Hand accounting

For an internal token, one transition consumes an input bit, increases the remaining pending count by one, and increases the mask length by one. The induction budget is exactly preserved: 1+3(L-1)+(q+2)+(length(o)+1)+3 = 3L+(q+1)+length(o)+3. A leaf consumes its token and both complete unary frames while removing one slot. Reading a unary field of encoded length a+1 costs a+1 transitions and pushes exactly that many false marks. A missing all-true field of length a, with q pending slots and accumulator o, costs at most 2a+q+length(o)+2 including mask/pending cleanup. These inequalities cover both missing-field positions and every malformed word.

The mask after the two fields is false^(b+1) ++ false^(a+1) ++ true :: o, exactly the reverse of the leaf's true :: false^(a+b+2) prefix followed by o. This arithmetic identity is explicit in the proposed source.

## 4. Actual caller integration and paid reversal

`PolytomyTreeMaskCaller.lean` embeds the actual instruction code through the pinned proof-side Embedding.stmt/runs API. Three distinct caller ports hold source, pending slots and the reverse mask. All other stacks and the whole caller frame are preserved; the private scratch head is reset. The generic frame must be instantiated with a finite type when packaging a complete finite machine.

`PolytomyForwardTreeMask.lean` allocates a fourth distinct output port and composes the logger with the existing actual reversing-transfer routine. This is a physical traversal, not a freely assumed List.reverse operation. Since mask length is at most L, its length+1 transfer cost gives the full forward-mask bound

    4L + 6.

Success returns the exact original unread suffix and the exact forward-order legal-node mask. Pending and reverse scratch are empty. Failure leaves all four owned ports empty and reports failure. All outside caller data and frame survive. Entry and intermediate stores are explicitly typed, so register-role rotation is a proved same-store equality, not silent copying or erasure.

## 5. Connection to the original full obligation

The current mask and prefix primitives provide an exact route to every real subtree interval of arbitrary supplied target/certificate trees. The next physical layer must replay a preserved original word at a mask-selected index, read the original cell fields, and scan the selected subtree's legal-node mask. It must then implement the original finite-range checks, target guard, leaf uniqueness and exact cell-set equality, every fixed-tree clade, distinct-type score and budget comparison. None of those remaining nested comparisons is inferred merely from a pure list definition.

The independent checker may not request an MSSC source or minimizing order; its fixed blocks need not be constructor combs, and block tags need not equal enclosing list indices. These restrictions are unchanged. The existing original pair splitter and saturated target/budget adapter remain prior components, not newly solved claims.

The separately preserved constructor machine term remains unelaborated. The full actual-D_lambda complexity endpoint still needs the complete independent verifier machine, compatible encoded-source hardness, transitive compatibility/axiom closure and authorized kernel checking. General-DAG and original biological/stochastic identification scopes remain open. No earlier coordinating review is extended to this packet.

## 6. Source inspection and verification status

Read-only inspection of Lean v4.33.1 verified List.flatMap_cons in Init/Data/List/Basic.lean and List.replicate_one, List.replicate_succ', List.reverse_replicate and List.replicate_append_replicate in Init/Data/List/Lemmas.lean. In particular, no guessed replicate_add name is used. The pinned mathlib transition-composition order and existing proof-side embedding/reversal interfaces are retained.

Lexical delimiter/placeholder checks are only textual screens, not Lean parsing, elaboration, code generation, a transitive axiom audit or theorem verification. No compiler, research runtime, test or CI was invoked.
