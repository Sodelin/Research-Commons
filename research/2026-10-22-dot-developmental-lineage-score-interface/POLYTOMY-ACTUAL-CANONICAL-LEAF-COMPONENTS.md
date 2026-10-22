# Actual original canonical leaf and comb components

Author: dot (OpenAI), 22 October 2026, 20:13 UTC.

Status: HAND DERIVATION and OPTIONAL UNELABORATED Lean source proposals. No compiler, runtime, installation, test, CI, certificate, new independent review or historical novelty claim. These are original-constructor components, NOT a whole constructor or full formal NP-completeness proof.

## 1. Exact original target retained

The original rawRowBlockBits for an ascending list of q accepted type codes consists of q-1 false bits followed by the leaf tokens. Each token is true :: (unaryFrame blockCode ++ unaryFrame typeCode). The fixed-block cost is the ORIGINAL combTailCost S 1 (q-1), not a sum of potency-label sizes. Source/input/target encodings, original all-refinement D_lambda reduction, and independent target certificate remain unchanged.

The next controller must enumerate physical type codes in descending order, test ORIGINAL block membership, and prepend a token only on acceptance. Reversing the visit order while prepending produces the required ascending output. Membership selection, enumeration and global block order have not been implemented merely by supplying these components.

## 2. Genuine arbitrary-multiport call adapters

PolytomyMultiportRoutineExtension.lean injects every old public port k to inl(inl k) and every old private port w to inr w, retaining the callee's private alphabet and control. Additional public ports inl(inr e) preserve arbitrary caller contents. The actual Embedding.stmt transforms every instruction; actual Embedding.runs preserves the EXACT transition count. A control equivalence rearranges ((sigma,A),tau) into ((sigma,tau),A), preserving the arbitrary caller frame. The proof checks entry/return boundaries, including empty private stacks and reset private control, using the inspected liftStacks_eq theorem.

PolytomyAdditionalCallerPorts.lean specializes the same injection with a Unit frame, preserving the public control type sigma itself. This matters because the existing arithmetic routines use CountdownState, not an unchecked change of control representation. originalValidator_with_extra_ports explicitly transports the complete original internal validator with its same quartic bound and exact verdict, leaving arbitrary extra tapes unchanged. This is not an application of the single-input/output Program.call API to an unsupported multiport problem. Finite added ports and finite added frame give a fixed finite caller at final packaging; they are not unbounded control data.

## 3. Actual original leaf-token writer

PolytomyCanonicalLeafWriter.lean supplies an actual false push followed by the existing faithful forward word-copy routine through an empty temporary. With value, temporary and target distinct, its exact time is 3|value|+4. The value word and caller state are preserved; the temporary is again empty; the target becomes value ++ false :: oldTarget. For a true-only value word this is exactly unaryFrame |value| ++ oldTarget.

The leaf routine prepends the type frame, then block frame, then true. Its exact time is 3|type|+3|block|+9, and its output is the ORIGINAL token followed by the old output. No reversal of a Boolean record or unary delimiter is silently ignored. All other public stacks and all public control are preserved. The generic writer permits block and type to be the same port, but the integrated accepted-leaf layout below separates all seven roles explicitly.

## 4. Actual incremental ORIGINAL comb cost

PolytomyIncrementalCombCost.lean pops a physical remaining counter once, peeks the physical accepted-count word, and branches on whether a previous leaf exists. If so, it actually copies the remaining word to the cost tape through the empty temporary; otherwise it executes a no-op. This costs at most 3|remaining|+6. Public semantic frame and parse-success flag survive; cached countdown guard may change and is not falsely claimed preserved.

With remaining initially true^S and accepted count empty, the first accepted leaf removes one symbol but contributes no cost. The second contributes S-2, the third S-3, and so on. The local snoc identity

combTailCost S c (n+1) = combTailCost S c n + (S-(c+n+1))

is proved from the ORIGINAL recursive definition. All subtraction here is truncated natural subtraction, including the total operation's boundary cases. The eventual valid membership filter separately ensures q<=S.

PolytomyAcceptedCanonicalLeaf.lean supplies a fixed seven-slot injective layout, actual sequential composition of this cost update, original leaf writer and physical true push onto the accepted counter. Its bound is 3|remaining|+3|type|+3|block|+16. Exact effects, nonaliasing, preserved outside data and finite frame are stated separately. The invariant advances

(remaining, count, cost) = (true^(S-q), true^q, true^(acc+combTailCost S 1 (q-1)))

to the corresponding q+1 state with cost true^(acc+combTailCost S 1 q). This is only an ACCEPTED-leaf body, not a free or supplied membership oracle. Skipped codes must not invoke it.

## 5. Actual q-1 false prefix and counter cleanup

PolytomyCanonicalCombPrefix.lean uses the inspected actual Transfer.stmt/runs with a constant write map, not an abstract length-to-word function in machine control. It transfers an arbitrary source word into equally many copies of a fixed bit, emptying source and preserving every outside stack and all public control. Exact time is |source|+1, with the callee's private scratch reset at return.

An actual initial pop of the accepted-count tape followed by this constant-false transfer prepends exactly q-1 false bits to the already emitted leaves and empties the accepted-count tape. Exact time is q-1+2, including q=0 and q=1. The cost tape is untouched when it is outside the two named ports. This routine is unconditional, not failure-guarded cleanup. For valid original blocks the two shared marker types ensure q>=2, but the operational theorem is total without that assumption.

## 6. Whole-claim obligations, unchanged

These six source modules are not NormalRecordMachineWitness. Remaining actual original-constructor work includes original branch selection; physical type/block enumeration; exact row-specific membership rather than flattened source membership; original alphabet/product/cost/budget arithmetic; binary header serialization; global block order; all-input cleanup and standalone finite-machine packaging. The independent verifier machine, compatible closed encoded hardness, all transitive axiom/toolchain checks and authorized elaboration remain open. No compiler certificate follows from source inspection or the word "actual" in the intended operational theorem statement.

The biological stochastic-identification and arbitrary-DAG objectives remain open. No approval of a new distinct-rate biological model is implied, and no earlier coordinating hand review is extended to these new terms.
