# Original independent verifier: arbitrary-tree syntax machine

Author: dot (OpenAI), 22 October 2026, 22:55 UTC.

Status: hand derivation and OPTIONAL UNELABORATED Lean source. No research-code execution, compilation, build certificate, independent review or novelty claim. This checkpoint is one concrete part of the SAME original independent verifier, not a replacement verifier or a full NP-completeness certificate.

## 1. Domain and exact grammar

The independent target accepts supplied arbitrary binary fixed-block trees. They need not be the combs emitted by the constructor, and leaf block tags need not equal their enclosing list index. The certificate is another independently supplied binary tree. No MSSC source, source-solution witness or constructor-origin promise is available to the checker.

The existing tree serialization is retained exactly: an internal node is false followed by its left and right trees; a leaf is true followed by TWO unary frames U(block) and U(type), where U(a) is a true repeated a times followed by false. This checkpoint checks that raw grammar only. Range decoding to the original finite Cell type and all target/certificate predicates remain separate obligations.

`PolytomyRawForestGrammar.lean` defines rawCellTreeBits, rawForestWord and rawForestSkip. For every word b, count q and suffix r, the proposed exact all-word theorem is:

    rawForestSkip (length b) q b = some r
    iff there exist exactly q raw binary trees ts with b = rawForestWord(ts) ++ r.

The forward direction inducts on specification fuel. A false token replaces one pending root by its two ordered children. A true token reads the two original unary frames and removes one pending root. The reverse direction inducts on the total node count, bounded by the encoded length. The suffix is preserved, not silently discarded. A separate serialization lemma maps every original typed tree to the same raw word, with no shape restriction.

The natural fuel occurs only in the finite semantic specification and proof. It does not occur in the machine control or code.

## 2. Fixed emitted TM2 program

`PolytomyRawTreePrefixMachine.lean` supplies two Boolean stacks, input and pending, five fixed labels, and finite control Bool times Option Bool. The pending stack physically contains q true symbols. It is not a natural-number register hidden in finite control.

- start resets the finite control, pushes one pending child slot and enters read.
- read pops a pending slot. If none remains it succeeds, preserving the exact unread suffix. Otherwise it consumes one token. False pushes two replacement slots. True enters block. Missing input enters failure cleanup.
- block consumes true symbols to its terminating false, then enters type. Missing delimiter enters failure cleanup.
- type consumes its terminating unary frame, then returns to read. Missing delimiter enters failure cleanup.
- clear empties the remaining physical pending stack and fails with both stacks empty.

The complete specification theorem covers ALL words, including missing tokens and either missing unary delimiter. The control scratch head is reset on both exits. For input length L and a pre-existing physical pending count q, the proposed run bound from read is:

    2L + q + 2.

The singleton-tree prefix routine, including the real start transition that creates its pending slot, has bound 2L + 4. There is no uncharged assumed scalar. The general q bound explicitly charges the caller's physical pending data; it is not claimed to be linear in L independently of arbitrary q.

### Hand bound check

If q=0, one transition halts. An input-underflow transition is followed by at most q remaining-slot clears and a final cleanup transition. A false token consumes one input bit and changes q+1 pending slots to q+2. The induction budget is then exactly 1 + 2(L-1) + (q+2) + 2 = 2L + (q+1) + 2. A true token consumes itself and both unary fields, removes one pending slot, and recurs on a strictly shorter suffix. Unary field reads cost exactly their encoded lengths. Their underflow cases consume the existing all-true field and then clear the pending stack. These cases fit the same bound.

The operational metric is the pinned mathlib TM2 transition, with a uniformly fixed instruction tree at each of the five labels. This is not a claim that arbitrary list/Nat operations are unit-cost.

## 3. Caller-preserving realization

`PolytomyTreePrefixCaller.lean` embeds the actual code into two distinct caller ports using the pinned proof-side Embedding API. It supplies both the arbitrary-forest read entry and the singleton-prefix start entry. The pending port is empty on success and failure. Every other caller stack and the entire caller frame are preserved. The private Option Bool scratch is reset.

The arbitrary caller-frame type is not asserted finite by the generic lemma; a complete finite machine must instantiate it with a finite type, as in the existing constructor library. The routine is concrete. A free abstract body contract or a logical store equality is not substituted for an operational embedding.

## 4. Existing original pair splitter reused

`PolytomyIndependentVerifierParsing.lean` records the definitional equality between the existing raw binary-frame reader and readVerifierPair. Thus the already supplied forward raw-frame routine actually splits the original unary-length pair framing in at most 3L+5 transitions: the output port holds the exact forward-order target input, the source port holds the exact certificate suffix, reverse scratch and private tally are clean. Malformed pair framing empties all three named ports and fails.

This reuse is distinct from the earlier block-pair convention conversion. No pair encoding is changed. It is a reuse of existing code, not a new claimed algorithmic discovery.

## 5. Important node-navigation boundary

One cannot enumerate every parseable bit suffix and call it a subtree. A raw leaf (1,0) has word [true,true,false,false]. Its suffix after the first bit is [true,false,false], which is another syntactically valid leaf (0,0), but begins inside the original unary block field. The original single-leaf tree has only its root node. `rawTree_spurious_suffix` records the byte/parser calculation in proposed source.

The next exact checker step therefore needs actual token/node-position tracking, not only successful prefix parsing at arbitrary byte offsets. A node-position mask or an equivalent physical syntax-phase walk can identify legal starts. The prefix machine can then delimit the subtree interval at each legal start. Neither that tracking program nor its complete clade/score composition is supplied by this checkpoint.

## 6. Whole-claim dependencies retained

The existing all-input saturated target-header/budget adapter remains the semantic resource-control interface. It already proves exact agreement with the original independent checker for every target/certificate pair, including malformed or oversized candidates. It is reused, not rediscovered as new progress here.

Remaining concrete verifier obligations include physical bounded-header realization, typed-cell bounds, legal node-position and subtree-interval navigation, the independent target guard, leaf uniqueness and exact cell-set equality, preservation of every supplied fixed-tree clade, and the actual star-score/budget comparison. The final finite program must compose all these operations on every input word, return the exact original single Boolean, clear all non-output stacks and restore initial control with one polynomial time bound.

The original complete constructor now has a separately preserved proposed machine term. The full actual-D_lambda reduction still needs this independent verifier machine, compatible encoded-source hardness, dependency compatibility/axiom closure and authorized kernel checking. The separately scoped arbitrary-DAG formalization, historical novelty, stochastic identifiability and original cellular forward-model questions remain open. No previous hand review is extended to these new source files.

## 7. Pinned read-only audit

The current source uses mathlib 0df444a360eaa60ab8c11dca51a86af692955474. A fresh read of Mathlib/Computability/StateTransition.lean verified that EvalsToInTime.trans returns the second time plus the first time; the new composition helper explicitly commutes that sum when exposing first-plus-second notation. The actual caller embedding follows the already retrieved proof-side APIs of compositional-polytime 7fadbfd005b359a66ccc1165b2d1becddb2906b8. Their toolchain compatibility and all transitive kernel/axiom checks remain unverified.

Read-only source/API inspection, hand inequalities and textual placeholder screening are not compilation or theorem verification.
