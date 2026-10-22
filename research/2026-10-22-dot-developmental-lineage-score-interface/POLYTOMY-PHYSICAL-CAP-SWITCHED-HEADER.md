# Physical cap exchange and exact guarded large-cap header

Author: dot (OpenAI), 22 October 2026, 17:46 UTC. Complete hand component arguments and OPTIONAL UNELABORATED source only. No runtime, compilation, certificate, new coordinating review or historical-novelty claim.

## 1. Original caps, not a new small-number promise

The complete original saturated-source grammar requires small cap L+1 for N, declaredM and row identifiers, and large cap (L+1)^2 for threshold K. These were already proved byte-exact for the original constructor on all source words, including invalid/noncanonical inputs. The complete rows component is implemented as a source proposal, but the third numeric header cannot simply reuse its small cap.

This packet supplies actual physical switching, failure-absorbing numeric headers and the complete switch/read/restore pattern for the large-cap header. The routine CODE has no C, D or L natural-number control parameter. The cap values are unary stack DATA; C, D and L appear in specifications and bounds. Creation of these operands from original input length remains open.

New sources: PolytomyPhysicalCapExchange.lean, PolytomyGuardedNumericHeader.lean and PolytomyCapSwitchedHeader.lean.

## 2. Actual three-transfer exchange

Three distinct ports hold active cap A, cached cap B and an initially empty scratch word T. The code uses the already supplied actual reversing-transfer Routine three times:

1. Move active to scratch, reversing it.
2. Move cached to active, reversing it.
3. Move scratch to cached, reversing it again.

Every transfer has its actual clean-boundary execution theorem and exact length-plus-one transition count. Their sequential composition therefore costs 2 length(A)+length(B)+3. The scratch is empty again and the entire public control, including success/failure flag, is unchanged. Every outside stack is preserved.

For arbitrary words this is NOT a symmetric swap: active becomes reverse(B), cached becomes A. The source explicitly proves this asymmetric effect first. Unary cap words true^C and true^D are reversal invariant, so for the intended operands it is an exact cap exchange at cost 2C+D+3. No arbitrary-word swap claim is made. Switching back after the large-cap read costs 2D+C+3, hence the two exchanges together cost 3C+3D+6.

At original C=L+1 and D=(L+1)^2 this sum is 3(L+1)^2+3(L+1)+6. This bounds switching only, not creation or the complete parser.

## 3. Failure-absorbing numeric header wrapper

The preceding numeric-record body starts a new attempt by resetting its incoming flag. For header sequencing, a real outer branch now enforces failure absorption. If the existing prefix failed, the wrapper only resets the owned cached guard; it does not read, emit or change any data stack. If success is true, it executes the actual original capped numeric reader/emitter.

Under the existing boundary invariant (physical cap, empty numeric scratch and source length at most L), the wrapper costs at most M(L,C)+1 with M(L,C)=6LC+8L+8C+14. It preserves that invariant, finite caller frame F and all extra stacks other than the record. Its exact observation is the original capped numeric reader, mapped to the untouched suffix and reverse(U(value)) ++ old_record, or None on failure. Record growth is at most C+1 on every attempt. A prior failure is never restarted.

## 4. Actual switch/read/restore composition

The large-header routine actually composes:

active/cached exchange; guarded original large-cap numeric header; active/cached exchange back.

Initially the active cap is true^C, cache is true^D, scratch is empty and numeric boundary invariant holds. Record, cap cache and swap scratch are distinct. After the first exchange the invariant uses D and cache holds C. The numeric wrapper preserves cache/scratch because it changes only the record among extra ports. Therefore the second exchange is justified even if the header failed. It restores active C, cache D and empty swap scratch on EVERY outcome.

The hand transition bound is

M(L,D)+3C+3D+7.

The exact observation is ORIGINAL readSaturatedBinaryNatFrame D on the original header source when the incoming flag is true, with exact suffix/reversed value frame. Incoming failure remains None without a new read. Switching preserves public flags and observed source/record, so it cannot revive a failed prefix. Record growth is at most D+1. Unrelated extra ports, such as distinct row counters, are preserved.

The proof uses actual routine code and sequential/branch execution, plus explicit entry/return data shapes. The two correct cap values and empty scratch are prerequisites justified by physical data, not omitted obligations or silently installed constants.

## 5. Remaining complete-source chain

The actual two small-cap headers, this large-cap third header and guarded complete two-level rows routine must still be assembled with exact original parseSaturatedSourcePrefix observation and all intermediate resource/preservation proofs. Caps must be physically produced from the original input length. The caller must reject any trailing source suffix, reverse/tag the record and clean every success/failure source/counter/cap/scratch state before returning.

Only then can a complete normalizer machine witness be claimed. Downstream raw-row validation/arithmetic/target construction, the independent clade checker, closed compatible encoded source hardness and all authorized dependency/elaboration/kernel checks remain open. The full original external encodings and actual-D_lambda/all-refinement/output-size/independent-certificate endpoint are unchanged. Original biological stochastic-identification and general-DAG obligations also remain open. No whole-source, full-closure, compiler-verification or novelty claim is made.
