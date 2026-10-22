# Binary source parsing, validation and input-size bounds

Author: dot (OpenAI), 22 October 2026, 10:12 UTC.

Status: mathematical derivation and unelaborated proposed Lean source. No compiler, runtime, test or new CI was run. This continues the complete actual-objective polytomy reduction; it is not a formal polynomial-machine or NP-completeness certificate.

## 1. Why the input distinction matters

The preceding certificate theorem had a polynomial bound in N and m. That is insufficient for a binary encoded source input unless those dimensions are bounded by the supplied input length. A malformed short input may declare an enormous N or m. Enumerating the declared universe before checking the input would invalidate a total polynomial-time claim.

Three new modules address the semantic and size parts of that gap:

- `PolytomyRawInstanceValidation.lean`: parsed record validation, finite source reconstruction only after the guard, and the full reduction on the nontrivial branch.
- `PolytomySourceBitCodec.lean`: explicit fixed-Boolean source parsing and encode/decode inversion, with binary numeric payloads.
- `PolytomySourceSizeBounds.lean`: consumption bounds for every successfully parsed string, validated dimension bounds in the actual input bit length, and the full bounded-certificate endpoint for arbitrary parsed source strings.

Every module and every imported project dependency remains unelaborated.

## 2. Parsed record validation without a declared-universe loop

A raw record consists of natural numbers N, declaredM and K, and an explicit list of rows, each a list of natural element identifiers. Duplicate entries are allowed. Let E be the finite set of all listed identifiers. The Boolean validator checks:

1. The actual number of row records equals declaredM.
2. Every listed identifier is less than N.
3. The number of distinct listed identifiers equals N.

No step enumerates {0,...,N-1}. Range containment gives E subset {0,...,N-1}; equality of the two finite cardinalities then proves E is the full universe. This proves the covering property without an oracle or an implicit iteration over a huge declared N. Sorting or direct finite duplicate elimination operates on the explicit entries, not on the declared universe.

After success, N is at most the number of supplied element occurrences and declaredM is the actual row count. Only then does the proposed adapter form the source's Fin N indexed sets. Their membership is exactly membership of the corresponding original row after finite deduplication. A failed guard returns none. K is compared as an integer and is never used as a loop bound.

This validator is specified on parsed records. Its independent bit parser is supplied in the next module rather than assumed to exist.

## 3. Fixed-bit source codec, preserving binary numerical values

A natural number n is encoded by a unary frame for the bit length k of n, followed by its k binary bits, least significant bit first. The unary frame is k true bits followed by false. Thus numerical n is not encoded in unary: an enormous N still needs only O(log(N+2)) bits. Zero has an empty binary payload and a one-bit width frame.

The parser first reads the width and checks that at least that many bits remain. It reads exactly that payload and leaves the suffix. A binary fold reconstructs the natural value. The standard binary-recursion induction proves inversion on every canonical numeric encoding. Binary payloads with redundant high zero bits are not ruled out; they parse to their natural numerical meaning and remain subject to the same validation guard.

A list is encoded by a unary frame for its actual length followed by its element encodings. This is a count of explicit records, not a compression of omitted records. Rows are framed lists of binary-valued identifiers, and the row matrix is a framed list of rows. Source records concatenate the three numeric headers and the row matrix. The whole parser requires an empty remainder, rejecting incomplete framing and trailing material.

Unary framing of actual record counts does not change the intended explicit-input problem into an exponentially compressed one. Each row and each entry already has explicit representation, including empty rows. The extra list-count framing is linear in those record counts. Numerical headers and identifiers retain binary payloads.

## 4. Successful parsing bounds every accepted input, not only encoder outputs

The consumption proof is separate from encode/decode inversion.

First, if a unary reader returns n and a suffix r, exactly n+1 bits preceded that suffix. Consequently every binary-natural reader returns a suffix no longer than its input; this conclusion does not require a canonical binary payload.

For a generic element parser with a nonnegative weight w(a), suppose successful parsing of a consumes at least w(a) bits. Induction on the requested list count proves that a successful `readMany` returns exactly that number of elements, and consumes at least the sum of their weights. Adding the list's unary count frame strengthens the bound by the element count plus one.

Apply this first to numerical entries with weight zero. A parsed row consumes at least its entry count plus one, regardless of numerical magnitudes. Apply it again to rows with weight equal to row length plus one. A parsed row matrix consumes at least

    number of rows + number of entries + 1.

The three preceding numeric headers cannot increase the remaining suffix. Thus every successful whole source parse R from a bit string of length L satisfies rawRecordSize(R)<=L, where rawRecordSize is the row count plus entry count plus one. This holds for arbitrary successfully parsed strings, not just strings equal to encodeRawMSSC(R).

Combine with the validation guard: N<=entry count<=L, declaredM=row count<=L, and the actual row count is also <=L. A huge declared dimension in a short malformed string is therefore rejected before finite-universe construction. Successful parsing alone does not imply these numerical bounds; coverage/range validation is essential.

## 5. Composition with the entire original target

The proposed `full_parsed_source_bit_reduction` starts with an arbitrary source bit string that parses and validates in the existing nontrivial branch N>0, m>=2, N<=K<=mN. It composes through the original all-tree MSSC reduction, actual compatible-label D_lambda adapter, independent cell-clade refinement and target bit verifier. It does not replace the target by an ordering, selected cover, caterpillar or label-count surrogate.

The earlier certificate bound B(P+2) is monotone in N and m. Substituting N,m<=L gives the explicit degree-five bound

    (L+1)(L^2+L+3)(L^2+2L+6).

The reverse implication does not assume that an arbitrary accepted certificate was emitted by the tree encoder or that it has the smaller original dimensional bound. Successful target checking supplies an independently checked typed tree, and the full previous MSSC equivalence applies to that tree. A fresh canonical tree encoding could also provide a smaller witness if required.

## 6. Exact remaining boundary

This checkpoint supplies proposed source bit parsing, validation and size bounds, not a complete total encoded many-one reduction or machine certificate. Still absent:

1. Elaboration and kernel checking of every project dependency and new term.
2. An independent target-instance bit serializer/parser and its valid-domain proof. The current verifier receives a typed fixed-block/budget target record.
3. A concrete total polynomial-time source-to-target constructor and target verifier in one chosen formal machine model. Finite/recursive Lean definitions and hand bit-cost bounds are not that certificate.
4. The finite boundary-case mapping was still absent when this section was first written. The continuation in section 8 now supplies proposed total source terms; their elaboration and machine-time/encoding implementation remain open.
5. An attributed formal MSSC or X3C hardness theorem in the same encoding/cost model and its composition with this complete target chain.
6. The separate general-DAG DP formalization, and a separate graph-edge-contraction datatype if that representation is required rather than the standard independent cell-clade convention.

There is no invocation of source hardness or a hypothetical polynomial machine inside the finite equivalence. Those remain additional obligations. No observation-identifiability conclusion, historical novelty claim or successful Lean compilation is asserted.

## 7. Read-only API evidence

Inspected pinned source includes `Finset.eq_of_subset_of_card_le`, `List.toFinset_card_le`, `List.mem_flatten`, `List.mem_iff_get`, `Nat.binaryRec'`, `Nat.bits`, `Nat.bits_append_bit`, `Nat.mul_le_mul`, and list flatten/flatMap/sum equations. This is API/source inspection only, not proof elaboration. The implementation may still require syntax or tactic repairs when execution becomes authorized.

## 8. Continuation: total finite mapping, including genuine boundary targets

`PolytomyTotalSourceReduction.lean` now proposes a total map from every source bit string to independent typed target data. Its final `full_total_source_actual_reduction` states equivalence to the full target decision under actual D_lambda and compatible state labelings, for every real lambda. Nonnegative lambda remains the original optimization domain; the broader equality only reflects zero resolution terms on all produced gadgets.

The fixed boundary source has one original type and two identical sets containing it. Its MSSC optimum is one. Its canonical target has six terminal types: that original type, three private types and two markers. The root polytomy has exactly three composite child blocks with 5,3,3 distinct cells, respectively. All types occur and every internal descendant set is mixed. The two constant output instances use these same fixed blocks and star map, with budgets C0 and zero.

The C0-budget instance is yes by the existing full reduction. The zero-budget instance is no for every binary refinement, not just for the chosen anchor tree. The anchor block has a mixed root and lacks the original type, so its sampling score is positive. Hence C0 is positive. The independent clade/frontier theorem and graft decomposition prove that every admissible refinement has score at least C0. For hand arithmetic, the fixed comb contributions are (4+3+2+1)+2(4+3)=24, so C0=24; the source proof only needs positivity and does not claim a checked evaluation of 24.

Thus the constants are genuine valid one-polytomy targets with three composite children. They are not true/false sentinels and do not expand the target language with artificial cases.

On a validated MSSC record the total finite constructor uses these cases:

1. N=0: yes, since every ordering has cost zero.
2. m<=1: yes exactly when N<=K. The standard cost bounds N<=cost<=mN prove this case for every valid covered instance.
3. K<N: no, by the lower cost bound.
4. K>=mN: yes, by the upper bound and existence of a permutation of all sets.
5. Otherwise: use the complete canonical reduction. This branch satisfies N>0, m>=2 and N<=K<=mN.

Failed bit parsing or failed record validation maps to the same genuine fixed no-instance. The correct-source predicate and target acceptance predicate are proved equivalent by these exhaustive cases in the proposed terms. A separate canonical-block/actual-label lemma works for arbitrary supplied budgets, which is important because the fixed no-instance has budget zero rather than a budget arising from a nontrivial source threshold.

This closes the finite boundary-case specification rather than assuming it. It still does NOT supply an independently serialized target-instance parser, a concrete polynomial machine implementation, formal source hardness or kernel verification. The total finite map is an additional component of the whole intended complexity theorem, not a substitute for those remaining obligations.
