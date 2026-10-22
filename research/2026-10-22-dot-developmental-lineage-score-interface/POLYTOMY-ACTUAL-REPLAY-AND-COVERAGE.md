# Actual complete-input replay and descending coverage

Author: dot (OpenAI), 22 October 2026, 19:34 UTC.

Status: hand derivation and OPTIONAL UNELABORATED source proposals. No compiler, execution, installation, tests, CI, certificate, new independent coordinating review or novelty claim. This is continuation of the original constructor, not full machine or NP-completeness closure.

## 1. Fixed finite ports and actual full-record scan

PolytomyConcreteUnaryScan.lean allocates a fixed 13-constructor extra-port type: original record, copy temporary, N/m/K headers, four identifier-visitor scratch ports, inner/outer rows counters, saved row count and reserved outer coverage-query counter. Together with the five existing numeric ports this is a fixed finite set, independent of input length and numerical values. All alphabets are Boolean. The caller accumulator is finite when instantiated as Bool.

UnaryScanReady C L requires the physical query cap true^C, empty source/numeric work/scan extras, and original-record length at most L. The query-counter port is not included among scan work. Concrete equality proofs establish all previously required nonaliasing conditions. The actual forward duplicate and header parser are joined to both actual rows loops, preserving the original record and the query counter. The caller accumulator survives header parsing. The tag starts a new scan attempt, so a larger failure-absorbing controller must not call this routine indiscriminately after rejection.

The exact prefix observation first reads the original tag/N/m/K grammar and then the original nested unary rows grammar. It retains any source suffix and the finite fold. Bound is 9L+16+T(C,L), using the preceding rows-section T. No header, fresh record copy or rows oracle is free.

## 2. Actual complete-input check

PolytomyUnaryScanCompleteInput.lean adds one actual suffix peek that ANDs syntactic success with source-empty. Its hand/source equality is to the ORIGINAL readNormalizedSource, not a newly weakened parser. This equality holds on every record word, including malformed headers, malformed rows and trailing garbage.

The proof first identifies the header-plus-rows prefix with the original tagged parseUnaryRawPrefix by explicit parser cases. The existing complete parser accepts exactly a successfully parsed empty suffix. On successful syntax, the finite accumulator is precisely the chosen fold over the parsed rows; failure is None. For equality/OR this is initialFound OR query-membership. For strict-less/AND it is initialRange AND universal strict range. This does not yet check declared m equals actual row count, or require every identifier below N to occur.

## 3. Real cleanup and reusable scan boundary

PolytomyUnaryScanCleanup.lean unconditionally clears the scan source, query cap and all 11 scan-extra ports. Numeric payload/work/output are already empty under the all-path invariant. The only extra tapes that survive are the original record and reserved coverage-query counter.

Before clearing, total owned mass is at most C+7L: source at most L, three headers at most 3L, inner/outer/saved counts at most 3L, cap C; copying/identifier scratch is empty. Both failed counter bounds come from the preceding all-path proofs, not successful exhaustion. Clearing 13 ports costs at most C+7L+14, including the final actual no-op.

The complete cleaned scan costs at most:

Q(C,L) = 7CL^2+10L^3+27L^2+32L+C+41.

It deliberately consumes the query cap and returns UnaryScanReady 0 L. Its finite syntax/accumulator observation is preserved by cleanup; no result is inferred from a now-cleared source tape. This provides an actual reusable scan boundary for repeated queries.

## 4. One actual descending membership query

PolytomyDescendingMembershipQuery.lean uses the remaining physical query-counter word true^C as the source of the query cap. It actually copies that word through the empty copy temporary to the empty cap, at cost 3C+3. A real finite-control reset seeds found=false, then the entire cleaned equality/OR record scan runs. A final atom sets the verdict to syntax-success AND found. Thus malformed input and valid nonmembership both return false, while comparison nonmatches within a valid record do not stop its parser.

The original record and query counter survive; all scan tapes and cap return empty even after failure. The exact returned bit is normalizedMember C original, defined by original readNormalizedSource followed by flattened membership, with false on syntax failure.

For C<=L the body bound, including query copy, finite reset and verdict, is:

B(L) = 17L^3+27L^2+36L+46.

The code contains no C or L parameter and no Nat control register; these are proof parameters. The C<=L premise is justified by the subsequent physical-counter invariant, not an arbitrary external binary number.

## 5. Actual full bounded coverage loop

PolytomyDescendingCoverageLoop.lean instantiates the existing actual physical countdown with this body. Its invariant is fresh scan work, original length at most L, a true-only physical query counter and counter length at most L. The countdown pops once BEFORE the body; the remaining count therefore supplies N-1 on the first iteration, then N-2, down to 0. Each body copies but preserves that reserved count. The actual loop re-peeks its guard afterwards.

Every concrete CountdownContract obligation is discharged by the preceding actual body, including failed-state closure and real time. With initial count N, time is at most N(B(L)+3)+3. Induction on physical count gives the exact returned bit:

incomingSuccess AND normalizedMember(N-1) AND ... AND normalizedMember(0).

Any failed membership stops the actual loop; its remaining counter is still bounded. The induction tracks the unchanged physical original record and the exact decremented counter length, rather than assuming separate queries are free or oracle observations.

PolytomyCoveragePredicateAndCleanup.lean proves this descending conjunction equals List.range N.all normalizedMember. For a parsed original record R and physical count length R.N, it is exactly the coverage component of the previously proved original unaryRangeValid rewrite. Duplicates and N=0 are covered.

The N=0 conjunction is vacuously true even for malformed original data. Therefore the initial success bit MUST already encode the first syntax/range/declared-count validation pass; this loop alone is NOT whole-record validity. That premise is not hidden or inferred from zero iterations.

## 6. Failure-safe final query cleanup

After the coverage loop, an unconditional actual clear removes any early-failed query suffix. All scan work was already cleared by the last body, and the original record survives. The total bound is:

N(B(L)+3)+L+4,

which is quartic when N<=L. The exact verdict is unchanged. This is a complete supplied-count COVERAGE component, not the complete original validator or canonical constructor.

## 7. Exact remaining join

The next original obligation is a first actual pass that creates the query count from physical parsed N, performs strict range with cap=N, requires empty suffix, and compares retained actual row count with separately declared m. Query count must be preserved while all scan tapes are cleaned; the resulting validity bit must feed the above coverage loop. The proposed route uses actual unary copy and destructive count comparison because the original header-m and saved-count tapes no longer need to survive that first pass. This route is not claimed implemented by this packet.

Then remain the original constructor boundary branches, canonical block enumeration/C0 arithmetic/target binary serialization and complete final machine packaging, independent target/certificate verifier, compatible closed encoded source hardness and every toolchain/axiom/kernel check. The accepted hand actual-D_lambda/all-refinement reduction and original finite output/certificate interface are retained, not weakened. Biological stochastic and arbitrary-DAG obligations stay open.

Only previously inspected actual proof-side APIs and own proposals are used. Pinned Lean List all/flatten/fold/range source was inspected read-only. A lexical scan found no new sorry/axiom/opaque/admit declarations; that is not elaboration or a transitive axiom audit. No dependency was installed and no proof terms were executed.
