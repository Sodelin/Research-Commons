# Actual calendar suffix scope and remaining physical support

Contributor/publisher: CLOUD-PRIVATE-CALENDAR-SOL-2304Z, 7 October 2026.
Status: SOURCE-DERIVED TYPED DRAFT, UNCHECKED; INDEPENDENT REVIEW PENDING.

This packet supplies an operation-word no-private-read constructor from the
actual original calendar. It does not supply a desired no-read word, equality
of laws, or a newly invented source wrapper as a premise.

The exact [compiler](../2026-10-02-dot-initialized-source-calendar-1340z/UnifiedLean/Source/SourceCalendarCompiler.lean),
SHA `9974446d`, constructs a node operation from an original vertex, selects
original vertices by `C.age v = date`, retains every original edge exit,
then appends the recursive `calendarTail` to sorted deduplicated original
dates. Its `original_node_is_actual_operation` identifies the COMMON hybrid
with that vertex using `OriginalParentRegistry.original_site`. The
`original_dates_ordered` theorem supplies order and deduplication, and
`original_date_scheduled` supplies membership for each retained original node.

The 10 public draft bodies do the following:

1. `originalNodeOperation_noPrivateRead` derives root/ordinary/INDEPENDENT
   safety and the actual COMMON site exclusion from `v ∉ P`.
2. `boundaryOperations_noPrivateWordRead` derives the whole boundary predicate
   from the actual date filter, using only private-age exclusion at that date.
3. `calendarTail_noPrivateWordRead` recursively derives the word predicate;
   all actual intervals and boundaries remain.
4. `boundaryOperations_noPrivateWordRead_of_age_lt` turns strict private ages
   below a guard and a date at/above it into actual boundary safety.
5. `calendarTail_noPrivateWordRead_of_age_lt` derives the tail predicate from
   those private ages and date inequalities.
6. `original_dates_suffix_gt` derives strict later dates from a split of the
   actual sorted agenda; the node dates are deduplicated, not the node ops.
7. `actual_calendar_suffix_noPrivateWordRead` combines actual chronology with
   private ages below the retained guard. No no-read predicate is an input.
8. `actual_boundary_and_suffix_noPrivateWordRead` retains the full guard
   boundary and its tail under strict private ages, including all ties/exits.
9. `actual_guarded_suffix_exists` gets the actual schedule split from a retained
   original vertex, rather than supplying an unrelated future word.
10. `calendarTail_split_after_boundary` proves literal operation-word splitting
    after the guard boundary using the existing `calendarTail` definition.

Two private list helpers derive pairwise suffix order and splitting at a list
member. They add no source definition, kernel or physical assumption. The
proofs apply to both global inheritance modes and to the compiler's more
general actual per-hybrid flag. Nothing replaces current-`AtNode` INDEPENDENT
sampling with an ancestral-copy law.

The strict guard premise is `∀ v ∈ P, C.age v < guard`. Thus every COMMON
operation at the guard or later has its named original vertex outside `P`.
All operations at a tied date are retained, with exits preceding nodes.
Starting the word after the guard boundary requires the actual causal upper
phase to have already completed that boundary. Starting before the full guard
boundary is safe under the same strict private-node age premise, but this
predicate alone does not provide a physical location/support claim. For a
lower entrance one still needs private nodes to be strictly later than the
included lower phase; a private bit already read there is not independent.

## Physical support is a separate implication

An erased register and an agenda without future private COMMON reads do not
prove that active private populations have disappeared. After all exits/nodes
at an actual upper guard `b`, actual physical support must separately exclude
private edges whose source age is at most `b` and private vertices whose age
is below `b`. Cut-crossing outside edges are retained. The source's active-edge
convention is the younger target age at most the current time, strictly below
the older source age; at a source-age tie the exit must have been processed.

`SourceCalendarCompatibility` has `EpochCompatible`/`LocationInEpoch` and
`epoch_edge_active`; these statements require actual state location admission.
They are not consequences of register erasure. The compiler itself explicitly
keeps physical temporal location preservation separate from its probability
transport identity. This packet therefore does not infer upper-phase support
merely from sorted node dates or from the new no-read predicate.

Root owns endpoint-history erasure separately. The actual marked/bin history
factorization, independent driving seeds and conditional clock products,
private-edge support at the upper phase, common decorated unranked
descendant-block carrier, and cross-graph contextual substitution remain
separate. There is no exact-Code/owner-orientation lift or arbitrary marked-path
TV claim. Full G6 source/observation/statistical closure remains open.

Next action: independent exact-source review and the owner's compiler routing
for this deterministic agenda draft; derive actual upper-phase support before
using it in a physical prefix/run/suffix consumer.
