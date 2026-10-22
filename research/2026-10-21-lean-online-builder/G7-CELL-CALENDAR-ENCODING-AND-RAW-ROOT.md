# Owning calendar source and the existing raw-completion receiver

This is source-level review only. The complete new Rust body, its two contracts,
the complete original calendar producer and the complete retained raw-calendar
root proof were read and SHA256/Git-blob authenticated. No Rust, Lean, native
provider, compiler, backend or control was run for this review. Historical
source headers and the distinction between hosted and pinned contexts remain.

The new source at Rust PR2 commit7d33d9211238dd9ea5d97445719931913055c154 is
native/g7_cell_calendar.rs,7943B/SHA256
a5cd0afb5c309a66fbf0309df354992f47480b7276775c4ea18f2857ec163eb3,
Git blobdee4a23429be062eeb6290dac2c9d255faa89e1a. The inspected ownership and
one-bank composition agree with the existing conditional mathematical receiver:

- The request owns the unchanged captured cell and supplied complete vector.
  Original affine::check_witness checks every original ordered row. Failure
  rejects this construction and yields no partial calendar or mathematical NO.
- The coordinate helpers extract every original age, each edge inverse rate,
  one ancestral inverse rate and each original hybrid coin exactly once.
  The used-coordinate check covers the entire vector. This is the physical
  age/inverse/coin bank, distinct from the later slot/gamma polynomial bank.
- The generated calendar and child stay with that request/vector. The controlled
  method accepts a mask and limits, and passes the stored child to the existing
  controlled-word composition. It accepts no replacement word, rates or source.
- Under the still-required original M0 port map, the coin is parent1 gamma.
  This path performs no old-LAW parent0 complement. A site-specific mode vector
  still needs the original source-class premise when the requested class has
  one global COMMON/INDEPENDENT mode.

The complete unchanged source_calendar.rs at4e556c4a is12140B/SHA256
d993e8808a4f227001a393db123b1be00f70a5c940388586d909772bbb3ff3a8,
Git blob8bd8bc7c1ec86c1c1fcf76989039e151beebf00f. It checks strict edge ages,
positive inverse rates and strict natural gamma. Distinct dates are sorted;
each later interval precedes that date's exits, followed by its node entries.
The first date processes its boundary before any positive interval. Its
physical coordinates are exactly ExpNeg(duration/u), with the same edge and
ancestral inverse rates at every slot, followed by the unchanged parent1 bank.
AncestralComplete refuses empty Copy. ExpNeg is symbolic metadata here; the
new composition evaluates or independently fits no exponential.

No material ownership, coordinate, rate-convention or forcing mismatch was
found in those inspected sources. This is not a Rust compatibility check,
native checker/validator refinement, an actual M0 proof or parser authentication.
The separate complete contract and representation-join hashes are recorded in
G7-CELL-CALENDAR-SOURCE-REVIEW.json.

## Existing all-raw root supplier

The exact retained source G7RawCalendarRoot is15828B/SHA256
b31a2534a28800aee647f3301345974aa7d5cf278d4a900e587ade600e7b232c,
Git bloba20dae10be0f96616e2f7028baa95277ff2ca0f3. Its complete unchanged body
is already selected in the775-module source context. Its header explicitly
retains pending kernel/owned-audit status; this review adds no compilation.
The namespace is GProgram.G7.RawCalendarRoot.

The actual initialized_calendar_trace_root theorem proves AncestralRoot for
EVERY structural programTrace from initialCode through compiledCalendarProgram,
for arbitrary original entering register and closed-unit transition gamma.
It does not require the row's coefficient to be nonzero. Its exit_trace_list,
node_trace_list, boundary_trace_batch and calendar_tail_trace use the literal
original locations, scheduled dates and complete boundary operations.

The existing natural_calendar_raw_root then states, for the same original N,
calendars C,D with SameOrder C.age D.age, sample, original parent registry H,
strict natural p and any mode vector common:

    row in naturalWordRows N sample H common
      (indexedSymbols (calendarSchema N C))
      -> AncestralRoot N row.1.

This is the literal raw list, including polynomial-zero rows. The companion
polynomial_generated_completedRows, with Nonempty Copy and positive original
rates, supplies the complete rational-polynomial identity

    polynomial (readRows project
      (completedNaturalWordRows ... indexedSymbols) b)
      = completedPolynomial N (naturalWordPolynomial ... indexedSymbols) b.

Thus the mathematical raw-root supplier exists for the actual complete
initialized calendar. The still-missing native use-site relation must identify
the generated source, initial Code, agenda, phase order and slot/state encoding
with that original program. A generic unsupported claim about raw completion
must not replace this existing supplier, nor be counted as a new theorem.

One order qualification is material. The original native producer's own header
limits its accepted phase-permutation justification to the endpoint PMF.
Equality of endpoint PMFs alone does not identify a literal raw list containing
zero rows. At this join, supply exact program/word correspondence, or transport
the structural trace/root property for the actual native phase blocks. The
existing generic exit_trace_list and node_trace_list are available for that
purpose. Do not silently infer all-raw support from positive PMF support or from
an endpoint-only permutation result. No failure of the native agenda is claimed.

For forcing, keep the natural initial weights outside transition substitution.
Use the structural root property before applying endpoint polynomial
substitution, retaining the actual original registry and controlled mode vector.
Constant rational completion still needs its encoding and substitution relation;
the raw-root theorem does not prove that native representation step by itself.

## First remaining use-site

The native canonical Snapshot must map to the existing admitted runtime state
Code on the SAME graph/sample. Its dead None fields form a canonical image;
they are not a bijection onto every admitted Code with arbitrary dead garbage.
The original graph Code/BinaryValid proof is a separate earlier constructor.

For every selected destination, including absent sparse-map destinations,
the complete coefficient fibre must match the existing effective step/word
row under the precise WordVariable map. Slot-major edge occurrences precede
one ancestral none in each slot; original hybrids follow all slots. A particular
evaluated zero does not establish a zero polynomial. Both the exact closed-unit
transition domain and strict outer natural inheritance remain required.

The existing final source receiver remains
GProgram.G7.ActualExactLawResponses.actual_controlled_unranked_readout_polynomial
in sourcec57cca332a369dee05f61164cba15af0bdb8ec40ae09783b0a1e898772b408bb.
It consumes the actual complete calendar/schema, SameOrder relation, rates,
natural inheritance, registry, mask, Nonempty Copy and authorized observer.
One physical SourcePoint must serve every row/menu/history. An arbitrary
observational projection or endpoint register erasure is not automatically an
authorized continuation or readout.

Captured parser/Code origin, exact field/layout relations, source-class and
legal-action coverage in both directions, AST/game/QE/selection/CorrectRun and
authenticated runtime results remain open. The original-owner encrypted native
controller and transitive first writers remain UNBOUND. The hosted case count
stays28 and source selection stays775; this review adds neither a proof case
nor a native module, API, execution permit or new test suite.
