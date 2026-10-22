# Exact-real G7 formula frontend

Status: SOURCE ONLY, UNCOMPILED/UNEXECUTED. No solver/backend/model, Cargo,
native binary, CI, compiler or new worker ran. The original G1–G7 goal stays
active. This component does not return an identifying policy or budget NO.

native/g7_exact_law_formula.rs is a pure Rust library. The separate
native/g7-formula/Cargo.toml binds it to the already recovered exact
parity_solver Polynomial/Rational implementation. It declares no CLI, parser,
dispatch task, process, filesystem or network writer. The original biological
compiler, source census, QE and CAD providers are reused as separate suppliers.

## Typed input and exact scope

Problem declares one ordered original forcing-row alphabet, one finite base
observation alphabet, a finite target-labelled polynomial source-model family,
algebraic constants and finitely many semialgebraic action/support cases.
Each source model has its OWN parameter arity/domain, and exactly one shared
row-major base vector of dimension D=rows*base_observations. Model target is
constant on that piece; split a parameter-dependent finite target into pieces.
All polynomials use constants first, then source-local OR action-local symbols.

Rows have exactly r original-ID Option<Bool> slots. Sites are DERIVED from
their Some entries, including forcing to false. Original row IDs are literal
positions; distinct IDs may have equal masks and retain distinct channels and
row-union costs. No mask quotient is performed. Duplicate support IDs are still
invalid. Ordered G6 constraint/multiplier positions also remain unchanged. Multiple
observation/channel modes are base coordinates or action modes, never new
physical configuration IDs. The complete menu/census/readout interpretation
is a supplier obligation, not authenticated by the typed container.

Every action supplies exact positive original-row support and a polynomial
weight for EVERY row. The generated guard requires positive weights on support,
zero elsewhere and total1. StochasticChannels adds nonnegative, mass1 channel
rows and DERIVES coefficient B[o,row,obs]=w[row]*C[row,obs,o], with offset0.
SuppliedAffine accepts a declared B/b specification and guards zero coefficients
on absent support rows. Its case IDs are exposed by supplied_affine_cases():
actual-programme correspondence is still mandatory for EACH such case.
No dictionary field or caller Boolean supplies that proof.

All actions are source independent and real valued. Fixed semialgebraic action
domains plus these exact support guards form the allowed family. Variable
output dimensions can be embedded in a common finite output carrier by zero
padding; that typed bridge remains part of supplier integration.

## Whole-history game and resource state

H excludes every pair of consistent source states with different targets.
Each source copy receives ONE parameter bank, used for its domain and EVERY
history equation. The competing source gets a distinct bank. No fresh source
parameters are allocated per row or response.

W0=H.
W(d+1)=H OR disjunction_over_cases(
  exists action_parameters,
    allowed_action AND forall exact_response, Wd(updated_history,state)).

Action variables lie outside the competing-source quantifiers and before their
future response. They may depend on the entire previous history. Invalid or
physically impossible histories are kept distinct: impossible histories satisfy
H; ReachableHistory separately asks for a whole-history consistent model.

Resources are executed calls plus unions of positive original rows/sites.
A PathBudget is a nonempty finite union of downward ResourceCeiling rectangles,
with optional allowed original row/site sets. This supports standard call/row/
site caps and arbitrary finite downsets in THESE coordinates, including
combined objectives encoded by their maximal states. It does not implement
arbitrary irreversible/value-dependent resource updates. Deletion preserves
this syntactic legality, so the general affine bound D applies. Retained depth
is min(D, affordable remaining calls), not the pooled prototype's row count k.
Different varying channels do not create extra charged original rows.

AST/input/bit/exponent/symbol/output and construction-depth limits are explicit.
The current recursive builder additionally refuses depth>128. These engineering
limits return Error::Limit, an UNKNOWN/unavailable result; they never return a
false winning formula or a losing-budget certificate. Invalid dimensions,
IDs, duplicate support IDs or malformed prefixes return Error::Invalid separately.
No source-census completeness follows from either validation path.

## Backend queries and policy interface

compile(problem,budget,prefix_case_ids,emit_action_fibres,limits) returns a
Compiled value immutably borrowing BOTH complete inputs. Prefix case IDs fix
only the finite case path. Prefix actions and responses remain FREE real
symbols, exposed by history_symbols(); no transcendental response is converted
to a rational sample or global algebraic constant.

QueryKind includes ConstantsWellDefined, LegalHistory, ReachableHistory,
HomogeneousHistory, WinningContinuation and optional WinningAction fibres.
A fibre exposes free next-action coordinates and universally quantifies its
next reply and remaining game. Disabled fibres explicitly retain affordability
and enabled_in_retained_horizon; their formula is false and no action is selected.
The output is a relation for the EXISTING history-relative algebraic selector.
It is not an executable next-action oracle.

Each algebraic constant is a rational univariate polynomial plus STRICT
rational isolating interval. ConstantsWellDefined is the existence AND
uniqueness formula for the ENTIRE shared tuple. It MUST be true before any
other query is interpreted. An invalid/no-root/nonunique description is a
prerequisite failure, never a budget NO. Other decision relations universally
bind this tuple under its root constraints; without the prerequisite their
implications can be vacuous. Reachability instead existentially binds roots
and one consistent source. Root isolation/QE itself is not executed here.

wolfram_query() emits bounded Resolve[...,Reals] source for the existing
provider. All symbols/heads are generated; no caller text becomes executable
code. The iterative renderer checks each append, because DAG sharing can
expand in text. The frozen source/projection/request/result must still be
authenticated at the actual provider boundary. A Rust borrow does not
authenticate an arbitrary external dictionary, binary or origin receipt.

## Reuse and remaining integration

G7-POLICY-REUSE.md and evidence/G7-POLICY-SOURCE-INTAKE.json pin the accepted
539c G7 contract, existing census/whole-forest source solver, pooled
continuous_optimizer.wl and actual CAD selector, plus the original typed
Winning/rank/resource/strategy consumers. This library ports their game
architecture and adds general channels/free histories without replacing QE.

The original native LAW compiler supplies a bounded joint-frontier polynomial
table. Its natural G is incoming[0] probability. Original forcing can be
represented by polynomial specialization G=1 for parent0 and G=0 for parent1,
with one unchanged source bank elsewhere. This use-site still needs its
controlled-law/registry proof and coherent M0 map: G=1-physical_gamma when
incoming order is false/true. Formal specialization is NOT declaring an
interior natural gamma equal to0/1. The current native engine has no separate
forced-request field and retains its original sample/size/state caps.
Those limits cannot stand in for the all-finite G7 source supplier.

Required next links are the actual complete census/admission/source/readout
provider, effective shared polynomial rows, AST-to-Winning correctness,
verified QE with free-variable preservation, relative-history algebraic
selection and terminal target/lower-source witnesses, executable-policy
CorrectRun and frontier enumeration. General mathematical hand acceptance
is retained; this engineering component does not reclassify it as a missing
theorem or promote the prototype's execution scope.

NEW native/Cargo/Lake/CI/backend execution remains held BEFORE the first writer.
Do not invoke even Cargo metadata/configuration through an ordinary shell:
the existing authenticated Linux writer/controller/recipient/frame/sequence
and transitive hooks are still UNBOUND. No new launcher, key, owner route,
runtime task/profile/whitelist, local Git or phone artifact is introduced.
The source manifest binds the exact current library and Cargo proposal;
source review is not parse/typecheck/link/run evidence.

The first bounded original joint-LAW inlet is now source-implemented in
law_table_inlet. See G7-LAW-TABLE-INLET-CONTRACT.md. One source/model retains
ALL original forcing rows and sampling/readout menus, with literal menu
coordinate offsets. Multiple concatenated menu blocks are not one PMF and
require explicit SuppliedAffine programme maps; the constructor rejects the
single-law stochastic shorthand there. The original compiler and frozen
inputs are unchanged. Both modules remain uncompiled/unexecuted.

## Open-history result interpretation

WinningContinuation is constants-conditional(prefix_legal AND win), not bare
Winning on arbitrary free coordinates. A FALSE continuation is a losing
continuation only AFTER ConstantsWellDefined AND LegalHistory are TRUE at
those EXACT history/action values. Otherwise the false value may only reject
an illegal prefix. ReachableHistory is additionally required to call the
history an actual physical transcript. This is a mandatory backend/result
consumer guard, not supplied by an arbitrary dictionary Boolean.

A false WinningAction fibre, a disabled unaffordable case or a zero retained
horizon is not budget loss. HomogeneousHistory may already allow stopping;
a relation false at one free action assignment does not prove its fibre empty.
Use the complete scoped winning query and authenticated provider result with
all prerequisites. No backend/result consumer or executed acceptance is
implemented by this pure query emitter.

## Guarded assertion interface and response carrier

wolfram_assertion now source-implements positive assertions with constants
and legal-history guards, optional mathematical reachability and an immutable
IssuedAssertion input association. See G7-ASSERTION-QUERY-CONTRACT.md. FALSE
remains inconclusive. This addition is uncompiled/unexecuted and has no inherited
Rust AST/kernel/backend acceptance.

For the future game/rank refinement, ActionCase.output_count can vary while
the abstract response carrier is fixed. One suitable proof embedding pads
each chosen case's coefficients, offsets and responses with zeros into
Fin(maximum output_count)->Real. Preserve native active-coordinate order.
Nonzero padding makes the extended history inconsistent with every source,
hence homogeneous; on zero padding the active native quantifier is retained.
This is a missing proof relation, not a native output-format change or extra
legal observation/charged forcing row. Empty carriers use Fin0.

## Native values to the retained mathematical game

Fix the unique constant tuple C. A source point is a model index m plus one
real parameter vector satisfying THAT model's declared domain at C. Its target
is the model's constant target label. Its base is the complete D-vector of
model polynomials evaluated at that SAME point. D=rows*base_observations.
Do not merge different-target points with identical responses.

An action is a finite case index plus that case's real parameter vector.
Its allowed predicate is exactly the generated allowed/weight/channel/affine
guard at C, independent of the unknown source vector. Support is the case's
declared strictly positive original-row support; the generated guard proves
positivity on support and zero weights off support. Original sites include
Some(false). No channel/menu alternative creates a fresh forcing row.

Choose O=Fin(maximum output_count) for the WHOLE Problem. Embed each case's
coefficients, offsets and responses by zero padding, preserving active order.
With V=Real^D, the coefficient row is a linear functional on V and the offset
depends only on the chosen action. Thus the response is linear(base)+offset.
This includes polynomial action dependence; it is affine in the SOURCE BASE,
not necessarily in source parameters or action parameters.

The experiment uses this source point, target, padded response and exact
finite-region executed-action resource contract. Its past list is the reversed
native chronological action prefix; resource update prepends only the action
actually called. The source fits EVERY history equation with ONE parameter
vector. Native consistency must be proved equal to the retained Consistent,
then native homogeneity to Homogeneous (within one model targets are constant).

For every case the native response quantifier ranges over active coordinates.
In the fixed abstract carrier, nonzero padding cannot equal any source response,
so the extended history has no consistent source and is homogeneous. On zero
padding, the active vector gives the native quantifier. This is the required
induction link; padding supplies no new legal observation. Fin0 stays empty.

The remaining AST proof must relate exact sparse polynomial/predicate evaluation
and arena scoping to this value semantics, then induct on the retained horizon.
The existing rank/budget theorems supply the abstract cap AFTER the actual
affine/resource/history hypotheses. They do not prove this Rust implementation.
Actual physical source/response/target transport and legal-programme coverage
remain the separate supplier relation already pinned in the physical contract.

## Audited free query scope

IssuedAssertion now runs an iterative scope audit before rendering. Constants
and source/future-action variables must be bound in the generated AST. The only
permitted free variables are the ORIGINAL prefix action/response symbols plus
the selected candidate action symbols. The audit refuses a binder that captures
one of those declared free symbols, reused active binders, invalid IDs or an
undeclared free variable. Boolean simplification may legitimately remove a
declared coordinate; actual_free_symbols() returns only actual syntactic free
occurrences, in generated-symbol order.

Traversal is iterative and uses bounded work/stack allocation from existing
AST/symbol/render ceilings. A scope/work failure refuses issuance; it never
returns a partial certificate or budget loss. The original low-level query
method remains unchanged. This audit is source-implemented and uncompiled/
unexecuted. It is not proof of quantifier semantics, polynomial evaluation,
external result identity, actual source admission or an authenticated writer.

The integrated hosted G7ExactLawSourceTransfer and G7PaddedResponseCarrier
sources now supply the conditional same-point/game and padding lemmas above.
Their eight plus six selected complete types and exact source/submitted-audit
projections are reviewed in evidence/G7-TRANSFER-PADDING-HOSTED-REVIEW.json.
This is attributed peer checking, not a Rust AST proof or provider factory.

Representation uses the SAME action, response and resource carriers. Its
legal_iff/update_eq fields are genuine obligations. A native case menu must
cover every legal action in the requested original problem before a losing
result excludes its full strategy class; a restricted menu cannot establish
loss for a larger action universe. A transferred current-history ambiguity
pair is not one fixed obstruction against every possible future policy.


## Explicit stochastic menu channels (source candidate)

StochasticMenuChannels declares the exact ordered outcome count of each
separate menu, a normalized nonnegative menu choice for EACH original row,
and stochastic output channels for each row/menu/outcome. The existing arena
derives w(row)*q(row,menu)*channel(row,menu,outcome,output). All probability
guards and polynomial scopes are explicit; no polynomial expansion or numeric
evaluation is introduced. Original positive row support, Some(false) sites,
source-independent action quantifiers and resource transitions are unchanged.

The ordered menu counts must sum exactly to base_observations. The LAW inlet
also binds them to its captured menu order. Old StochasticChannels remains
the single-PMF representation and is still refused for concatenated menus.
General SuppliedAffine retains its actual programme correspondence obligation.
Every menu must have its actual normalized law on the SAME source; this new
measurement representation does not prove native provider or source coverage.

Earlier guard/scope reviews concern their exact pinned source. This revision
adds one enum variant and new validation/action arms; it is uncompiled and
unexecuted. See G7-TARGET-LABELLED-FAMILY-JOIN.md and the exact current source
review for the target-labelled normalization and semantic acceptance boundary.

The guarded assertion kind IdentifiedTarget(t) now expresses the retained
Valid(.stop t) obligation for the supplied source family. It reuses the existing
whole-history model predicates, closes their shared constant tuple, and excludes
every differently labelled piece. It returns only an IssuedAssertion bound to
the exact problem/history/label. No unique parameter point or arbitrary target
function of normalized survival is assumed. Empty consistency is vacuous;
physical transcript interpretation additionally requires reachability and origin.
See G7-ASSERTION-QUERY-CONTRACT.md and the exact source-only terminal review.
